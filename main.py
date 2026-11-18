import os
import sys
import json
import threading
import time
import traceback
import xml.etree.ElementTree as ET
from datetime import datetime, timezone

from PySide6.QtWidgets import (
    QApplication,
    QVBoxLayout,
    QSizePolicy,
    QPushButton,
    QComboBox,
    QHBoxLayout,
    QFileDialog,
    QMessageBox,
    QLineEdit,
    QCheckBox
)
from PySide6.QtUiTools import QUiLoader
from PySide6.QtCore import QFile, QObject, Signal, QTimer
from PySide6.QtWebEngineWidgets import QWebEngineView

from pubsub import pub
from meshtastic.tcp_interface import TCPInterface


MESHTASTIC_HOST = "192.168.0.31"

# Default folder offered by the Save / Load GPX dialogs.
GPX_FOLDER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "gpx_tracks")

GPX_NS = "http://www.topografix.com/GPX/1/1"

# Namespace for the Meshtastic Tracker extension elements (<mt:fix>,
# <mt:rssi>) stored inside each <trkpt> of a saved GPX file.
MT_NS = "http://meshtastic-tracker.local/gpx/1"

# Only nodes heard from within this window are offered in the drop-down.
NODE_SEEN_WINDOW_SECONDS = 60 * 60  # 1 hour

# How often stale nodes are pruned from the drop-down.
NODE_PRUNE_INTERVAL_MS = 30 * 1000

ALLOWED_NODE_NAMES = {
    "mike",
    "michael"
}


class MainWindow(QObject):

    gps_update = Signal(str, float, float, str, object)
    telemetry_update = Signal(str, str)
    hops_update = Signal(str, int)
    gps_time_update = Signal(str, str)
    status_update = Signal(str)
    message_result = Signal(str)
    received_message = Signal(str, str)
    node_discovered = Signal(str, str)

    def __init__(self):
        super().__init__()

        self.mesh_interface = None
        self.map_ready = False
        self.pending_positions = {}
        self.pending_telemetry = {}
        self.pending_hops = {}
        self.pending_gps_times = {}
        self.recording = False  # track recording starts off
        self.snapping = True  # snap tracks to roads/trails (default on)
        self.known_nodes = {}
        self.latest_positions = {}
        self.displayed_nodes = set()
        self.last_seen = {}  # node_id -> epoch seconds of last packet

        # Load Qt Designer UI
        loader = QUiLoader()
        ui_file = QFile("map.ui")

        if not ui_file.open(QFile.OpenModeFlag.ReadOnly):
            raise RuntimeError("Could not open map.ui")

        self.ui = loader.load(ui_file)
        ui_file.close()

        if self.ui is None:
            raise RuntimeError("Could not load map.ui")

        self.ui.setWindowTitle("Meshtastic Tracker")

        # Connect signals to GUI thread
        self.gps_update.connect(self.update_map_position)
        self.telemetry_update.connect(self.update_map_telemetry)
        self.hops_update.connect(self.update_map_hops)
        self.gps_time_update.connect(self.update_map_gps_time)
        self.status_update.connect(self.show_status)
        self.message_result.connect(self.show_status)
        self.received_message.connect(self.show_received_message)
        self.node_discovered.connect(self.add_node_to_selector)

        # Make mapWidget fill the main window
        self.ui.setCentralWidget(self.ui.mapWidget)
        self.ui.mapWidget.setMinimumSize(0, 0)
        self.ui.mapWidget.setSizePolicy(
            QSizePolicy.Policy.Expanding,
            QSizePolicy.Policy.Expanding
        )

        self.setup_map()

        # Periodically drop nodes not heard from in the last hour.
        self.prune_timer = QTimer(self)
        self.prune_timer.timeout.connect(self.prune_selector)
        self.prune_timer.start(NODE_PRUNE_INTERVAL_MS)

        self.ui.showMaximized()

        # Connect to Meshtastic
        self.connect_to_meshtastic()

    # =========================================================
    # MAP SETUP
    # =========================================================

    def setup_map(self):

        self.map_view = QWebEngineView()
        self.map_view.setSizePolicy(
            QSizePolicy.Policy.Expanding,
            QSizePolicy.Policy.Expanding
        )
        self.map_view.setMinimumSize(0, 0)

        self.ui.mapWidget.setSizePolicy(
            QSizePolicy.Policy.Expanding,
            QSizePolicy.Policy.Expanding
        )
        self.ui.mapWidget.setMinimumSize(0, 0)

        layout = self.ui.mapWidget.layout()
        if layout is None:
            layout = QVBoxLayout(self.ui.mapWidget)

        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Map expands to fill the available space.
        layout.addWidget(self.map_view, 1)

        # Keep the CLEAR button and node selector together at the bottom.
        controls = QHBoxLayout()
        controls.setContentsMargins(0, 0, 0, 0)
        controls.setSpacing(8)

        self.clear_button = QPushButton("CLEAR")
        self.clear_button.setMinimumHeight(42)
        self.clear_button.setMaximumHeight(48)
        self.clear_button.setStyleSheet(
            "QPushButton {"
            " background-color: #d9534f;"
            " color: white;"
            " font-weight: bold;"
            " font-size: 14px;"
            " border: none;"
            " padding: 8px;"
            "}"
            "QPushButton:hover { background-color: #c9302c; }"
            "QPushButton:pressed { background-color: #ac2925; }"
        )
        self.clear_button.clicked.connect(self.clear_tracks)
        controls.addWidget(self.clear_button)

        self.save_button = QPushButton("SAVE GPX")
        self.style_action_button(
            self.save_button, "#2e7d32", "#256628", "#1b4d1e"
        )
        self.save_button.clicked.connect(self.save_gpx)
        controls.addWidget(self.save_button)

        self.load_button = QPushButton("LOAD GPX")
        self.style_action_button(
            self.load_button, "#1565c0", "#11519a", "#0d3c73"
        )
        self.load_button.clicked.connect(self.load_gpx)
        controls.addWidget(self.load_button)

        self.start_record_button = QPushButton("START RECORDING")
        self.style_action_button(
            self.start_record_button, "#00897b", "#00695c", "#004d40"
        )
        self.start_record_button.clicked.connect(
            lambda: self.set_recording(True)
        )
        controls.addWidget(self.start_record_button)

        self.stop_record_button = QPushButton("STOP RECORDING")
        self.style_action_button(
            self.stop_record_button, "#ef6c00", "#d35f00", "#b25000"
        )
        self.stop_record_button.clicked.connect(
            lambda: self.set_recording(False)
        )
        controls.addWidget(self.stop_record_button)

        # Recording is off until START RECORDING is pressed.
        self.update_record_buttons()

        self.snap_checkbox = QCheckBox("Snap to trails")
        self.snap_checkbox.setMinimumHeight(42)
        self.snap_checkbox.setChecked(self.snapping)
        self.snap_checkbox.setToolTip(
            "When checked, new track segments are snapped to nearby "
            "roads/trails. When unchecked, raw GPS points are joined "
            "with straight lines."
        )
        self.snap_checkbox.toggled.connect(self.set_snapping)
        controls.addWidget(self.snap_checkbox)

        self.node_selector = QComboBox()
        self.node_selector.setMinimumHeight(42)
        self.node_selector.setSizePolicy(
            QSizePolicy.Policy.Expanding,
            QSizePolicy.Policy.Fixed
        )
        self.node_selector.addItem("Add node to map...", None)
        self.node_selector.activated.connect(self.add_selected_node)
        controls.addWidget(self.node_selector, 1)

        self.message_input = QLineEdit()
        self.message_input.setMinimumHeight(42)
        self.message_input.setPlaceholderText("Message selected node...")
        self.message_input.returnPressed.connect(self.send_message)
        controls.addWidget(self.message_input, 1)

        self.send_message_button = QPushButton("SEND MESSAGE")
        self.style_action_button(
            self.send_message_button, "#6a1b9a", "#531579", "#3f105d"
        )
        self.send_message_button.clicked.connect(self.send_message)
        controls.addWidget(self.send_message_button)

        layout.addLayout(controls, 0)

        self.map_view.loadFinished.connect(self.map_loaded)

        html = """
        <!DOCTYPE html>
        <html>
        <head>
            <meta charset="utf-8">
            <link rel="stylesheet"
                  href="https://unpkg.com/leaflet/dist/leaflet.css"/>
            <script src="https://unpkg.com/leaflet/dist/leaflet.js"></script>
            <style>
                html, body {
                    width: 100%;
                    height: 100%;
                    margin: 0;
                    padding: 0;
                    overflow: hidden;
                }
                #map {
                    position: absolute;
                    top: 0;
                    left: 0;
                    right: 0;
                    bottom: 0;
                }
                .telemetry-popup {
                    min-width: 230px;
                    max-width: 320px;
                    max-height: 350px;
                    overflow-y: auto;
                    font-family: Arial, sans-serif;
                    font-size: 12px;
                    line-height: 1.45;
                }
                .telemetry-popup h3 {
                    margin: 0 0 7px 0;
                    font-size: 14px;
                }
                .telemetry-popup h4 {
                    margin: 9px 0 3px 0;
                    font-size: 12px;
                }
                .telemetry-row {
                    display: flex;
                    justify-content: space-between;
                    gap: 12px;
                    border-bottom: 1px solid #eee;
                    padding: 2px 0;
                }
                .telemetry-key {
                    color: #555;
                }
                .telemetry-value {
                    font-weight: 600;
                    text-align: right;
                    overflow-wrap: anywhere;
                }
                /* Flag shown beside each recorded location (RSSI). The
                   pole's base sits on the recorded point. */
                .rssi-flag {
                    position: relative;
                    width: 80px;
                    height: 26px;
                }
                .rssi-pole {
                    position: absolute;
                    left: 0;
                    bottom: 0;
                    width: 2px;
                    height: 26px;
                    background: #333;
                }
                .rssi-label {
                    position: absolute;
                    left: 2px;
                    top: 0;
                    padding: 1px 6px 1px 4px;
                    font: bold 11px/14px Arial, sans-serif;
                    color: #fff;
                    white-space: nowrap;
                    background: var(--flag-color, #555);
                    border-radius: 0 4px 4px 0;
                    box-shadow: 0 1px 3px rgba(0, 0, 0, 0.45);
                }
                .route-arrow {
                    background: none;
                    border: none;
                }
            </style>
        </head>
        <body>
            <div id="map"></div>

            <script>
                var map = L.map('map').setView(
                    [34.995815, -82.763522],
                    13
                );

                // ---------------------------------------------------
                // Base maps (choose one) and optional overlays.
                // maxNativeZoom lets you keep zooming in past the
                // provider's last real tile level (tiles are scaled up).
                // ---------------------------------------------------
                var esriAttr = 'Tiles © Esri — Source: Esri, Maxar, Earthstar Geographics, USGS, and the GIS User Community';

                var baseOSM = L.tileLayer(
                    'https://tile.openstreetmap.org/{z}/{x}/{y}.png',
                    {
                        attribution: '© OpenStreetMap contributors',
                        maxZoom: 19
                    }
                );

                var baseSatellite = L.tileLayer(
                    'https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}',
                    {
                        attribution: esriAttr,
                        maxNativeZoom: 19,
                        maxZoom: 19
                    }
                );

                var baseTopo = L.tileLayer(
                    'https://{s}.tile.opentopomap.org/{z}/{x}/{y}.png',
                    {
                        attribution: '© OpenStreetMap contributors, SRTM | © OpenTopoMap (CC-BY-SA)',
                        subdomains: 'abc',
                        maxNativeZoom: 17,
                        maxZoom: 19
                    }
                );

                var baseUSGS = L.tileLayer(
                    'https://basemap.nationalmap.gov/arcgis/rest/services/USGSTopo/MapServer/tile/{z}/{y}/{x}',
                    {
                        attribution: 'Tiles courtesy of the U.S. Geological Survey',
                        maxNativeZoom: 16,
                        maxZoom: 19
                    }
                );

                var baseCycl = L.tileLayer(
                    'https://{s}.tile-cyclosm.openstreetmap.fr/cyclosm/{z}/{x}/{y}.png',
                    {
                        attribution: '© OpenStreetMap contributors | CyclOSM',
                        subdomains: 'abc',
                        maxNativeZoom: 20,
                        maxZoom: 19
                    }
                );

                var baseEsriTopo = L.tileLayer(
                    'https://server.arcgisonline.com/ArcGIS/rest/services/World_Topo_Map/MapServer/tile/{z}/{y}/{x}',
                    {
                        attribution: esriAttr,
                        maxNativeZoom: 19,
                        maxZoom: 19
                    }
                );

                // Overlays
                var overlayHiking = L.tileLayer(
                    'https://tile.waymarkedtrails.org/hiking/{z}/{x}/{y}.png',
                    {
                        attribution: '© waymarkedtrails.org, OpenStreetMap contributors',
                        maxNativeZoom: 18,
                        maxZoom: 19,
                        opacity: 0.85
                    }
                );

                // Roads + place names, handy on top of satellite imagery.
                var overlayRoads = L.layerGroup([
                    L.tileLayer(
                        'https://server.arcgisonline.com/ArcGIS/rest/services/Reference/World_Transportation/MapServer/tile/{z}/{y}/{x}',
                        { maxNativeZoom: 19, maxZoom: 19 }
                    ),
                    L.tileLayer(
                        'https://server.arcgisonline.com/ArcGIS/rest/services/Reference/World_Boundaries_and_Places/MapServer/tile/{z}/{y}/{x}',
                        { maxNativeZoom: 19, maxZoom: 19 }
                    )
                ]);

                baseOSM.addTo(map);

                L.control.layers(
                    {
                        'Street (OpenStreetMap)': baseOSM,
                        'Satellite (Esri)': baseSatellite,
                        'Topo / Trails (OpenTopoMap)': baseTopo,
                        'USGS Topo (US)': baseUSGS,
                        'Cycle / Trails (CyclOSM)': baseCycl,
                        'Esri World Topo': baseEsriTopo
                    },
                    {
                        'Hiking trails overlay': overlayHiking,
                        'Roads & place names': overlayRoads
                    },
                    { position: 'topright', collapsed: true }
                ).addTo(map);

                var markers = {};
                var tracks = {};
                var telemetryData = {};
                var hopsData = {};
                var gpsTimeData = {};
                var recording = false;

                // Pause/resume adding positions to the movement tracks.
                function setRecording(flag) {
                    recording = !!flag;
                }

                // Enable/disable snapping new track segments to roads and
                // trails. When off, raw GPS fixes are joined by straight
                // lines and no routing requests are made.
                var snapping = true;

                function setSnapping(flag) {
                    snapping = !!flag;
                }

                // Snap track segments to walkable OpenStreetMap roads/trails
                // only when both GPS endpoints are within 30 feet (9.144 m).
                // Valhalla's pedestrian costing supports footways and trails.
                var SNAP_RADIUS_METERS = 1.524; // 1.524 = 5'
                var VALHALLA_ROUTE_URL =
                    'https://valhalla1.openstreetmap.de/route';

                var trackColors = [
                    '#e6194b', '#3cb44b', '#4363d8',
                    '#f58231', '#911eb4', '#42d4f4'
                ];

                var nextColor = 0;

                function getNodeColor(node_id) {
                    if (!tracks[node_id]) {
                        tracks[node_id] = {
                            nodeId: node_id,
                            points: [],          // Original GPS points
                            times: [],           // Arrival time (ms) of each GPS point
                            displayPoints: [],   // Road/trail-snapped geometry
                            displayTimes: [],    // Time (ms) of each displayed point
                            // Parallel to displayPoints: null for routed
                            // in-between points, {rssi} for GPS fixes.
                            displayFixes: [],
                            color: trackColors[
                                nextColor++ % trackColors.length
                            ],
                            line: null,
                            arrowLayer: L.layerGroup().addTo(map),
                            flagLayer: L.layerGroup().addTo(map),
                            routeChain: Promise.resolve(),
                            generation: 0
                        };
                    }
                    return tracks[node_id].color;
                }

                // ---------------------------------------------------------
                // DIRECTION ARROWS
                // ---------------------------------------------------------

                // Approximate on-screen distance between arrows.
                var ARROW_SPACING_PX = 80;

                function makeArrowIcon(color, angleDeg) {
                    return L.divIcon({
                        className: 'route-arrow',
                        iconSize: [18, 18],
                        iconAnchor: [9, 9],
                        html:
                            "<div style='width:18px;height:18px;" +
                            "transform:rotate(" + angleDeg.toFixed(1) +
                            "deg);'>" +
                            "<svg width='18' height='18' viewBox='0 0 18 18'>" +
                            "<path d='M3 2 L16 9 L3 16 L6.5 9 Z' fill='" +
                            color + "' stroke='#ffffff' stroke-width='1.2' " +
                            "stroke-linejoin='round'/></svg></div>"
                    });
                }

                // Place direction arrows along a path (array of [lat, lon]
                // in the direction of travel) at a roughly constant on-screen
                // spacing, and add them to the given layer group.
                function buildArrowMarkers(latlngs, color, group) {
                    if (!latlngs || latlngs.length < 2) return;

                    // Work in screen pixels, dropping vertices closer than
                    // 3 px so very short snapped segments don't make the
                    // arrow angle jitter.
                    var pts = [map.latLngToLayerPoint(latlngs[0])];
                    for (var i = 1; i < latlngs.length; i++) {
                        var p = map.latLngToLayerPoint(latlngs[i]);
                        var q = pts[pts.length - 1];
                        var isLast = (i === latlngs.length - 1);
                        if (Math.hypot(p.x - q.x, p.y - q.y) >= 3) {
                            pts.push(p);
                        } else if (isLast && pts.length > 1) {
                            pts[pts.length - 1] = p;
                        }
                    }
                    if (pts.length < 2) return;

                    var remaining = ARROW_SPACING_PX / 2;
                    for (var s = 1; s < pts.length; s++) {
                        var a = pts[s - 1];
                        var b = pts[s];
                        var dx = b.x - a.x;
                        var dy = b.y - a.y;
                        var len = Math.hypot(dx, dy);
                        if (len === 0) continue;

                        // Screen y grows downward, so atan2 gives a clockwise
                        // angle, which matches CSS rotate().
                        var angle = Math.atan2(dy, dx) * 180 / Math.PI;
                        var pos = remaining;

                        while (pos <= len) {
                            var t = pos / len;
                            var at = map.layerPointToLatLng(
                                L.point(a.x + dx * t, a.y + dy * t)
                            );
                            L.marker(at, {
                                icon: makeArrowIcon(color, angle),
                                interactive: false,
                                keyboard: false,
                                zIndexOffset: -500
                            }).addTo(group);
                            pos += ARROW_SPACING_PX;
                        }
                        remaining = pos - len;
                    }
                }

                function drawTrackArrows(track) {
                    track.arrowLayer.clearLayers();
                    buildArrowMarkers(
                        track.displayPoints, track.color, track.arrowLayer
                    );
                }

                // Saved (loaded) tracks, kept so their arrows can be redrawn
                // when the zoom level changes.
                var loadedArrowLayer = L.layerGroup().addTo(map);
                var loadedArrowSources = [];

                function drawLoadedArrows() {
                    loadedArrowLayer.clearLayers();
                    loadedArrowSources.forEach(function(item) {
                        item.segments.forEach(function(seg) {
                            buildArrowMarkers(seg, item.color, loadedArrowLayer);
                        });
                    });
                }

                // Arrow spacing is screen-based, so rebuild after zooming.
                map.on('zoomend', function() {
                    Object.keys(tracks).forEach(function(node_id) {
                        drawTrackArrows(tracks[node_id]);
                    });
                    drawLoadedArrows();
                });

                // ---------------------------------------------------------
                // RSSI FLAGS
                // ---------------------------------------------------------

                function rssiColor(rssi) {
                    if (rssi === null || rssi === undefined) return '#757575';
                    if (rssi >= -90) return '#2e7d32';    // strong
                    if (rssi >= -105) return '#ef6c00';   // fair
                    return '#c62828';                     // weak
                }

                // Add a dot plus a flag showing the received RSSI at a
                // recorded location.
                function addRssiFlag(layer, color, latlng, rssi, timeMs) {
                    var hasRssi = (rssi !== null && rssi !== undefined &&
                                   !isNaN(rssi));
                    var text = hasRssi
                        ? Math.round(rssi) + " dBm"
                        : "RSSI n/a";

                    L.circleMarker(latlng, {
                        radius: 3,
                        color: '#ffffff',
                        weight: 1,
                        fillColor: color,
                        fillOpacity: 1,
                        interactive: false
                    }).addTo(layer);

                    var flag = L.marker(latlng, {
                        icon: L.divIcon({
                            className: '',
                            iconSize: [80, 26],
                            iconAnchor: [1, 26],
                            html:
                                "<div class='rssi-flag' style='--flag-color:" +
                                rssiColor(hasRssi ? rssi : null) + ";'>" +
                                "<div class='rssi-pole'></div>" +
                                "<div class='rssi-label'>" +
                                escapeHtml(text) + "</div></div>"
                        }),
                        keyboard: false,
                        zIndexOffset: -250
                    });
                    flag.bindTooltip(
                        "RSSI: " + escapeHtml(text) +
                        (timeMs !== null && timeMs !== undefined
                            ? "<br>" + escapeHtml(
                                  new Date(timeMs).toLocaleString())
                            : ""),
                        { direction: 'right' }
                    );
                    flag.addTo(layer);
                }

                function escapeHtml(value) {
                    return String(value).replace(/[&<>"']/g, function(c) {
                        return {
                            '&': '&amp;',
                            '<': '&lt;',
                            '>': '&gt;',
                            '"': '&quot;',
                            "'": '&#39;'
                        }[c];
                    });
                }

                function formatValue(value) {
                    if (value === null || value === undefined) {
                        return "—";
                    }
                    if (typeof value === "boolean") {
                        return value ? "Yes" : "No";
                    }
                    if (typeof value === "object") {
                        return JSON.stringify(value);
                    }
                    return String(value);
                }

                function addTelemetrySection(rows, title, values) {
                    if (!values || typeof values !== "object" ||
                        Array.isArray(values)) {
                        return;
                    }

                    var entries = Object.entries(values);
                    if (entries.length === 0) return;

                    rows.push("<h4>" + escapeHtml(title) + "</h4>");

                    entries.forEach(function(entry) {
                        rows.push(
                            "<div class='telemetry-row'>" +
                            "<span class='telemetry-key'>" +
                            escapeHtml(entry[0]) +
                            "</span><span class='telemetry-value'>" +
                            escapeHtml(formatValue(entry[1])) +
                            "</span></div>"
                        );
                    });
                }

                function getTrackDistanceMeters(node_id) {
                    var track = tracks[node_id];
                    if (!track || !track.displayPoints ||
                        track.displayPoints.length < 2) {
                        return 0;
                    }

                    var total = 0;
                    for (var i = 1; i < track.displayPoints.length; i++) {
                        var previous = L.latLng(
                            track.displayPoints[i - 1][0],
                            track.displayPoints[i - 1][1]
                        );
                        var current = L.latLng(
                            track.displayPoints[i][0],
                            track.displayPoints[i][1]
                        );
                        total += previous.distanceTo(current);
                    }
                    return total;
                }

                function formatTrackDistance(meters) {
                    var feet = meters * 3.280839895;
                    var miles = meters / 1609.344;
                    if (miles >= 0.1) {
                        return miles.toFixed(2) + " mi (" +
                            Math.round(feet).toLocaleString() + " ft)";
                    }
                    return Math.round(feet).toLocaleString() + " ft (" +
                        (meters / 1000).toFixed(2) + " km)";
                }

                function refreshNodePopup(node_id) {
                    if (markers[node_id]) {
                        markers[node_id].setPopupContent(
                            makeTelemetryHtml(node_id)
                        );
                    }
                }

                function makeTelemetryHtml(node_id) {
                    var data = telemetryData[node_id];
                    var rows = [];
                    rows.push("<div class='telemetry-popup'>");
                    rows.push("<h3>Node Telemetry</h3>");
                    rows.push(
                        "<div class='telemetry-row'>" +
                        "<span class='telemetry-key'>Total Distance Traveled</span>" +
                        "<span class='telemetry-value'>" +
                        escapeHtml(formatTrackDistance(
                            getTrackDistanceMeters(node_id)
                        )) +
                        "</span></div>"
                    );

                    rows.push(
                        "<div class='telemetry-row'>" +
                        "<span class='telemetry-key'>Hops Away</span>" +
                        "<span class='telemetry-value'>" +
                        escapeHtml(formatHops(hopsData[node_id])) +
                        "</span></div>"
                    );

                    if (!data) {
                        rows.push(makeGpsTimeRow(node_id));
                        rows.push("No telemetry received from this node yet.");
                        rows.push("</div>");
                        return rows.join("");
                    }

                    rows.push(
                        "<div class='telemetry-row'>" +
                        "<span class='telemetry-key'>Last Data Received</span>" +
                        "<span class='telemetry-value'>" +
                        escapeHtml(formatValue(data.lastReceived)) +
                        "</span></div>"
                    );
                    rows.push(makeGpsTimeRow(node_id));

                    // Meshtastic telemetry fields are normally camelCase.
                    // Also accept snake_case keys for compatibility.
                    addTelemetrySection(
                        rows, "Device Metrics",
                        data.deviceMetrics || data.device_metrics
                    );
                    addTelemetrySection(
                        rows, "Environment Metrics",
                        data.environmentMetrics || data.environment_metrics
                    );
                    addTelemetrySection(
                        rows, "Local Stats",
                        data.localStats || data.local_stats
                    );

                    var known = [
                        "deviceMetrics", "device_metrics",
                        "environmentMetrics", "environment_metrics",
                        "localStats", "local_stats", "lastReceived"
                    ];

                    Object.entries(data).forEach(function(entry) {
                        if (known.indexOf(entry[0]) === -1) {
                            addTelemetrySection(rows, entry[0], entry[1]);
                        }
                    });

                    rows.push("</div>");
                    return rows.join("");
                }

                function makeGpsTimeRow(node_id) {
                    return (
                        "<div class='telemetry-row'>" +
                        "<span class='telemetry-key'>Last GPS Location Received</span>" +
                        "<span class='telemetry-value'>" +
                        escapeHtml(gpsTimeData[node_id] || "Unknown") +
                        "</span></div>"
                    );
                }

                function updateGpsTime(node_id, gps_time) {
                    gpsTimeData[node_id] = gps_time;

                    // Refresh popup content if the marker already exists.
                    if (markers[node_id]) {
                        markers[node_id].setPopupContent(
                            makeTelemetryHtml(node_id)
                        );
                    }
                }

                function formatHops(hops) {
                    if (hops === undefined || hops === null) {
                        return "Unknown";
                    }
                    return hops === 0 ? "0 (direct)" : String(hops);
                }

                function updateHops(node_id, hops) {
                    hopsData[node_id] = hops;

                    // Refresh popup content if the marker already exists.
                    if (markers[node_id]) {
                        markers[node_id].setPopupContent(
                            makeTelemetryHtml(node_id)
                        );
                    }
                }

                function updateTelemetry(node_id, telemetry_json) {
                    try {
                        telemetryData[node_id] = JSON.parse(telemetry_json);

                        // Refresh popup content if the marker already exists.
                        if (markers[node_id]) {
                            markers[node_id].setPopupContent(
                                makeTelemetryHtml(node_id)
                            );
                        }
                    } catch (error) {
                        console.error("Unable to parse telemetry:", error);
                    }
                }

                // Remove all movement paths while keeping node markers,
                // labels, telemetry, and track colors.
                function clearTracks() {
                    Object.keys(tracks).forEach(function(node_id) {
                        var track = tracks[node_id];

                        if (track.line) {
                            map.removeLayer(track.line);
                            track.line = null;
                        }

                        track.arrowLayer.clearLayers();
                        track.flagLayer.clearLayers();

                        track.points = [];
                        track.times = [];
                        track.displayPoints = [];
                        track.displayTimes = [];
                        track.displayFixes = [];
                        // Invalidate requests already in flight so an old
                        // response cannot redraw a path after CLEAR is pressed.
                        track.generation++;
                        track.routeChain = Promise.resolve();
                        refreshNodePopup(node_id);
                    });

                    clearLoadedTracks();

                    console.log("Node movement paths cleared");
                }

                // ---------------------------------------------------------
                // GPX SAVE / LOAD SUPPORT
                // ---------------------------------------------------------

                // Previously saved tracks loaded for review are drawn on their
                // own layer (dashed lines) so they never mix with live tracks.
                var loadedLayer = L.featureGroup().addTo(map);
                var loadedActive = false;
                var loadedColors = [
                    '#000000', '#8c564b', '#008080',
                    '#800000', '#556b2f', '#4b0082'
                ];

                // Returns the currently displayed path of every node as JSON.
                function getTrackData() {
                    var out = [];
                    Object.keys(tracks).forEach(function(node_id) {
                        var track = tracks[node_id];
                        if (track.displayPoints &&
                            track.displayPoints.length > 0) {
                            out.push({
                                nodeId: node_id,
                                points: track.displayPoints,
                                times: track.displayTimes,
                                fixes: track.displayFixes
                            });
                        }
                    });
                    return JSON.stringify(out);
                }

                function clearLoadedTracks() {
                    loadedLayer.clearLayers();
                    loadedArrowLayer.clearLayers();
                    loadedArrowSources = [];
                    loadedActive = false;
                }

                function formatTime(ms) {
                    return new Date(ms).toLocaleString();
                }

                function formatDuration(seconds) {
                    seconds = Math.round(seconds);
                    var h = Math.floor(seconds / 3600);
                    var m = Math.floor((seconds % 3600) / 60);
                    var s = seconds % 60;
                    if (h > 0) return h + "h " + m + "m " + s + "s";
                    if (m > 0) return m + "m " + s + "s";
                    return s + "s";
                }

                // list: [{name, source, segments: [[[lat, lon], ...], ...],
                //         times: [[ms or null, ...], ...]}]
                function showLoadedTracks(list) {
                    clearLoadedTracks();

                    list.forEach(function(item, index) {
                        var segments = item.segments.filter(function(seg) {
                            return seg.length > 0;
                        });
                        if (segments.length === 0) return;

                        var color = loadedColors[index % loadedColors.length];

                        var meters = 0;
                        segments.forEach(function(seg) {
                            for (var i = 1; i < seg.length; i++) {
                                meters += L.latLng(seg[i - 1][0], seg[i - 1][1])
                                    .distanceTo(L.latLng(seg[i][0], seg[i][1]));
                            }
                        });

                        // Earliest / latest timestamp in the file, if any.
                        var firstTime = null;
                        var lastTime = null;
                        (item.times || []).forEach(function(seg) {
                            seg.forEach(function(t) {
                                if (t === null || t === undefined) return;
                                if (firstTime === null || t < firstTime) firstTime = t;
                                if (lastTime === null || t > lastTime) lastTime = t;
                            });
                        });

                        var text = escapeHtml(item.name) + " (saved) — " +
                            escapeHtml(formatTrackDistance(meters));

                        if (firstTime !== null && lastTime !== null) {
                            var seconds = (lastTime - firstTime) / 1000;
                            text += "<br>" + escapeHtml(formatTime(firstTime)) +
                                " → " + escapeHtml(formatTime(lastTime));
                            text += "<br>Duration: " +
                                escapeHtml(formatDuration(seconds));
                            if (seconds > 0) {
                                var mph = (meters / 1609.344) / (seconds / 3600);
                                text += " · Avg " + mph.toFixed(1) + " mph";
                            }
                        }
                        text += "<br><small>" + escapeHtml(item.source) +
                            "</small>";

                        L.polyline(segments, {
                            color: color,
                            weight: 4,
                            opacity: 0.9,
                            dashArray: '8 6'
                        }).bindTooltip(text, { sticky: true })
                          .addTo(loadedLayer);

                        loadedArrowSources.push({
                            segments: segments,
                            color: color
                        });

                        // Recreate the RSSI flags saved with the track.
                        (item.fixes || []).forEach(function(segFixes, s) {
                            (segFixes || []).forEach(function(fix, i) {
                                if (!fix || !item.segments[s] ||
                                    !item.segments[s][i]) {
                                    return;
                                }
                                var t = item.times && item.times[s]
                                    ? item.times[s][i] : null;
                                addRssiFlag(
                                    loadedLayer, color, item.segments[s][i],
                                    fix.rssi, t
                                );
                            });
                        });

                        var firstSeg = segments[0];
                        var lastSeg = segments[segments.length - 1];

                        L.circleMarker(firstSeg[0], {
                            radius: 7, color: '#ffffff', weight: 2,
                            fillColor: '#2e7d32', fillOpacity: 1
                        }).bindTooltip(
                            "Start: " + escapeHtml(item.name) +
                            (firstTime !== null
                                ? "<br>" + escapeHtml(formatTime(firstTime))
                                : "")
                        )
                          .addTo(loadedLayer);

                        L.circleMarker(lastSeg[lastSeg.length - 1], {
                            radius: 7, color: '#ffffff', weight: 2,
                            fillColor: '#c62828', fillOpacity: 1
                        }).bindTooltip(
                            "End: " + escapeHtml(item.name) +
                            (lastTime !== null
                                ? "<br>" + escapeHtml(formatTime(lastTime))
                                : "")
                        )
                          .addTo(loadedLayer);
                    });

                    if (loadedLayer.getLayers().length > 0) {
                        // Stop auto-centering on live positions so the
                        // loaded track stays in view. Press CLEAR to resume.
                        loadedActive = true;
                        map.fitBounds(loadedLayer.getBounds(), {
                            padding: [40, 40]
                        });
                    }

                    // If the zoom level changes, zoomend redraws these.
                    drawLoadedArrows();
                }

                function drawTrack(track) {
                    if (!track.line) {
                        track.line = L.polyline(track.displayPoints, {
                            color: track.color,
                            weight: 4,
                            opacity: 0.8
                        }).addTo(map);
                    } else {
                        track.line.setLatLngs(track.displayPoints);
                    }
                    drawTrackArrows(track);
                    // Keep the distance shown in an open popup current as
                    // routed geometry is appended to the recorded track.
                    refreshNodePopup(track.nodeId);
                }

                function routeSegment(start, end) {
                    var requestBody = {
                        locations: [
                            {
                                lat: start[0],
                                lon: start[1],
                                radius: SNAP_RADIUS_METERS
                            },
                            {
                                lat: end[0],
                                lon: end[1],
                                radius: SNAP_RADIUS_METERS
                            }
                        ],
                        costing: 'pedestrian',
                        units: 'kilometers',
                        // Valhalla's default JSON response encodes the leg
                        // geometry as a polyline6 string.
                        shape_format: 'polyline6'
                    };

                    return fetch(VALHALLA_ROUTE_URL, {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify(requestBody)
                    }).then(function(response) {
                        if (!response.ok) {
                            throw new Error('Routing service HTTP ' + response.status);
                        }
                        return response.json();
                    }).then(function(result) {
                        var shape = result && result.trip &&
                            result.trip.legs && result.trip.legs[0] &&
                            result.trip.legs[0].shape;

                        if (!shape) {
                            var detail = result && result.error ?
                                result.error : 'empty route geometry';
                            throw new Error('No road/trail route returned: ' + detail);
                        }

                        // Valhalla's JSON route response normally returns
                        // shape as an encoded polyline6 STRING, not a GeoJSON
                        // object. Decode it here. Also accept GeoJSON arrays
                        // in case the server is configured to return them.
                        if (typeof shape === 'object' &&
                            Array.isArray(shape.coordinates)) {
                            if (shape.coordinates.length < 2) {
                                throw new Error('Route geometry has fewer than two points');
                            }
                            return shape.coordinates.map(function(point) {
                                return [point[1], point[0]];
                            });
                        }

                        if (typeof shape !== 'string' || shape.length === 0) {
                            throw new Error('Unexpected Valhalla route geometry format');
                        }

                        return decodePolyline6(shape);
                    });
                }

                // Decode Valhalla's default polyline6 geometry into Leaflet
                // [latitude, longitude] pairs.
                function decodePolyline6(encoded) {
                    var index = 0;
                    var lat = 0;
                    var lon = 0;
                    var points = [];

                    function readDelta() {
                        var result = 0;
                        var shift = 0;
                        var byte;
                        do {
                            if (index >= encoded.length) {
                                throw new Error('Truncated Valhalla polyline');
                            }
                            byte = encoded.charCodeAt(index++) - 63;
                            result |= (byte & 0x1f) << shift;
                            shift += 5;
                        } while (byte >= 0x20);
                        return (result & 1) ? ~(result >> 1) : (result >> 1);
                    }

                    while (index < encoded.length) {
                        lat += readDelta();
                        lon += readDelta();
                        points.push([lat / 1e6, lon / 1e6]);
                    }

                    if (points.length < 2) {
                        throw new Error('Decoded route has fewer than two points');
                    }
                    return points;
                }

                function appendTrackSegment(node_id, track, start, end, generation,
                                            startTime, endTime, endRssi) {
                    // Capture the setting now so a segment recorded while
                    // snapping was on/off keeps that behavior even if the
                    // option is toggled before its turn in the chain.
                    var snapThisSegment = snapping;

                    // Chain requests per node so responses are applied in GPS
                    // order even if the routing service responds out of order.
                    track.routeChain = track.routeChain.then(function() {
                        if (!snapThisSegment) {
                            return [start, end];
                        }
                        return routeSegment(start, end).catch(function(error) {
                            console.warn(
                                'Road/trail snapping unavailable for node ' +
                                node_id + '; using straight GPS segment:', error
                            );
                            return [start, end];
                        });
                    }).then(function(segment) {
                        if (track.generation !== generation) return;

                        // Skip the first coordinate because it is already the
                        // end of the preceding displayed segment.
                        // Snapped geometry has many more points than GPS fixes,
                        // so spread the time between the two fixes across the
                        // segment in proportion to the distance covered.
                        var cumulative = [0];
                        for (var i = 1; i < segment.length; i++) {
                            cumulative.push(
                                cumulative[i - 1] +
                                L.latLng(segment[i - 1][0], segment[i - 1][1])
                                    .distanceTo(
                                        L.latLng(segment[i][0], segment[i][1])
                                    )
                            );
                        }
                        var segmentLength = cumulative[cumulative.length - 1];

                        for (var j = 1; j < segment.length; j++) {
                            var fraction = segmentLength > 0
                                ? cumulative[j] / segmentLength
                                : j / (segment.length - 1);
                            track.displayPoints.push(segment[j]);
                            track.displayTimes.push(Math.round(
                                startTime + (endTime - startTime) * fraction
                            ));
                            // Only the last point is the actual GPS fix.
                            track.displayFixes.push(
                                j === segment.length - 1
                                    ? { rssi: endRssi }
                                    : null
                            );
                        }
                        drawTrack(track);
                    });
                }

                function updateNode(node_id, lat, lon, label, rssi) {
                    // Automatically center the map on Michael's position.
                    if (!loadedActive &&
                        String(label).trim().toLowerCase() === "michael") {
                        map.setView([lat, lon], map.getZoom(), {
                            animate: true
                        });
                    }

                    var color = getNodeColor(node_id);

                    if (!markers[node_id]) {
                        markers[node_id] = L.marker([lat, lon]).addTo(map);

                        markers[node_id].bindTooltip(label, {
                            permanent: true,
                            direction: 'top',
                            offset: [0, -10]
                        });

                        // Click the node icon to open its telemetry popup.
                        markers[node_id].bindPopup(
                            makeTelemetryHtml(node_id)
                        );
                    } else {
                        markers[node_id].setLatLng([lat, lon]);
                        markers[node_id].setTooltipContent(label);
                    }

                    // While recording is stopped the marker still moves, but
                    // the position is not added to the track.
                    if (!recording) {
                        return;
                    }

                    var track = tracks[node_id];
                    var points = track.points;
                    var last = points.length
                        ? points[points.length - 1]
                        : null;
                    var current = [lat, lon];

                    var now = Date.now();
                    if (rssi === undefined || rssi === null || isNaN(rssi)) {
                        rssi = null;
                    }

                    if (!last) {
                        points.push(current);
                        track.times.push(now);
                        track.displayPoints.push(current);
                        track.displayTimes.push(now);
                        track.displayFixes.push({ rssi: rssi });
                        addRssiFlag(track.flagLayer, track.color, current,
                                    rssi, now);
                        drawTrack(track);
                    } else if (last[0] !== lat || last[1] !== lon) {
                        var startTime = track.times[track.times.length - 1];
                        points.push(current);
                        track.times.push(now);
                        addRssiFlag(track.flagLayer, track.color, current,
                                    rssi, now);
                        appendTrackSegment(
                            node_id,
                            track,
                            last,
                            current,
                            track.generation,
                            startTime,
                            now,
                            rssi
                        );
                    }
                }

                // Force Leaflet to recalculate its size.
                setTimeout(function() {
                    map.invalidateSize(true);
                }, 300);
            </script>
        </body>
        </html>
        """

        self.map_view.setHtml(html)

    def touch_node(self, node_id, timestamp=None):
        """Record that a node was heard from (now, unless a time is given)."""
        node_id = str(node_id)
        timestamp = float(timestamp) if timestamp else time.time()
        if timestamp > self.last_seen.get(node_id, 0):
            self.last_seen[node_id] = timestamp

    def is_recently_seen(self, node_id):
        """True when the node was heard within NODE_SEEN_WINDOW_SECONDS."""
        seen = self.last_seen.get(str(node_id))
        if seen is None:
            return False
        return (time.time() - seen) <= NODE_SEEN_WINDOW_SECONDS

    def register_node(self, node_id, label):
        """Remember a node that has location info and expose it in the selector."""
        node_id = str(node_id)
        label = str(label or node_id)
        self.known_nodes[node_id] = label
        # Always emit: a node that aged out of the selector must be able to
        # reappear when it is heard from again. add_node_to_selector()
        # de-duplicates and applies the 1 hour filter.
        self.node_discovered.emit(node_id, label)

    def add_node_to_selector(self, node_id, label):
        """Refresh the drop-down after a node is heard from."""
        self.known_nodes[str(node_id)] = str(label)
        self.refresh_selector()

    def refresh_selector(self):
        """Show recently seen nodes, most recently seen first.

        Nodes not heard from in the last hour are left out. The list is only
        rebuilt when its contents or order actually change.
        """
        recent = [
            node_id for node_id in self.known_nodes
            if self.is_recently_seen(node_id)
        ]
        recent.sort(key=lambda n: self.last_seen.get(n, 0), reverse=True)

        current = [
            self.node_selector.itemData(i)
            for i in range(1, self.node_selector.count())
        ]
        labels = [
            self.node_selector.itemText(i)
            for i in range(1, self.node_selector.count())
        ]
        wanted_labels = [self.known_nodes[n] for n in recent]

        if current == recent and labels == wanted_labels:
            return

        selected = self.node_selector.currentData()

        self.node_selector.blockSignals(True)
        # Keep index 0, the "Add node to map..." placeholder.
        while self.node_selector.count() > 1:
            self.node_selector.removeItem(1)
        for node_id in recent:
            self.node_selector.addItem(self.known_nodes[node_id], node_id)

        new_index = 0
        if selected in recent:
            new_index = recent.index(selected) + 1
        self.node_selector.setCurrentIndex(new_index)
        self.node_selector.blockSignals(False)

    def prune_selector(self):
        """Timer callback: drop nodes not seen in the last hour."""
        self.refresh_selector()

    def add_selected_node(self, index):
        node_id = self.node_selector.itemData(index)
        if not node_id:
            return

        node_id = str(node_id)
        self.displayed_nodes.add(node_id)
        position = self.latest_positions.get(node_id)

        if position:
            self.move_node(
                node_id,
                position["latitude"],
                position["longitude"],
                position["label"],
                position.get("rssi")
            )
            self.show_status(f"Added {position['label']} to the map")
        else:
            self.show_status(
                f"{self.known_nodes.get(node_id, node_id)} selected; "
                "waiting for GPS coordinates"
            )

    def send_message(self):
        node_id = self.node_selector.currentData()
        message = self.message_input.text().strip()

        if not node_id:
            QMessageBox.warning(
                self.ui, "No node selected", "Select a node before sending."
            )
            return

        if not message:
            QMessageBox.warning(
                self.ui, "Message required", "Enter a message to send."
            )
            return

        if self.mesh_interface is None:
            QMessageBox.warning(
                self.ui, "Not connected", "Meshtastic is not connected."
            )
            return

        node_id = str(node_id)
        node_label = self.known_nodes.get(node_id, node_id)

        def onAckNak(packet):
            routing = packet.get("decoded", {}).get("routing", {})
            error = routing.get("errorReason")
            if error in (None, "NONE"):
                result = f"{node_label} acknowledged the message."
            else:
                result = f"Message delivery to {node_label} failed: {error}."
            self.message_result.emit(result)

        try:
            self.mesh_interface.sendText(
                message,
                destinationId=node_id,
                wantAck=True,
                onResponse=onAckNak
            )
        except Exception as error:
            QMessageBox.critical(
                self.ui,
                "Message failed",
                f"Could not send message to "
                f"{node_label}:\n{error}"
            )
            return

        self.message_input.clear()
        self.show_status(
            f"Message sent to radio for {node_label}; awaiting node acknowledgment."
        )

    # =========================================================
    # MAP UPDATE FUNCTIONS
    # =========================================================

    def map_loaded(self, success):

        if not success:
            print("Map failed to load")
            return

        print("Map loaded successfully")
        self.map_ready = True

        # Display positions received before the map loaded.
        for node_id, position in self.pending_positions.items():
            self.move_node(
                node_id,
                position["latitude"],
                position["longitude"],
                position["label"],
                position.get("rssi")
            )

        self.pending_positions.clear()

        # Send telemetry received before the map loaded.
        for node_id, telemetry_json in self.pending_telemetry.items():
            self.send_telemetry_to_map(node_id, telemetry_json)

        for node_id, hops in self.pending_hops.items():
            self.send_hops_to_map(node_id, hops)

        for node_id, gps_time in self.pending_gps_times.items():
            self.send_gps_time_to_map(node_id, gps_time)

        self.send_recording_state()
        self.send_snapping_state()

    def update_record_buttons(self):
        # Only the action that can currently be taken is enabled.
        self.start_record_button.setEnabled(not self.recording)
        self.stop_record_button.setEnabled(self.recording)

    def set_recording(self, recording):
        """Start or stop adding node positions to the movement tracks.

        Node markers keep following their latest position either way; only
        the recorded track (and so the saved GPX) is paused.
        """
        self.recording = bool(recording)
        self.update_record_buttons()
        self.show_status(
            "Recording started" if self.recording else "Recording stopped"
        )

        if self.map_ready:
            self.send_recording_state()

    def send_recording_state(self):
        self.map_view.page().runJavaScript(
            f"setRecording({'true' if self.recording else 'false'});"
        )

    def set_snapping(self, enabled):
        """Enable or disable snapping of new track segments to roads/trails.

        Only affects segments recorded after the change; existing track
        geometry is left as it is.
        """
        self.snapping = bool(enabled)
        self.show_status(
            "Track snapping enabled" if self.snapping
            else "Track snapping disabled"
        )

        if self.map_ready:
            self.send_snapping_state()

    def send_snapping_state(self):
        self.map_view.page().runJavaScript(
            f"setSnapping({'true' if self.snapping else 'false'});"
        )

    def clear_tracks(self):
        """Clear the movement paths from the map, leaving node markers."""
        if not self.map_ready:
            return

        self.map_view.page().runJavaScript("clearTracks();")

    # =========================================================
    # GPX SAVE / LOAD
    # =========================================================

    @staticmethod
    def style_action_button(button, base, hover, pressed):
        button.setMinimumHeight(42)
        button.setMaximumHeight(48)
        button.setStyleSheet(
            "QPushButton {"
            f" background-color: {base};"
            " color: white;"
            " font-weight: bold;"
            " font-size: 14px;"
            " border: none;"
            " padding: 8px 16px;"
            "}"
            f"QPushButton:hover {{ background-color: {hover}; }}"
            f"QPushButton:pressed {{ background-color: {pressed}; }}"
            "QPushButton:disabled {"
            " background-color: #9e9e9e; color: #e0e0e0; }"
        )

    def save_gpx(self):
        """Ask the map for the current paths, then write them to a .gpx."""
        if not self.map_ready:
            QMessageBox.information(
                self.ui, "Save GPX", "The map has not finished loading yet."
            )
            return

        self.map_view.page().runJavaScript(
            "getTrackData();", self.on_track_data_for_save
        )

    def on_track_data_for_save(self, result):
        try:
            data = json.loads(result) if result else []
        except (TypeError, ValueError):
            data = []

        tracks = []
        for item in data:
            node_id = str(item.get("nodeId", ""))
            points = item.get("points") or []
            if not points:
                continue
            times = item.get("times") or []
            if len(times) != len(points):
                times = [None] * len(points)
            fixes = item.get("fixes") or []
            if len(fixes) != len(points):
                fixes = [None] * len(points)
            tracks.append({
                "node_id": node_id,
                "name": self.known_nodes.get(node_id, node_id),
                "points": points,
                "times": times,
                "fixes": fixes
            })

        # Let the web engine callback return before opening a modal dialog.
        QTimer.singleShot(0, lambda: self.write_gpx_file(tracks))

    def write_gpx_file(self, tracks):
        if not tracks:
            QMessageBox.information(
                self.ui, "Save GPX", "There is no path to save yet."
            )
            return

        os.makedirs(GPX_FOLDER, exist_ok=True)
        default_name = datetime.now().strftime(
            "meshtastic_track_%Y%m%d_%H%M%S.gpx"
        )

        path, _ = QFileDialog.getSaveFileName(
            self.ui,
            "Save path as GPX",
            os.path.join(GPX_FOLDER, default_name),
            "GPX files (*.gpx)"
        )

        if not path:
            return

        if not path.lower().endswith(".gpx"):
            path += ".gpx"

        try:
            self.build_gpx(tracks, path)
        except Exception as error:
            traceback.print_exc()
            QMessageBox.warning(
                self.ui, "Save GPX", f"Could not save the file:\n{error}"
            )
            return

        total_points = sum(len(t["points"]) for t in tracks)
        message = (
            f"Saved {len(tracks)} track(s), {total_points} points to {path}"
        )
        self.show_status(message)
        QMessageBox.information(self.ui, "Save GPX", message)

    @staticmethod
    def build_gpx(tracks, path):
        ET.register_namespace("", GPX_NS)
        ET.register_namespace("mt", MT_NS)

        def tag(name):
            return f"{{{GPX_NS}}}{name}"

        def mt_tag(name):
            return f"{{{MT_NS}}}{name}"

        gpx = ET.Element(tag("gpx"), {
            "version": "1.1",
            "creator": "Meshtastic Tracker"
        })

        metadata = ET.SubElement(gpx, tag("metadata"))
        ET.SubElement(metadata, tag("name")).text = "Meshtastic Tracker export"
        ET.SubElement(metadata, tag("time")).text = (
            datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        )

        for track in tracks:
            trk = ET.SubElement(gpx, tag("trk"))
            ET.SubElement(trk, tag("name")).text = track["name"]
            ET.SubElement(trk, tag("desc")).text = (
                f"Meshtastic node {track['node_id']}"
            )
            segment = ET.SubElement(trk, tag("trkseg"))

            times = track.get("times") or [None] * len(track["points"])

            fixes = track.get("fixes") or [None] * len(track["points"])

            for (latitude, longitude), time_ms, fix in zip(
                track["points"], times, fixes
            ):
                trkpt = ET.SubElement(segment, tag("trkpt"), {
                    "lat": f"{float(latitude):.7f}",
                    "lon": f"{float(longitude):.7f}"
                })
                if time_ms is not None:
                    ET.SubElement(trkpt, tag("time")).text = (
                        datetime.fromtimestamp(
                            time_ms / 1000, timezone.utc
                        ).strftime("%Y-%m-%dT%H:%M:%SZ")
                    )

                # Recorded GPS fixes carry their received RSSI (dBm) so the
                # flags can be rebuilt when the file is loaded again.
                if fix is not None:
                    extensions = ET.SubElement(trkpt, tag("extensions"))
                    ET.SubElement(extensions, mt_tag("fix")).text = "1"
                    rssi = fix.get("rssi")
                    if rssi is not None:
                        ET.SubElement(extensions, mt_tag("rssi")).text = (
                            str(int(round(float(rssi))))
                        )

        tree = ET.ElementTree(gpx)
        ET.indent(tree, space="  ")
        tree.write(path, encoding="utf-8", xml_declaration=True)

    def load_gpx(self):
        """Load one or more saved .gpx files and show them for review."""
        if not self.map_ready:
            QMessageBox.information(
                self.ui, "Load GPX", "The map has not finished loading yet."
            )
            return

        os.makedirs(GPX_FOLDER, exist_ok=True)

        paths, _ = QFileDialog.getOpenFileNames(
            self.ui,
            "Load saved GPX file(s)",
            GPX_FOLDER,
            "GPX files (*.gpx);;All files (*)"
        )

        if not paths:
            return

        loaded = []
        errors = []

        for path in paths:
            try:
                loaded.extend(self.parse_gpx(path))
            except Exception as error:
                errors.append(f"{os.path.basename(path)}: {error}")

        if loaded:
            self.map_view.page().runJavaScript(
                f"showLoadedTracks({json.dumps(loaded)});"
            )
            self.show_status(
                f"Loaded {len(loaded)} saved track(s) from "
                f"{len(paths) - len(errors)} file(s)"
            )

        if errors or not loaded:
            detail = "\n".join(errors) if errors else (
                "No tracks were found in the selected file(s)."
            )
            QMessageBox.warning(self.ui, "Load GPX", detail)

    @staticmethod
    def parse_gpx_time(text):
        """Convert a GPX ISO-8601 time string to epoch milliseconds."""
        if not text:
            return None
        text = text.strip()
        try:
            if text.endswith(("Z", "z")):
                text = text[:-1] + "+00:00"
            # Older Python versions only accept 3 or 6 fractional digits.
            if "." in text:
                head, rest = text.split(".", 1)
                digits = ""
                while rest and rest[0].isdigit():
                    digits += rest[0]
                    rest = rest[1:]
                text = f"{head}.{digits[:6].ljust(6, '0')}{rest}"
            moment = datetime.fromisoformat(text)
            if moment.tzinfo is None:
                moment = moment.replace(tzinfo=timezone.utc)
            return int(moment.timestamp() * 1000)
        except ValueError:
            return None

    @staticmethod
    def parse_gpx_fix(extensions):
        """Read the <mt:fix>/<mt:rssi> extension of a <trkpt>.

        Returns {"rssi": int or None} for a recorded GPS fix, or None for a
        point without the extension (for example a routed in-between point,
        or any point from a file saved before RSSI was stored).
        """
        is_fix = False
        rssi = None
        for element in extensions:
            name = element.tag.rsplit("}", 1)[-1]
            if name == "fix":
                is_fix = True
            elif name == "rssi":
                is_fix = True
                try:
                    rssi = int(round(float((element.text or "").strip())))
                except ValueError:
                    rssi = None
        return {"rssi": rssi} if is_fix else None

    @staticmethod
    def parse_gpx(path):
        """Return [{name, source, segments}] for every <trk> in a GPX file."""

        def local(element):
            return element.tag.rsplit("}", 1)[-1]

        root = ET.parse(path).getroot()
        source = os.path.basename(path)
        tracks = []

        for trk in root.iter():
            if local(trk) != "trk":
                continue

            name = "Track"
            segments = []
            segment_times = []
            segment_fixes = []

            for child in trk:
                kind = local(child)

                if kind == "name" and child.text and child.text.strip():
                    name = child.text.strip()

                elif kind == "trkseg":
                    points = []
                    times = []
                    fixes = []
                    for point in child:
                        if local(point) != "trkpt":
                            continue
                        try:
                            latitude = float(point.attrib["lat"])
                            longitude = float(point.attrib["lon"])
                        except (KeyError, ValueError):
                            continue
                        points.append([latitude, longitude])

                        time_ms = None
                        fix = None
                        for sub in point:
                            kind_sub = local(sub)
                            if kind_sub == "time":
                                time_ms = MainWindow.parse_gpx_time(sub.text)
                            elif kind_sub == "extensions":
                                fix = MainWindow.parse_gpx_fix(sub)
                        times.append(time_ms)
                        fixes.append(fix)
                    if points:
                        segments.append(points)
                        segment_times.append(times)
                        segment_fixes.append(fixes)

            if segments:
                tracks.append({
                    "name": name,
                    "source": source,
                    "segments": segments,
                    "times": segment_times,
                    "fixes": segment_fixes
                })

        return tracks

    def move_node(self, node_id, latitude, longitude, label, rssi=None):

        js = f"""
            updateNode(
                {json.dumps(str(node_id))},
                {float(latitude)},
                {float(longitude)},
                {json.dumps(str(label))},
                {json.dumps(rssi)}
            );
        """
        self.map_view.page().runJavaScript(js)

    def update_map_position(
        self,
        node_id,
        latitude,
        longitude,
        label,
        rssi=None
    ):

        print(
            f"GPS: {label} ({node_id}) "
            f"{latitude:.6f}, {longitude:.6f} "
            f"RSSI: {rssi if rssi is not None else 'n/a'}"
        )

        position = {
            "latitude": latitude,
            "longitude": longitude,
            "label": label,
            "rssi": rssi
        }

        if not self.map_ready:
            self.pending_positions[node_id] = position
            return

        self.move_node(node_id, latitude, longitude, label, rssi)

    def update_map_telemetry(self, node_id, telemetry_json):
        # Keep the latest telemetry, including while the map is loading.
        self.pending_telemetry[node_id] = telemetry_json

        if self.map_ready:
            self.send_telemetry_to_map(node_id, telemetry_json)

    def send_telemetry_to_map(self, node_id, telemetry_json):
        js = (
            "updateTelemetry("
            + json.dumps(str(node_id))
            + ","
            + json.dumps(telemetry_json)
            + ");"
        )
        self.map_view.page().runJavaScript(js)

    def update_map_hops(self, node_id, hops):
        # Keep the latest hop count, including while the map is loading.
        self.pending_hops[node_id] = hops

        if self.map_ready:
            self.send_hops_to_map(node_id, hops)

    def send_hops_to_map(self, node_id, hops):
        js = (
            "updateHops("
            + json.dumps(str(node_id))
            + ","
            + json.dumps(int(hops))
            + ");"
        )
        self.map_view.page().runJavaScript(js)

    def record_gps_time(self, node_id, timestamp=None):
        """Note when a GPS location was received for a node.

        timestamp is epoch seconds; None means now. Falsy values from the
        node database (missing/0) are ignored.
        """
        if timestamp is None:
            timestamp = time.time()
        if not timestamp:
            return

        text = (
            datetime.fromtimestamp(float(timestamp)).astimezone()
            .strftime("%Y-%m-%d %H:%M:%S %Z")
        )
        self.gps_time_update.emit(str(node_id), text)

    def update_map_gps_time(self, node_id, gps_time):
        # Keep the latest value, including while the map is loading.
        self.pending_gps_times[node_id] = gps_time

        if self.map_ready:
            self.send_gps_time_to_map(node_id, gps_time)

    def send_gps_time_to_map(self, node_id, gps_time):
        js = (
            "updateGpsTime("
            + json.dumps(str(node_id))
            + ","
            + json.dumps(gps_time)
            + ");"
        )
        self.map_view.page().runJavaScript(js)

    # =========================================================
    # MESHTASTIC CONNECTION
    # =========================================================

    def connect_to_meshtastic(self):

        pub.subscribe(
            self.on_position_packet,
            "meshtastic.receive.position"
        )

        pub.subscribe(
            self.on_telemetry_packet,
            "meshtastic.receive.telemetry"
        )

        pub.subscribe(
            self.on_text_packet,
            "meshtastic.receive.text"
        )

        pub.subscribe(
            self.on_meshtastic_connected,
            "meshtastic.connection.established"
        )

        pub.subscribe(
            self.on_meshtastic_disconnected,
            "meshtastic.connection.lost"
        )

        thread = threading.Thread(
            target=self.open_meshtastic_connection,
            daemon=True
        )
        thread.start()

    def open_meshtastic_connection(self):

        try:
            self.status_update.emit(
                f"Connecting to {MESHTASTIC_HOST}..."
            )

            self.mesh_interface = TCPInterface(
                hostname=MESHTASTIC_HOST
            )

            self.status_update.emit(
                f"Connected to {MESHTASTIC_HOST}"
            )

        except Exception:
            traceback.print_exc()
            self.status_update.emit(
                "Meshtastic connection failed"
            )

    # =========================================================
    # MESHTASTIC CALLBACKS
    # =========================================================

    def on_meshtastic_connected(self, interface, topic=None):

        print("Meshtastic connection established")
        self.status_update.emit("Meshtastic connected")

        # Populate the selector with every node in the node database that
        # has location information, including nodes that do not pass the
        # default map display filter.
        nodes = interface.nodes or {}

        for node_id, node in nodes.items():
            user = node.get("user", {})
            label = (
                user.get("longName")
                or user.get("shortName")
                or str(node_id)
            )
            position = node.get("position", {})
            latitude, longitude = self.extract_coordinates(position)

            # Only nodes with location information are offered in the
            # drop-down; emit_position() registers the node.
            if not self.is_valid_position(latitude, longitude):
                continue

            # Use the node database's last-heard time so the 1 hour filter
            # applies to nodes known before this session started.
            self.touch_node(node_id, node.get("lastHeard"))

            self.record_gps_time(node_id, position.get("time"))

            if node.get("hopsAway") is not None:
                self.hops_update.emit(str(node_id), int(node["hopsAway"]))

            self.emit_position(
                node_id,
                latitude,
                longitude,
                label
            )

    def on_meshtastic_disconnected(self, interface, topic=None):

        print("Meshtastic connection lost")
        self.status_update.emit("Meshtastic connection lost")

    def get_packet_node_id(self, packet):
        node_id = packet.get("fromId")

        if not node_id:
            node_num = packet.get("from")
            if node_num is None:
                return None
            node_id = f"!{node_num:08x}"

        return str(node_id)

    def update_hops(self, packet, interface, node_id):
        """Work out how many hops away a node is and send it to the map.

        A packet carries hopStart (the limit it was sent with) and hopLimit
        (what remains), so hops taken = hopStart - hopLimit; 0 means direct.
        Older firmware leaves hopStart at 0, so fall back to the node
        database's hopsAway value.
        """
        hops = None

        hop_start = packet.get("hopStart")
        hop_limit = packet.get("hopLimit")
        if hop_start and hop_limit is not None and hop_start >= hop_limit:
            hops = hop_start - hop_limit

        if hops is None:
            node_info = (interface.nodes or {}).get(node_id, {})
            hops = node_info.get("hopsAway")

        if hops is not None:
            self.hops_update.emit(node_id, int(hops))

    @staticmethod
    def get_packet_rssi(packet):
        """RSSI (dBm) this radio measured for the packet, or None.

        This is the signal strength of the last hop heard by the connected
        radio. Packets that did not arrive over the air (for example the
        local node's own) report 0, which is treated as unknown.
        """
        rssi = packet.get("rxRssi")
        if rssi is None:
            rssi = packet.get("rx_rssi")
        try:
            rssi = int(rssi)
        except (TypeError, ValueError):
            return None
        return rssi if rssi != 0 else None

    def get_node_label(self, interface, node_id):
        node_info = (interface.nodes or {}).get(node_id, {})
        user = node_info.get("user", {})

        return (
            user.get("longName")
            or user.get("shortName")
            or node_id
        )

    def on_position_packet(self, packet, interface):

        decoded = packet.get("decoded", {})
        position = decoded.get("position", {})

        latitude, longitude = self.extract_coordinates(position)

        if not self.is_valid_position(latitude, longitude):
            return

        node_id = self.get_packet_node_id(packet)
        if not node_id:
            return

        label = self.get_node_label(interface, node_id)
        self.touch_node(node_id)
        self.update_hops(packet, interface, node_id)
        self.record_gps_time(node_id)
        self.register_node(node_id, label)

        rssi = self.get_packet_rssi(packet)

        print(
            f"Position packet from {label}: "
            f"{latitude}, {longitude} "
            f"(RSSI: {rssi if rssi is not None else 'n/a'})"
        )

        self.emit_position(
            node_id,
            latitude,
            longitude,
            label,
            rssi
        )

    def on_telemetry_packet(self, packet, interface):
        try:
            decoded = packet.get("decoded", {})
            telemetry = decoded.get("telemetry")

            if not telemetry:
                return

            node_id = self.get_packet_node_id(packet)
            if not node_id:
                return

            label = self.get_node_label(interface, node_id)

            # Telemetry has no location, so it must not add a new node to the
            # selector; the node is listed once a position is received.
            # It does count as the node being seen, so a node that already
            # has a known position stays (or returns) in the selector.
            self.touch_node(node_id)
            self.update_hops(packet, interface, node_id)
            if node_id in self.latest_positions:
                self.register_node(node_id, label)

            # Record the local arrival time for this telemetry packet.
            telemetry = dict(telemetry)
            telemetry["lastReceived"] = (
                datetime.now().astimezone()
                .strftime("%Y-%m-%d %H:%M:%S %Z")
            )
            telemetry_json = json.dumps(telemetry, default=str)

            print(f"Telemetry received from {label}: {telemetry}")

            self.telemetry_update.emit(node_id, telemetry_json)

        except Exception:
            traceback.print_exc()

    def on_text_packet(self, packet, interface):
        decoded = packet.get("decoded", {})
        text = decoded.get("text")
        if text is None:
            return

        node_id = self.get_packet_node_id(packet)
        label = self.get_node_label(interface, node_id) if node_id else "Unknown node"
        received_at = datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S")
        self.received_message.emit(
            f"{label} ({node_id or 'unknown'})",
            f"[{received_at}]\n{text}"
        )

    def show_received_message(self, sender, message):
        QMessageBox.information(
            self.ui,
            "New Meshtastic Message",
            f"From: {sender}\n{message}"
        )

    # =========================================================
    # GPS COORDINATE EXTRACTION
    # =========================================================

    @staticmethod
    def extract_coordinates(position):

        latitude = position.get("latitude")
        longitude = position.get("longitude")

        # Fall back to integer coordinate fields.
        if latitude is None:
            latitude_i = position.get("latitudeI")
            if latitude_i is None:
                latitude_i = position.get("latitude_i")
            if latitude_i is not None:
                latitude = latitude_i * 1e-7

        if longitude is None:
            longitude_i = position.get("longitudeI")
            if longitude_i is None:
                longitude_i = position.get("longitude_i")
            if longitude_i is not None:
                longitude = longitude_i * 1e-7

        if latitude is None or longitude is None:
            return None, None

        try:
            return float(latitude), float(longitude)
        except (TypeError, ValueError):
            return None, None

    @staticmethod
    def is_valid_position(latitude, longitude):
        """True when the coordinates are usable location information."""
        if latitude is None or longitude is None:
            return False
        if not (-90 <= latitude <= 90):
            return False
        if not (-180 <= longitude <= 180):
            return False
        if latitude == 0 or longitude == 0:
            return False
        return True

    def emit_position(
        self,
        node_id,
        latitude,
        longitude,
        label,
        rssi=None
    ):

        if not self.is_valid_position(latitude, longitude):
            return

        node_id = str(node_id)
        label = str(label)
        self.register_node(node_id, label)

        # Cache every valid position, even when its node is not currently
        # displayed. The selector can display it later without waiting for
        # another GPS packet.
        self.latest_positions[node_id] = {
            "latitude": float(latitude),
            "longitude": float(longitude),
            "label": label,
            "rssi": rssi
        }

        # Preserve the default Mike/Michael display, while allowing any
        # discovered node to be added explicitly through the selector.
        if (
            label.strip().casefold() not in ALLOWED_NODE_NAMES
            and node_id not in self.displayed_nodes
        ):
            return

        self.displayed_nodes.add(node_id)

        print(
            f"Displaying {label}: "
            f"{latitude}, {longitude}"
        )

        self.gps_update.emit(
            str(node_id),
            float(latitude),
            float(longitude),
            str(label),
            rssi
        )

    # =========================================================
    # STATUS
    # =========================================================

    def show_status(self, message):
        print(message)
        self.ui.statusBar().showMessage(message, 10000)

    # =========================================================
    # SHUTDOWN
    # =========================================================

    def shutdown(self):

        print("Shutting down...")

        pub.unsubscribe(
            self.on_position_packet,
            "meshtastic.receive.position"
        )

        pub.unsubscribe(
            self.on_telemetry_packet,
            "meshtastic.receive.telemetry"
        )

        pub.unsubscribe(
            self.on_text_packet,
            "meshtastic.receive.text"
        )

        pub.unsubscribe(
            self.on_meshtastic_connected,
            "meshtastic.connection.established"
        )

        pub.unsubscribe(
            self.on_meshtastic_disconnected,
            "meshtastic.connection.lost"
        )

        if self.mesh_interface is not None:
            try:
                self.mesh_interface.close()
            except Exception as error:
                print(f"Error closing connection: {error}")


# =============================================================
# MAIN
# =============================================================

if __name__ == "__main__":

    app = QApplication(sys.argv)

    window = MainWindow()

    app.aboutToQuit.connect(window.shutdown)

    sys.exit(app.exec())