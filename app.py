# -*- coding: utf-8 -*-
"""
GPS軌跡 自動生成システム v128
restore_local_boundary_search_pre_pin

目的:
- 通常エリアは「戸建て/小型アパート/不明」扱いで道路沿い風のぐにゃぐにゃ軌跡を作る
- 団地枠だけを別指定し、通常ルートから枝道として入って同じ通常ルートへ戻す
- 離れた通常エリア同士を勝手に直線接続しない
- 町丁目間の接続は、ユーザーが描いた「移動線」だけを使う
- エリア同士/団地同士を直接つないでジャンプさせる処理を禁止

起動:
    streamlit run app_mansion_photo_v116_restore_local_boundary_search_pre_pin.py

必要:
    pip install streamlit folium streamlit-folium shapely requests
"""

from __future__ import annotations

import datetime as _dt
import json
import math
import random
import re
import time
import xml.etree.ElementTree as ET
from pathlib import Path
from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import streamlit as st

try:
    import networkx as nx
except Exception:  # pragma: no cover
    nx = None

try:
    import osmnx as ox
    try:
        ox.settings.use_cache = True
        ox.settings.log_console = False
        ox.settings.requests_timeout = 60
    except Exception:
        pass
except Exception:  # pragma: no cover
    ox = None


try:
    import folium
    from folium.plugins import Draw
    from streamlit_folium import st_folium
except Exception as e:  # pragma: no cover
    folium = None
    Draw = None
    st_folium = None

try:
    import requests
except Exception:  # pragma: no cover
    requests = None

try:
    from shapely.geometry import LineString, Point, Polygon, shape
    from shapely.ops import unary_union
except Exception as e:  # pragma: no cover
    LineString = None
    Point = None
    Polygon = None
    shape = None
    unary_union = None

LatLon = Tuple[float, float]

EARTH_R = 6371008.8
ROAD_CACHE_DIR = Path("data") / "road_cache"
try:
    ROAD_CACHE_DIR.mkdir(parents=True, exist_ok=True)
except Exception:
    pass


@dataclass
class DrawArea:
    name: str
    kind: str  # normal / danchi / move
    coords: List[LatLon]


# -----------------------------
# 基本距離・補間
# -----------------------------

def haversine_m(a: LatLon, b: LatLon) -> float:
    lat1, lon1 = map(math.radians, a)
    lat2, lon2 = map(math.radians, b)
    dlat = lat2 - lat1
    dlon = lon2 - lon1
    h = math.sin(dlat / 2) ** 2 + math.cos(lat1) * math.cos(lat2) * math.sin(dlon / 2) ** 2
    return 2 * EARTH_R * math.asin(math.sqrt(h))


def total_distance_m(points: Sequence[LatLon]) -> float:
    return sum(haversine_m(points[i - 1], points[i]) for i in range(1, len(points)))


def lerp(a: LatLon, b: LatLon, t: float) -> LatLon:
    return (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t)


def densify(points: Sequence[LatLon], step_m: float = 7.0) -> List[LatLon]:
    if len(points) < 2:
        return list(points)
    out: List[LatLon] = [points[0]]
    for a, b in zip(points[:-1], points[1:]):
        d = max(haversine_m(a, b), 0.01)
        n = max(1, int(math.ceil(d / step_m)))
        for i in range(1, n + 1):
            out.append(lerp(a, b, i / n))
    return out


def local_xy(origin: LatLon, p: LatLon) -> Tuple[float, float]:
    lat0, lon0 = map(math.radians, origin)
    lat, lon = map(math.radians, p)
    x = (lon - lon0) * math.cos(lat0) * EARTH_R
    y = (lat - lat0) * EARTH_R
    return x, y


def local_ll(origin: LatLon, xy: Tuple[float, float]) -> LatLon:
    lat0, lon0 = map(math.radians, origin)
    x, y = xy
    lat = lat0 + y / EARTH_R
    lon = lon0 + x / (math.cos(lat0) * EARTH_R)
    return (math.degrees(lat), math.degrees(lon))


def wiggle_polyline(points: Sequence[LatLon], amp_m: float, every_m: float, seed: int) -> List[LatLon]:
    """線に小さな揺れを付ける。移動線はampを小さくする。"""
    if len(points) < 2:
        return list(points)
    rng = random.Random(seed)
    dense = densify(points, every_m)
    out = [dense[0]]
    for i in range(1, len(dense) - 1):
        prev_p, p, next_p = dense[i - 1], dense[i], dense[i + 1]
        origin = p
        x1, y1 = local_xy(origin, prev_p)
        x2, y2 = local_xy(origin, next_p)
        vx, vy = x2 - x1, y2 - y1
        norm = math.hypot(vx, vy) or 1.0
        nx, ny = -vy / norm, vx / norm
        # なめらか過ぎる直線を避けるため、ランダムだが小さめ
        amp = rng.uniform(-amp_m, amp_m)
        out.append(local_ll(origin, (nx * amp, ny * amp)))
    out.append(dense[-1])
    return out


def remove_near_duplicates(points: Sequence[LatLon], min_m: float = 1.0) -> List[LatLon]:
    out: List[LatLon] = []
    for p in points:
        if not out or haversine_m(out[-1], p) >= min_m:
            out.append(p)
    return out


# -----------------------------
# GeoJSON描画取り込み
# -----------------------------

def parse_drawn_features(raw: Dict[str, Any], default_kind: str) -> List[DrawArea]:
    areas: List[DrawArea] = []
    if not raw:
        return areas
    features = raw.get("all_drawings") or raw.get("features") or []
    for idx, f in enumerate(features):
        geom = f.get("geometry") or {}
        props = f.get("properties") or {}
        kind = props.get("kind") or props.get("type") or default_kind
        name = props.get("name") or f"area_{idx+1}"
        gtype = geom.get("type")
        coords = geom.get("coordinates")
        pts: List[LatLon] = []
        if gtype == "Polygon" and coords:
            ring = coords[0]
            pts = [(float(lat), float(lon)) for lon, lat in ring]
        elif gtype == "LineString" and coords:
            pts = [(float(lat), float(lon)) for lon, lat in coords]
            kind = "move"
        if pts:
            areas.append(DrawArea(name=name, kind=kind, coords=pts))
    return areas


def polygon_bounds(coords: Sequence[LatLon]) -> Tuple[float, float, float, float]:
    lats = [p[0] for p in coords]
    lons = [p[1] for p in coords]
    return min(lats), min(lons), max(lats), max(lons)


def centroid(coords: Sequence[LatLon]) -> LatLon:
    if not coords:
        return (35.681236, 139.767125)
    return (sum(p[0] for p in coords) / len(coords), sum(p[1] for p in coords) / len(coords))


# -----------------------------
# 通常エリア: OSM道路データ優先の道路沿いぐにゃぐにゃ
# -----------------------------

# v126: 道路を取れなかった時に横線で塗るフォールバックは禁止。
# あの横線は「地図データを読まずに作った偽ルート」なので、今後は出さない。
OSM_EXCLUDE_ROAD_TYPES = {
    "motorway", "motorway_link", "trunk", "trunk_link", "raceway", "proposed", "construction"
}


def _is_usable_road(tags: Dict[str, Any]) -> bool:
    hw = str(tags.get("highway", "")).strip()
    if not hw or hw in OSM_EXCLUDE_ROAD_TYPES:
        return False
    if tags.get("access") in {"private", "no"}:
        # 団地内通路がprivate扱いの場合もあるが、外部道路としては使わない
        return False
    if tags.get("area") == "yes":
        return False
    return True


def _poly_to_shapely(poly: Sequence[LatLon]):
    if Polygon is None or len(poly) < 3:
        return None
    try:
        return Polygon([(lon, lat) for lat, lon in poly]).buffer(0)
    except Exception:
        return None


@st.cache_data(show_spinner=False, ttl=60 * 60 * 12)
def overpass_roads_in_bbox_cached(minlat: float, minlon: float, maxlat: float, maxlon: float) -> List[List[LatLon]]:
    """bbox内のOSM道路中心線を取得。複数エンドポイントを試す。"""
    if requests is None:
        return []
    q = f"""
    [out:json][timeout:35];
    (
      way["highway"]({minlat},{minlon},{maxlat},{maxlon});
    );
    out tags geom;
    """
    endpoints = [
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://overpass.openstreetmap.ru/api/interpreter",
    ]
    data = None
    for url in endpoints:
        try:
            r = requests.post(url, data={"data": q}, timeout=45, headers={"User-Agent": "posting-route-builder-v126/1.0"})
            r.raise_for_status()
            data = r.json()
            break
        except Exception:
            data = None
            continue
    if not data:
        return []
    lines: List[List[LatLon]] = []
    for el in data.get("elements", []):
        tags = el.get("tags") or {}
        if not _is_usable_road(tags):
            continue
        geom = el.get("geometry") or []
        pts = [(float(g["lat"]), float(g["lon"])) for g in geom if "lat" in g and "lon" in g]
        if len(pts) >= 2:
            lines.append(pts)
    return lines


def _bbox_expand(bounds: Tuple[float, float, float, float], meter: float = 80.0) -> Tuple[float, float, float, float]:
    minlat, minlon, maxlat, maxlon = bounds
    c = ((minlat + maxlat) / 2, (minlon + maxlon) / 2)
    dlat = meter / EARTH_R * 180 / math.pi
    dlon = meter / (EARTH_R * max(0.2, math.cos(math.radians(c[0])))) * 180 / math.pi
    return minlat - dlat, minlon - dlon, maxlat + dlat, maxlon + dlon


def combine_bounds(polys: Sequence[Sequence[LatLon]], expand_m: float = 120.0) -> Tuple[float, float, float, float]:
    vals = [polygon_bounds(p) for p in polys if len(p) >= 3]
    minlat = min(v[0] for v in vals); minlon = min(v[1] for v in vals)
    maxlat = max(v[2] for v in vals); maxlon = max(v[3] for v in vals)
    return _bbox_expand((minlat, minlon, maxlat, maxlon), expand_m)


def road_segments_inside_polygon(poly: Sequence[LatLon], coverage: float, seed: int, roads: Optional[List[List[LatLon]]] = None) -> List[List[LatLon]]:
    """町丁目ポリゴン内を通る道路セグメントだけを抽出。"""
    shp = _poly_to_shapely(poly)
    if shp is None:
        return []
    if roads is None:
        minlat, minlon, maxlat, maxlon = _bbox_expand(polygon_bounds(poly), 90)
        roads = overpass_roads_in_bbox_cached(round(minlat, 6), round(minlon, 6), round(maxlat, 6), round(maxlon, 6))
    segments: List[List[LatLon]] = []
    for road in roads:
        dense = densify(road, step_m=8.0)
        cur: List[LatLon] = []
        for pt in dense:
            try:
                point = Point(pt[1], pt[0])
                inside = shp.contains(point) or shp.touches(point) or shp.buffer(0.000008).contains(point)
            except Exception:
                inside = False
            if inside:
                cur.append(pt)
            else:
                if len(cur) >= 2 and total_distance_m(cur) >= 12:
                    segments.append(cur)
                cur = []
        if len(cur) >= 2 and total_distance_m(cur) >= 12:
            segments.append(cur)
    uniq = []
    seen = set()
    for seg in segments:
        a, b = seg[0], seg[-1]
        key = (round(a[0], 5), round(a[1], 5), round(b[0], 5), round(b[1], 5))
        rkey = (key[2], key[3], key[0], key[1])
        if key in seen or rkey in seen:
            continue
        seen.add(key)
        uniq.append(seg)
    rng = random.Random(seed)
    uniq.sort(key=lambda s: total_distance_m(s), reverse=True)
    if coverage < 99 and uniq:
        keep_n = max(1, int(len(uniq) * max(0.05, coverage / 100.0)))
        # 長い道路だけに偏ると不自然なので、上位を少し残して残りはランダム
        head_n = max(1, keep_n // 3)
        head = uniq[:head_n]
        tail = uniq[head_n:]
        rng.shuffle(tail)
        uniq = head + tail[: max(0, keep_n - len(head))]
    return uniq


def _build_road_graph(segments: Sequence[Sequence[LatLon]]) -> Tuple[Dict[Tuple[int, int], LatLon], Dict[Tuple[int, int], List[Tuple[Tuple[int, int], float]]]]:
    nodes: Dict[Tuple[int, int], LatLon] = {}
    graph: Dict[Tuple[int, int], List[Tuple[Tuple[int, int], float]]] = {}
    def key(p: LatLon) -> Tuple[int, int]:
        return (int(round(p[0] * 1e6)), int(round(p[1] * 1e6)))
    for seg in segments:
        dense = densify(seg, step_m=10.0)
        for a, b in zip(dense[:-1], dense[1:]):
            ka, kb = key(a), key(b)
            nodes.setdefault(ka, a); nodes.setdefault(kb, b)
            w = haversine_m(a, b)
            if w <= 45.0:  # 異常な長辺を道路グラフに入れない
                graph.setdefault(ka, []).append((kb, w))
                graph.setdefault(kb, []).append((ka, w))
    return nodes, graph


def _nearest_node(nodes: Dict[Tuple[int, int], LatLon], p: LatLon) -> Optional[Tuple[int, int]]:
    if not nodes:
        return None
    return min(nodes.keys(), key=lambda k: haversine_m(nodes[k], p))


def _shortest_path_nodes(graph: Dict[Any, List[Tuple[Any, float]]], start, goal, max_expand: int = 8000) -> Optional[List[Any]]:
    import heapq
    if start is None or goal is None:
        return None
    if start == goal:
        return [start]
    pq = [(0.0, start)]
    prev = {start: None}
    dist = {start: 0.0}
    expanded = 0
    while pq and expanded < max_expand:
        d, u = heapq.heappop(pq)
        if u == goal:
            path = []
            cur = goal
            while cur is not None:
                path.append(cur)
                cur = prev[cur]
            return list(reversed(path))
        if d != dist.get(u):
            continue
        expanded += 1
        for v, w in graph.get(u, []):
            nd = d + w
            if nd < dist.get(v, 1e18):
                dist[v] = nd; prev[v] = u; heapq.heappush(pq, (nd, v))
    return None


def _road_path_between(points_graph, a: LatLon, b: LatLon, seed: int, max_snap_m: float = 55.0, max_path_m: float = 1200.0) -> List[LatLon]:
    """道路グラフ上でa→bを接続。取れない時は直線フォールバックしない。"""
    nodes, graph = points_graph
    sa = _nearest_node(nodes, a); sb = _nearest_node(nodes, b)
    if sa is None or sb is None:
        return []
    if haversine_m(nodes[sa], a) > max_snap_m or haversine_m(nodes[sb], b) > max_snap_m:
        return []
    path = _shortest_path_nodes(graph, sa, sb)
    if path and len(path) >= 2:
        pts = [nodes[k] for k in path]
        if total_distance_m(pts) <= max_path_m:
            return wiggle_polyline(pts, amp_m=0.65, every_m=8.0, seed=seed)
    return []


def order_road_segments_as_route(segments: List[List[LatLon]], seed: int, connector_graph=None) -> Tuple[List[LatLon], List[str]]:
    """道路セグメントを近い順に道路グラフで接続。道路接続できないものは飛ばさずスキップ。"""
    logs: List[str] = []
    if not segments:
        return [], logs
    graph_pack = connector_graph or _build_road_graph(segments)
    unused = [list(s) for s in segments if len(s) >= 2]
    if not unused:
        return [], logs
    start_i = min(range(len(unused)), key=lambda i: (unused[i][0][0], unused[i][0][1]))
    route = list(unused.pop(start_i))
    skipped = 0
    while unused:
        last = route[-1]
        best = None
        # 近すぎる道路を優先。遠い道路へは飛ばない。
        for i, seg in enumerate(unused):
            for rev, endpoint in [(False, seg[0]), (True, seg[-1])]:
                direct = haversine_m(last, endpoint)
                if best is None or direct < best[0]:
                    best = (direct, i, rev)
        if best is None:
            break
        direct, idx, rev = best
        seg = unused.pop(idx)
        if rev:
            seg = list(reversed(seg))
        conn = _road_path_between(graph_pack, route[-1], seg[0], seed=seed + len(route))
        if conn:
            route.extend(conn[1:])
            route.extend(seg[1:])
        elif direct <= 22.0:
            # 交差点の丸め誤差程度だけは短く接続
            tiny = densify([route[-1], seg[0]], step_m=6.0)
            route.extend(tiny[1:]); route.extend(seg[1:])
        else:
            skipped += 1
            # 飛ばすくらいなら使わない。ジャンプ優先で禁止。
            continue
    if skipped:
        logs.append(f"道路接続できない道路片を{skipped}本スキップしました（ジャンプ防止）。")
    return remove_near_duplicates(route, min_m=0.8), logs


def fallback_scan_route(poly: Sequence[LatLon], seed: int, density: float = 1.0) -> List[LatLon]:
    # v126: 横線塗りフォールバックは禁止。道路データが無ければ生成しない。
    return []


def generate_normal_area_route(poly: Sequence[LatLon], seed: int, density: float = 1.0, coverage_pct: int = 70, roads: Optional[List[List[LatLon]]] = None, connector_graph=None) -> Tuple[List[LatLon], List[str]]:
    # 通常エリアはOSM道路中心線だけを使う。畑/境界外の単純横走査はしない。
    logs: List[str] = []
    segments = road_segments_inside_polygon(poly, coverage=float(coverage_pct), seed=seed, roads=roads)
    if not segments:
        logs.append("この配布範囲内でOSM道路中心線を取得できませんでした。横線の偽ルートは作らず停止します。")
        return [], logs
    route, rlogs = order_road_segments_as_route(segments, seed=seed, connector_graph=connector_graph)
    logs.extend(rlogs)
    if route:
        route = wiggle_polyline(route, amp_m=0.75 * max(0.7, density), every_m=8.0, seed=seed + 333)
    return route, logs

# -----------------------------
# 団地枠: OSM建物取得 + 枝道化
# -----------------------------

def overpass_buildings_in_bbox(minlat: float, minlon: float, maxlat: float, maxlon: float, timeout: int = 25) -> List[List[LatLon]]:
    if requests is None:
        raise RuntimeError("requests がありません。pip install requests を実行してください。")
    # Overpass API。失敗時は空で返す。
    q = f"""
    [out:json][timeout:{timeout}];
    (
      way["building"]({minlat},{minlon},{maxlat},{maxlon});
    );
    out body geom;
    """
    url = "https://overpass-api.de/api/interpreter"
    r = requests.post(url, data={"data": q}, timeout=timeout + 10)
    r.raise_for_status()
    data = r.json()
    buildings: List[List[LatLon]] = []
    for el in data.get("elements", []):
        geom = el.get("geometry") or []
        pts = [(float(p["lat"]), float(p["lon"])) for p in geom if "lat" in p and "lon" in p]
        if len(pts) >= 4:
            buildings.append(pts)
    return buildings


def simplify_building_rect(building: Sequence[LatLon]) -> Tuple[LatLon, LatLon, LatLon, LatLon, LatLon]:
    """建物をbbox矩形として扱う。戻り: center, north, south, east, west"""
    minlat, minlon, maxlat, maxlon = polygon_bounds(building)
    c = ((minlat + maxlat) / 2, (minlon + maxlon) / 2)
    n = (maxlat, c[1])
    s = (minlat, c[1])
    e = (c[0], maxlon)
    w = (c[0], minlon)
    return c, n, s, e, w


def building_size_m(building: Sequence[LatLon]) -> Tuple[float, float, float]:
    minlat, minlon, maxlat, maxlon = polygon_bounds(building)
    h = haversine_m((minlat, minlon), (maxlat, minlon))
    w = haversine_m((minlat, minlon), (minlat, maxlon))
    return h, w, h * w


def filter_danchi_buildings(buildings: Sequence[Sequence[LatLon]]) -> List[List[LatLon]]:
    """小さい戸建てっぽい建物を除き、団地の棟っぽいものを残す。"""
    kept: List[List[LatLon]] = []
    for b in buildings:
        h, w, area = building_size_m(b)
        long_side = max(h, w)
        short_side = min(h, w)
        # 団地棟は細長い/大きい傾向。小型戸建ては落とす。
        if area >= 180 or long_side >= 22 or (long_side >= 16 and short_side >= 7):
            kept.append(list(b))
    return kept


def generate_danchi_spur_from_buildings(buildings: Sequence[Sequence[LatLon]], seed: int) -> List[LatLon]:
    """団地枠内だけの巡回線。建物そのものではなく、棟の入口側/長辺側を枝道風に回る。"""
    if not buildings:
        return []
    rng = random.Random(seed)
    centers = []
    for b in buildings:
        c, n, s, e, w = simplify_building_rect(b)
        h, ww, area = building_size_m(b)
        centers.append((c, b, h, ww, area))
    # 上下または左右に並ぶ棟を、座標順でスネーク。ジャンプを減らすため最近傍順も併用。
    start_idx = min(range(len(centers)), key=lambda i: (centers[i][0][0], centers[i][0][1]))
    used = {start_idx}
    order = [start_idx]
    while len(order) < len(centers):
        last_c = centers[order[-1]][0]
        candidates = [i for i in range(len(centers)) if i not in used]
        nxt = min(candidates, key=lambda i: haversine_m(last_c, centers[i][0]))
        used.add(nxt)
        order.append(nxt)
    route: List[LatLon] = []
    for k, idx in enumerate(order):
        c, b, h, ww, area = centers[idx]
        minlat, minlon, maxlat, maxlon = polygon_bounds(b)
        # 建物周辺を半周〜一周弱。長方形の外側をなぞるが、少し外へ逃がす。
        pad_lat = (maxlat - minlat) * 0.18 + 0.000015
        pad_lon = (maxlon - minlon) * 0.18 + 0.000015
        loop = [
            (minlat - pad_lat, minlon - pad_lon),
            (minlat - pad_lat, maxlon + pad_lon),
            (maxlat + pad_lat, maxlon + pad_lon),
            (maxlat + pad_lat, minlon - pad_lon),
            (minlat - pad_lat, minlon - pad_lon),
        ]
        # 反復感を減らす
        if k % 2:
            loop = list(reversed(loop))
        loop = wiggle_polyline(loop, amp_m=2.0, every_m=8.0, seed=seed + idx * 23)
        if route:
            # 棟間は直接斜め長距離にしない。短い場合だけL字、長すぎる場合はそこで打ち切り気味にする。
            if haversine_m(route[-1], loop[0]) <= 80:
                mid = (route[-1][0], loop[0][1])
                connector = wiggle_polyline([route[-1], mid, loop[0]], amp_m=1.5, every_m=8.0, seed=seed + idx * 31)
                route.extend(connector[1:])
            else:
                # 離れすぎた棟は飛ばない。別島として扱わず、今回はスキップしてジャンプを防ぐ。
                continue
        route.extend(loop if not route else loop[1:])
    return remove_near_duplicates(route)


def nearest_index(route: Sequence[LatLon], p: LatLon) -> int:
    return min(range(len(route)), key=lambda i: haversine_m(route[i], p)) if route else 0


def attach_spur_to_main_without_jump(main: List[LatLon], spur: List[LatLon], max_attach_m: float = 120.0) -> Tuple[List[LatLon], str]:
    """団地ルートをメインルートに枝道として挿入する。離れていたら挿入しない。"""
    if not spur:
        return main, "団地枝道なし"
    if not main:
        return spur, "メインがないため団地単独ルート"
    # spur内の入口候補をmainの最近点に合わせる
    best = None
    for si, sp in enumerate(spur):
        mi = nearest_index(main, sp)
        d = haversine_m(main[mi], sp)
        if best is None or d < best[0]:
            best = (d, mi, si)
    assert best is not None
    d, mi, si = best
    if d > max_attach_m:
        return main, f"団地枠はメインから{d:.1f}m離れているため自動接続しません"
    # spurを入口から始めて一周し、入口へ戻る枝道にする
    rotated = list(spur[si:]) + list(spur[:si + 1])
    entry = main[mi]
    # 入る/戻るは短距離だけL字密化。ここが長ければ接続禁止済み。
    in_conn = wiggle_polyline([entry, rotated[0]], amp_m=1.5, every_m=6.0, seed=mi + si + 1000)
    out_conn = wiggle_polyline([rotated[-1], entry], amp_m=1.5, every_m=6.0, seed=mi + si + 2000)
    inserted = main[: mi + 1] + in_conn[1:] + rotated[1:] + out_conn[1:] + main[mi + 1 :]
    return remove_near_duplicates(inserted), f"団地枝道をメインルート{mi}番付近へ挿入（接続距離 {d:.1f}m）"


# -----------------------------
# 移動線: ユーザーが描いた線だけ使う
# -----------------------------

def generate_move_line(line: Sequence[LatLon], seed: int) -> List[LatLon]:
    return wiggle_polyline(line, amp_m=1.2, every_m=12.0, seed=seed)


def assemble_routes_no_auto_stitch(normal_routes: List[List[LatLon]], move_routes: List[List[LatLon]]) -> Tuple[List[List[LatLon]], List[str]]:
    """離れた通常エリアを勝手に接続しない。移動線は独立セグメントとして残す。"""
    logs: List[str] = []
    segments: List[List[LatLon]] = []
    for r in normal_routes:
        if len(r) >= 2:
            segments.append(r)
    for m in move_routes:
        if len(m) >= 2:
            segments.append(m)
            logs.append("ユーザー指定の移動線を追加しました")
    if len(segments) > 1:
        logs.append("複数セグメントです。自動直線接続はしていません。必要なら移動線を描いてください。")
    return segments, logs


# -----------------------------
# GPX出力
# -----------------------------

def make_gpx(segments: Sequence[Sequence[LatLon]], start_time: _dt.datetime, speed_kmh: float, stop_total_min: float = 0.0) -> str:
    gpx = ET.Element("gpx", version="1.1", creator="ChatGPT v118 pre_pin_required_points_route_builder", xmlns="http://www.topografix.com/GPX/1/1")
    trk = ET.SubElement(gpx, "trk")
    ET.SubElement(trk, "name").text = "posting_route_v126"
    current = start_time
    speed_mps = max(speed_kmh / 3.6, 0.3)
    # 停止時間は大きなジャンプではなく、既存点に時間だけ足す。
    stop_pool_sec = max(0.0, stop_total_min * 60.0)
    stops_remaining = int(stop_pool_sec // 90) if stop_pool_sec else 0
    rng = random.Random(116)
    for seg in segments:
        if len(seg) < 2:
            continue
        trkseg = ET.SubElement(trk, "trkseg")
        prev: Optional[LatLon] = None
        for p in seg:
            if prev is not None:
                current += _dt.timedelta(seconds=haversine_m(prev, p) / speed_mps)
                if stops_remaining > 0 and rng.random() < 0.015:
                    add = rng.uniform(45, 180)
                    current += _dt.timedelta(seconds=add)
                    stops_remaining -= 1
            trkpt = ET.SubElement(trkseg, "trkpt", lat=f"{p[0]:.8f}", lon=f"{p[1]:.8f}")
            ET.SubElement(trkpt, "ele").text = "3.0"
            ET.SubElement(trkpt, "time").text = format_gpx_time(current)
            prev = p
    return ET.tostring(gpx, encoding="utf-8", xml_declaration=True).decode("utf-8")


def max_step_m(segments: Sequence[Sequence[LatLon]]) -> float:
    mx = 0.0
    for seg in segments:
        for a, b in zip(seg[:-1], seg[1:]):
            mx = max(mx, haversine_m(a, b))
    return mx



# -----------------------------
# ローカル町丁目境界検索（前回方式の復旧）
# -----------------------------

def _polygon_to_latlon_ring(poly) -> List[LatLon]:
    try:
        coords = list(poly.exterior.coords)
        return [(float(y), float(x)) for x, y in coords]
    except Exception:
        return []


def _geom_to_latlon_lines(geom) -> List[List[LatLon]]:
    if geom is None:
        return []
    try:
        gtype = getattr(geom, "geom_type", "")
        if gtype == "Polygon":
            line = _polygon_to_latlon_ring(geom)
            return [line] if len(line) >= 3 else []
        if gtype == "MultiPolygon":
            out = []
            for poly in list(getattr(geom, "geoms", [])):
                line = _polygon_to_latlon_ring(poly)
                if len(line) >= 3:
                    out.append(line)
            return out
    except Exception:
        pass
    return []


def _local_boundary_paths() -> List[Path]:
    """ユーザーPCの従来 data/kanto_boundaries.geojson を優先して探す。"""
    base = Path(__file__).resolve().parent
    cwd = Path.cwd()
    return [
        cwd / "data" / "kanto_boundaries.geojson",
        base / "data" / "kanto_boundaries.geojson",
        cwd / "kanto_boundaries.geojson",
        base / "kanto_boundaries.geojson",
    ]


def _get_prop_any(props: Dict[str, Any], keys: Sequence[str], default: str = "") -> str:
    for k in keys:
        if k in props and props[k] not in (None, ""):
            return str(props[k]).strip()
    # 大文字小文字ゆれ
    low = {str(k).lower(): k for k in props.keys()}
    for k in keys:
        kk = low.get(str(k).lower())
        if kk is not None and props.get(kk) not in (None, ""):
            return str(props.get(kk)).strip()
    return default


@st.cache_resource(show_spinner="ローカル町丁目境界データを読み込み中...")
def load_local_boundary_candidates_v126() -> List[Dict[str, Any]]:
    """前回システムと同じ data/kanto_boundaries.geojson を使った丁目検索。

    Nominatimのboundingbox矩形は使わず、ローカルGeoJSONの正確な町丁目ポリゴンを候補化します。
    """
    if shape is None:
        return []
    path = None
    for cand in _local_boundary_paths():
        if cand.exists():
            path = cand
            break
    if path is None:
        return []

    data = json.loads(path.read_text(encoding="utf-8"))
    features = data.get("features", []) or []
    props_list = [f.get("properties", {}) or {} for f in features]

    pref_keys = ["PREF_NAME", "pref_name", "都道府県名", "PREF", "N03_001", "都道府県"]
    city_keys = ["CITY_NAME", "city_name", "市区町村名", "CITY", "city", "N03_004", "行政区名", "市区町村"]
    name_keys = [
        "S_NAME", "s_name", "町丁目名", "町字名", "大字町丁目名", "町名", "丁目名",
        "MOJI", "moji", "NAME", "name", "TOWN_NAME", "town_name", "N03_005", "KEY_CODE_NAME"
    ]

    # 町丁目名フィールドを自動推定。丁目を多く含むキーを優先。
    best_key = None
    best_score = -1
    for k in name_keys:
        nonempty = 0
        chome = 0
        for props in props_list[:3000]:
            v = _get_prop_any(props, [k], "")
            if v:
                nonempty += 1
                if "丁目" in v or re.search(r"[一二三四五六七八九十0-9]+丁", v):
                    chome += 1
        score = chome * 20 + nonempty
        if score > best_score:
            best_key = k
            best_score = score

    records: List[Dict[str, Any]] = []
    for i, f in enumerate(features):
        props = f.get("properties", {}) or {}
        town = _get_prop_any(props, [best_key] + name_keys, "")
        if not town:
            continue
        pref = _get_prop_any(props, pref_keys, "")
        city = _get_prop_any(props, city_keys, "")
        if not city:
            # source_file などから市区町村が入っている古いデータ対策
            city = _get_prop_any(props, ["source_file", "file", "city_file"], "")
        try:
            geom = shape(f.get("geometry"))
            lines = _geom_to_latlon_lines(geom)
            if not lines:
                continue
            c = geom.centroid
            lat, lon = float(c.y), float(c.x)
        except Exception:
            continue
        display = " / ".join([x for x in [pref, city, town] if x]) + f"  [{i}]"
        records.append({
            "source": "local_boundary",
            "display_name": display,
            "short_name": town,
            "pref": pref,
            "city": city,
            "lat": lat,
            "lon": lon,
            "latlon_lines": lines,
            "precise": True,
            "raw_index": i,
        })

    def sort_key(r: Dict[str, Any]):
        return (r.get("pref", ""), r.get("city", ""), _natural_town_key(r.get("short_name", "")), r.get("display_name", ""))
    records.sort(key=sort_key)
    return records


def _normalize_jp(s: str) -> str:
    return re.sub(r"[\s　/／,，、・･\-ー_]+", "", str(s or ""))


def _kanji_num_to_int(s: str) -> int:
    table = {"一": 1, "二": 2, "三": 3, "四": 4, "五": 5, "六": 6, "七": 7, "八": 8, "九": 9, "十": 10}
    s = str(s)
    if s.isdigit():
        return int(s)
    if s == "十":
        return 10
    if s.startswith("十"):
        return 10 + table.get(s[1:], 0)
    if "十" in s:
        a, b = s.split("十", 1)
        return table.get(a, 0) * 10 + table.get(b, 0)
    return table.get(s, 999)


def _natural_town_key(name: str):
    s = str(name or "")
    m = re.search(r"(.+?)([0-9一二三四五六七八九十]+)丁目", s)
    if m:
        return (m.group(1), _kanji_num_to_int(m.group(2)))
    return (s, 999)


def _strip_pref_city_from_query(q: str, records: Sequence[Dict[str, Any]]) -> Tuple[str, str, str]:
    """queryから pref/city/town をざっくり分離。市だけならtownは空にする。"""
    nq = _normalize_jp(q)
    pref = ""
    city = ""
    # 入力に含まれる最長の市区町村名を採用
    cities = sorted({r.get("city", "") for r in records if r.get("city")}, key=len, reverse=True)
    for c in cities:
        if c and _normalize_jp(c) in nq:
            city = c
            nq = nq.replace(_normalize_jp(c), "")
            break
    prefs = sorted({r.get("pref", "") for r in records if r.get("pref")}, key=len, reverse=True)
    for p in prefs:
        if p and _normalize_jp(p) in nq:
            pref = p
            nq = nq.replace(_normalize_jp(p), "")
            break
    # 県名だけ残る場合を軽く除去
    nq = re.sub(r"^(東京都|千葉県|埼玉県|神奈川県|茨城県|栃木県|群馬県)", "", nq)
    return pref, city, nq


def local_boundary_search_candidates_v126(query: str, limit: int = 250) -> List[Dict[str, Any]]:
    records = load_local_boundary_candidates_v126()
    if not records:
        return []
    pref, city, town_q = _strip_pref_city_from_query(query, records)
    nq_full = _normalize_jp(query)
    town_q_norm = _normalize_jp(town_q)

    out = []
    for r in records:
        pref_r = r.get("pref", "")
        city_r = r.get("city", "")
        town_r = r.get("short_name", "")
        full = _normalize_jp(f"{pref_r}{city_r}{town_r}{r.get('display_name','')}")
        if pref and pref != pref_r:
            continue
        if city and city != city_r:
            continue
        if town_q_norm:
            if town_q_norm not in _normalize_jp(town_r) and town_q_norm not in full:
                continue
        else:
            # 市区町村だけの検索なら、その市区町村内の町丁目を全部出す
            if not city and nq_full not in full:
                continue
        out.append(r)

    # 市だけ検索で多すぎる場合も、あいうえお順・丁目順で見られるようにそのまま返す
    out.sort(key=lambda r: (r.get("pref", ""), r.get("city", ""), _natural_town_key(r.get("short_name", ""))))
    return out[:limit]

# -----------------------------
# 検索・境界取得
# -----------------------------

def _nominatim_get(query: str, limit: int = 10) -> List[Dict[str, Any]]:
    """Nominatim検索。複数候補を返す。"""
    if requests is None:
        raise RuntimeError("requests がありません。pip install requests を実行してください。")
    q = (query or "").strip()
    if not q:
        raise ValueError("検索語が空です")
    url = "https://nominatim.openstreetmap.org/search"
    params = {
        "q": q,
        "format": "jsonv2",
        "limit": int(limit),
        "countrycodes": "jp",
        "addressdetails": 1,
        "polygon_geojson": 1,
    }
    headers = {"User-Agent": "posting-route-builder-v126/1.0"}
    r = requests.get(url, params=params, headers=headers, timeout=25)
    r.raise_for_status()
    return r.json() or []


def _dedupe_places(items: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    seen = set()
    out = []
    for x in items:
        key = (x.get("osm_type"), x.get("osm_id"))
        if not key[0] or not key[1]:
            key = (round(float(x.get("lat", 0)), 6), round(float(x.get("lon", 0)), 6), x.get("display_name", "")[:40])
        if key in seen:
            continue
        seen.add(key)
        out.append(x)
    return out


def _has_polygon_geojson(place: Dict[str, Any]) -> bool:
    if place.get("latlon_lines"):
        return True
    if place.get("precise") is True:
        return True
    gj = place.get("geojson") or {}
    return gj.get("type") in ("Polygon", "MultiPolygon")


def _bbox_to_poly(place: Dict[str, Any]) -> List[LatLon]:
    """境界が取れない時の最低限の矩形表示。精密境界ではない。"""
    bb = place.get("boundingbox") or []
    if len(bb) != 4:
        return []
    minlat, maxlat, minlon, maxlon = map(float, bb)
    return [(minlat, minlon), (minlat, maxlon), (maxlat, maxlon), (maxlat, minlon), (minlat, minlon)]


def place_to_latlon_polylines(place: Dict[str, Any], allow_bbox: bool = True) -> List[List[LatLon]]:
    # ローカル境界データは正確な町丁目ポリゴンをlat/lonで保持している
    if place.get("latlon_lines"):
        return place.get("latlon_lines") or []
    lines = geojson_to_latlon_polylines(place.get("geojson") or {})
    if lines:
        return lines
    if allow_bbox:
        poly = _bbox_to_poly(place)
        if poly:
            return [poly]
    return []


def smart_search_place_candidates(query: str) -> List[Dict[str, Any]]:
    """町名検索の候補一覧を作る。

    v126: まず前回システムと同じローカル町丁目境界データを使う。
    これにより「我孫子市」→市内町丁目一覧、「我孫子市湖北台」→湖北台○丁目一覧を返す。
    ローカル境界が無い場合だけNominatimへフォールバックする。
    """
    q = (query or "").strip()
    if not q:
        raise ValueError("検索語が空です")

    local_items = local_boundary_search_candidates_v126(q, limit=300)
    if local_items:
        return local_items

    all_items: List[Dict[str, Any]] = []
    all_items.extend(_nominatim_get(q, limit=12))

    chome_words = ["一", "二", "三", "四", "五", "六", "七", "八", "九", "十", "十一", "十二"]
    if "丁目" not in q and not re.search(r"\d+\s*丁目", q):
        for i, k in enumerate(chome_words, start=1):
            variants = [f"{q}{i}丁目", f"{q}{k}丁目"]
            for v in variants:
                try:
                    all_items.extend(_nominatim_get(v, limit=2))
                    time.sleep(0.05)
                except Exception:
                    pass

    items = _dedupe_places(all_items)
    def score(x: Dict[str, Any]) -> Tuple[int, int, int]:
        disp = x.get("display_name", "")
        cls = x.get("class", "")
        typ = x.get("type", "")
        has_poly = 1 if _has_polygon_geojson(x) else 0
        has_chome = 1 if "丁目" in disp else 0
        residentialish = 1 if cls in ("boundary", "place") or typ in ("administrative", "quarter", "neighbourhood", "suburb") else 0
        return (-has_poly, -has_chome, -residentialish)
    items.sort(key=score)
    return items[:30]


def short_place_name(place: Dict[str, Any]) -> str:
    """画面で見やすい短い候補名。長い「千葉県/我孫子市/...」は出さない。"""
    if place.get("source") == "local_boundary":
        town = place.get("short_name") or place.get("display_name", "名称不明")
        return str(town)
    disp = str(place.get("display_name", "名称不明"))
    # Nominatim系だけは長い住所を末尾から短くする
    parts = [x.strip() for x in disp.split(",") if x.strip()]
    return " / ".join(parts[:2]) if len(parts) <= 2 else " / ".join(parts[:3])


def place_label(place: Dict[str, Any], idx: int) -> str:
    name = short_place_name(place)
    if place.get("source") == "local_boundary":
        raw = place.get("raw_index", idx)
        return f"{idx+1}. {name} [{raw}]"
    return f"{idx+1}. {name}"


def geojson_to_latlon_polylines(gj: Dict[str, Any]) -> List[List[LatLon]]:
    """Nominatim polygon_geojson を folium 用 lat,lon 列へ変換。"""
    if not gj:
        return []
    out: List[List[LatLon]] = []
    typ = gj.get("type")
    coords = gj.get("coordinates")
    if typ == "Polygon":
        for ring in coords[:1]:
            out.append([(float(lat), float(lon)) for lon, lat in ring])
    elif typ == "MultiPolygon":
        for poly in coords:
            if poly:
                ring = poly[0]
                out.append([(float(lat), float(lon)) for lon, lat in ring])
    return out


def map_center_from_state(default: LatLon) -> LatLon:
    c = st.session_state.get("map_center")
    if isinstance(c, (list, tuple)) and len(c) == 2:
        return (float(c[0]), float(c[1]))
    return default


def parse_one_feature_to_area(feature: Dict[str, Any], kind: str, name: str) -> Optional[DrawArea]:
    geom = feature.get("geometry") or {}
    gtype = geom.get("type")
    coords = geom.get("coordinates")
    pts: List[LatLon] = []
    if gtype == "Polygon" and coords:
        pts = [(float(lat), float(lon)) for lon, lat in coords[0]]
    elif gtype == "LineString" and coords:
        pts = [(float(lat), float(lon)) for lon, lat in coords]
        kind = "move"
    if not pts:
        return None
    return DrawArea(name=name, kind=kind, coords=pts)


# -----------------------------
# v118: 通過ピン先指定ルート生成
# -----------------------------

def parse_marker_feature_to_point(feature: Dict[str, Any]) -> Optional[LatLon]:
    geom = feature.get("geometry") or {}
    if geom.get("type") != "Point":
        return None
    coords = geom.get("coordinates") or []
    if len(coords) < 2:
        return None
    lon, lat = coords[:2]
    return (float(lat), float(lon))


def boundary_polygon_for_generation() -> List[List[LatLon]]:
    """登録済み境界があればそれを、なければ現在表示中の検索境界を配布範囲として使う。"""
    polys = st.session_state.get("route_boundaries_v118", []) or []
    out: List[List[LatLon]] = []
    for item in polys:
        coords = item.get("coords") if isinstance(item, dict) else item
        if coords and len(coords) >= 3:
            out.append(list(coords))
    if out:
        return out
    return [list(p) for p in (st.session_state.get("boundary_lines", []) or []) if len(p) >= 3]


def weak_move_connector(a: LatLon, b: LatLon, seed: int, step_m: float = 14.0) -> List[LatLon]:
    """町丁目から町丁目への移動線。遠目にはほぼ直線、GPSブレは弱い。"""
    d = haversine_m(a, b)
    if d < 1:
        return [a, b]
    # 完全な一直線を避けるため、長距離だけ軽い中間点を作る
    if d >= 120:
        mid = lerp(a, b, 0.5)
        base = [a, mid, b]
    else:
        base = [a, b]
    return wiggle_polyline(base, amp_m=0.9, every_m=step_m, seed=seed)


def loop_around_pin(pin: LatLon, radius_m: float, seed: int) -> List[LatLon]:
    """通過ピン周辺で、団地/集合住宅へ寄った感じを出す小ループ。"""
    r = max(0.0, float(radius_m))
    if r <= 1:
        return [pin]
    rng = random.Random(seed)
    # 少し楕円にする
    rx = r * rng.uniform(0.75, 1.15)
    ry = r * rng.uniform(0.55, 0.95)
    angle = rng.uniform(0, math.pi)
    pts = []
    for k in range(7):
        th = 2 * math.pi * k / 6
        x = math.cos(th) * rx
        y = math.sin(th) * ry
        xr = x * math.cos(angle) - y * math.sin(angle)
        yr = x * math.sin(angle) + y * math.cos(angle)
        pts.append(local_ll(pin, (xr, yr)))
    return wiggle_polyline(pts, amp_m=0.8, every_m=6.0, seed=seed+19)


def spur_to_required_pin(entry: LatLon, pin: LatLon, seed: int, radius_m: float = 18.0) -> List[LatLon]:
    """通常ルート上の最寄り点からピンへ入り、ピン周辺を回り、同じ場所へ戻る。"""
    # entry→pinは「最寄り道路から団地へ出入り」の短い線として扱う
    d = haversine_m(entry, pin)
    if d > 80:
        # 長めの場合はL字寄りにして、斜めに見える直線を弱める
        mid1 = (entry[0], pin[1])
        # L字の角が遠すぎる場合は中点を挟む
        base = [entry, mid1, pin]
    else:
        base = [entry, pin]
    in_line = wiggle_polyline(base, amp_m=0.9, every_m=6.0, seed=seed)
    loop = loop_around_pin(pin, radius_m=radius_m, seed=seed+100)
    out_line = list(reversed(in_line))
    # entry -> pin -> loop -> pin -> entry
    route = []
    route.extend(in_line)
    if loop:
        route.extend(loop[1:] if route else loop)
    if out_line:
        route.extend(out_line[1:])
    return remove_near_duplicates(route, min_m=0.8)



def _pin_clusters_v128(pins: Sequence[LatLon], cluster_m: float = 95.0) -> List[List[Tuple[int, LatLon]]]:
    """近い通過ピンを団地・集合住宅の同一クラスタとしてまとめる。"""
    n = len(pins)
    if n == 0:
        return []
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra
    for i in range(n):
        for j in range(i + 1, n):
            if haversine_m(pins[i], pins[j]) <= cluster_m:
                union(i, j)
    groups: Dict[int, List[Tuple[int, LatLon]]] = {}
    for i, pin in enumerate(pins):
        groups.setdefault(find(i), []).append((i, pin))
    return list(groups.values())


def _sort_pins_snake_v128(items: List[Tuple[int, LatLon]]) -> List[Tuple[int, LatLon]]:
    """団地内のピンを、行き戻りが少なくなるように長軸方向で並べる。"""
    if len(items) <= 2:
        return items
    pts = [p for _, p in items]
    lat0 = sum(p[0] for p in pts) / len(pts)
    lon0 = sum(p[1] for p in pts) / len(pts)
    origin = (lat0, lon0)
    xy = [local_xy(origin, p) for p in pts]
    # 一番広がりが大きい方向を主軸にする
    minx, maxx = min(x for x, y in xy), max(x for x, y in xy)
    miny, maxy = min(y for x, y in xy), max(y for x, y in xy)
    if (maxx - minx) >= (maxy - miny):
        keyed = [(xy[i][0], xy[i][1], items[i]) for i in range(len(items))]
    else:
        keyed = [(xy[i][1], xy[i][0], items[i]) for i in range(len(items))]
    # 近い列ごとに軽く蛇行順にする
    keyed.sort(key=lambda t: (round(t[0] / 22.0), t[1]))
    out=[]
    current_bucket=None
    bucket=[]
    flip=False
    for a,b,item in keyed:
        bk=round(a/22.0)
        if current_bucket is None:
            current_bucket=bk
        if bk!=current_bucket:
            bucket.sort(key=lambda t:t[0], reverse=flip)
            out.extend([it for _,it in bucket])
            bucket=[]; current_bucket=bk; flip=not flip
        bucket.append((b,item))
    if bucket:
        bucket.sort(key=lambda t:t[0], reverse=flip)
        out.extend([it for _,it in bucket])
    return out


def _pin_chain_segment_v128(entry: LatLon, exitp: LatLon, ordered_pins: List[Tuple[int, LatLon]], seed: int, radius_m: float) -> List[LatLon]:
    """ピンを1個ずつ戻らず、団地内の連続訪問線としてつなぐ。"""
    if not ordered_pins:
        return [entry, exitp]
    pts: List[LatLon] = [entry]
    for k, (_idx, pin) in enumerate(ordered_pins):
        # ピン間は団地内通路として少しだけ揺らす。大きなループは作らない。
        if haversine_m(pts[-1], pin) > 0.8:
            pts.extend(wiggle_polyline([pts[-1], pin], amp_m=1.1, every_m=5.0, seed=seed + k * 101)[1:])
        r = max(2.0, min(float(radius_m), 14.0))
        # 各ピン周りは小さな寄り道。戻り線ではなく、そのまま次ピンへ進む。
        tiny = loop_around_pin(pin, radius_m=r * 0.45, seed=seed + k * 131 + 500)
        if len(tiny) > 1:
            pts.extend(tiny[1:])
    if haversine_m(pts[-1], exitp) > 0.8:
        pts.extend(wiggle_polyline([pts[-1], exitp], amp_m=1.0, every_m=5.0, seed=seed + 9090)[1:])
    return remove_near_duplicates(pts, 0.7)


def insert_required_pins_into_route(base_route: List[LatLon], pins: Sequence[LatLon], pin_radius_m: float, seed: int) -> Tuple[List[LatLon], List[str]]:
    """完成後編集ではなく、生成時に通過ピンを通常ルートへ挿入する。

    v128: 近いピン群は1本ずつ往復させず、団地内でピン同士を連続接続する。
    これで「1個行って戻る、1個行って戻る」の不自然さを消す。
    """
    logs: List[str] = []
    if not base_route or not pins:
        return base_route, logs
    clusters = _pin_clusters_v128(pins, cluster_m=95.0)
    cluster_infos=[]
    for ci, items in enumerate(clusters):
        indices=[nearest_index(base_route, pin) for _, pin in items]
        entry_i=min(indices)
        exit_i=max(indices)
        # 同じ場所に挿入される時も、出口を少し先にずらして線が潰れないようにする
        if exit_i <= entry_i and entry_i < len(base_route)-1:
            exit_i = min(len(base_route)-1, entry_i + 1)
        dmin=min(haversine_m(base_route[nearest_index(base_route, pin)], pin) for _, pin in items)
        cluster_infos.append((entry_i, exit_i, ci, items, dmin))
    # 後ろから挿入してindex崩れを防ぐ
    cluster_infos.sort(reverse=True, key=lambda x: x[0])
    route=list(base_route)
    for entry_i, exit_i, ci, items, dmin in cluster_infos:
        entry=route[min(entry_i, len(route)-1)]
        exitp=route[min(exit_i, len(route)-1)]
        ordered=_sort_pins_snake_v128(list(items))
        # 入口に近い端から開始する
        if len(ordered) >= 2:
            if haversine_m(entry, ordered[-1][1]) < haversine_m(entry, ordered[0][1]):
                ordered=list(reversed(ordered))
        seg=_pin_chain_segment_v128(entry, exitp, ordered, seed=seed+ci*1201, radius_m=pin_radius_m)
        if len(seg) < 2:
            logs.append(f"通過ピンクラスタ{ci+1}: 生成失敗")
            continue
        route = route[:entry_i+1] + seg[1:] + route[exit_i+1:]
        logs.append(f"通過ピンクラスタ{ci+1}: {len(items)}本を連続接続 / 最寄り道路 {dmin:.1f}m / 追加 {total_distance_m(seg):.1f}m")
    return remove_near_duplicates(route, min_m=0.8), logs





# ==================================================
# v135: 色別ピングループ・同色順番接続
# ==================================================
PIN_GROUP_COLORS_V129 = ["blue", "red", "green", "purple", "orange", "darkred", "cadetblue", "darkgreen", "pink", "black"]
PIN_GROUP_COLOR_HEX_V129 = {
    "blue":"#2563eb", "red":"#dc2626", "green":"#16a34a", "purple":"#7c3aed",
    "orange":"#ea580c", "darkred":"#7f1d1d", "cadetblue":"#0f766e", "darkgreen":"#166534",
    "pink":"#db2777", "black":"#111827",
}

def init_pin_groups_v135():
    if "pin_groups_v135" not in st.session_state:
        st.session_state.pin_groups_v135 = []
    if "active_pin_group_id_v135" not in st.session_state:
        st.session_state.active_pin_group_id_v135 = None
    if "pin_group_next_id_v135" not in st.session_state:
        st.session_state.pin_group_next_id_v135 = 1
    if "pin_group_mode_v135" not in st.session_state:
        st.session_state.pin_group_mode_v135 = False

def color_for_group_v135(gid:int)->str:
    return PIN_GROUP_COLORS_V129[(int(gid)-1) % len(PIN_GROUP_COLORS_V129)]

def active_group_v135():
    init_pin_groups_v135()
    gid = st.session_state.active_pin_group_id_v135
    for g in st.session_state.pin_groups_v135:
        if g.get("id") == gid:
            return g
    return None

def start_pin_group_v135():
    init_pin_groups_v135()
    gid = int(st.session_state.pin_group_next_id_v135)
    g = {"id": gid, "name": f"グループ{gid}", "color": color_for_group_v135(gid), "points": []}
    st.session_state.pin_groups_v135.append(g)
    st.session_state.active_pin_group_id_v135 = gid
    st.session_state.pin_group_next_id_v135 = gid + 1
    st.session_state.pin_group_mode_v135 = True
    return g

def end_pin_group_v135():
    init_pin_groups_v135()
    st.session_state.active_pin_group_id_v135 = None
    st.session_state.pin_group_mode_v135 = False

def toggle_pin_group_v135():
    init_pin_groups_v135()
    if st.session_state.pin_group_mode_v135 and st.session_state.active_pin_group_id_v135 is not None:
        end_pin_group_v135()
        return None
    return start_pin_group_v135()

def flatten_pin_groups_v135():
    init_pin_groups_v135()
    pts=[]
    for g in st.session_state.pin_groups_v135:
        for p in g.get("points", []):
            try: pts.append((float(p[0]), float(p[1])))
            except Exception: pass
    st.session_state.required_pins_v118 = pts
    return pts

def add_pin_to_active_group_v135(pt: LatLon)->bool:
    init_pin_groups_v135()
    g = active_group_v135()
    if g is None:
        g = start_pin_group_v135()
    try:
        p=(float(pt[0]), float(pt[1]))
    except Exception:
        return False
    # 同一グループ内・全体で2m以内は重複扱い
    for old in flatten_pin_groups_v135():
        if haversine_m(p, old) < 2.0:
            return False
    g.setdefault("points", []).append(p)
    flatten_pin_groups_v135()
    return True

def undo_pin_group_v135():
    init_pin_groups_v135()
    g = active_group_v135()
    if g is None and st.session_state.pin_groups_v135:
        g = st.session_state.pin_groups_v135[-1]
    if g and g.get("points"):
        g["points"].pop()
        flatten_pin_groups_v135()
        return True
    return False

def clear_pin_groups_v135():
    st.session_state.pin_groups_v135=[]
    st.session_state.active_pin_group_id_v135=None
    st.session_state.pin_group_next_id_v135=1
    st.session_state.pin_group_mode_v135=False
    st.session_state.required_pins_v118=[]

def draw_pin_groups_v135(m):
    init_pin_groups_v135()
    for g in st.session_state.pin_groups_v135:
        color = g.get("color", "blue")
        hexcolor = PIN_GROUP_COLOR_HEX_V129.get(color, "#2563eb")
        pts=[]
        for p in g.get("points", []):
            try: pts.append((float(p[0]), float(p[1])))
            except Exception: pass
        for i,p in enumerate(pts, start=1):
            folium.Marker(
                location=[p[0], p[1]],
                tooltip=f"{g.get('name','グループ')} #{i}",
                icon=folium.Icon(color=color if color in PIN_GROUP_COLORS_V129 else "blue", icon="flag")
            ).add_to(m)
        if len(pts)>=2:
            folium.PolyLine([[p[0],p[1]] for p in pts], color=hexcolor, weight=3, opacity=0.75, dash_array="5,6", tooltip=f"{g.get('name')} ピン順").add_to(m)
    return m

def route_between_points_v135(a:LatLon, b:LatLon, mode:str="normal", seed:int=0)->List[LatLon]:
    # ピン内/通常は通常ブレ。丁目間だけ弱ブレにしたい場合は mode='move'
    amp = float(st.session_state.get("move_wiggle_m_v135", 0.30)) if mode=="move" else float(st.session_state.get("normal_wiggle_m_v135", 2.75))
    return wiggle_polyline([a,b], amp_m=amp, every_m=5.0, seed=seed)

def _pin_chain_segment_v135(entry: LatLon, exitp: LatLon, ordered_pins: List[Tuple[int, LatLon]], seed: int, radius_m: float) -> List[LatLon]:
    if not ordered_pins:
        return [entry, exitp]
    pts=[entry]
    max_direct = float(st.session_state.get("pin_group_direct_connect_limit_m_v135", 170.0))
    for k, (_idx, pin) in enumerate(ordered_pins):
        if haversine_m(pts[-1], pin) > max_direct:
            # 同じグループ内でも遠すぎる場合は、直線長距離ジャンプを避けるためL字寄りで密化
            mid=(pts[-1][0], pin[1])
            seg=wiggle_polyline([pts[-1], mid, pin], amp_m=1.0, every_m=5.0, seed=seed+k*101)
        else:
            seg=route_between_points_v135(pts[-1], pin, mode="normal", seed=seed+k*101)
        pts.extend(seg[1:] if len(seg)>1 else [pin])
        # ピン周辺は通常住宅地と同じブレ。大きな円ではなく小さく寄る。
        r=max(1.5, min(float(radius_m), 12.0))*0.42
        tiny=loop_around_pin(pin, radius_m=r, seed=seed+k*131+500)
        if len(tiny)>1:
            pts.extend(tiny[1:])
    if haversine_m(pts[-1], exitp)>0.8:
        pts.extend(route_between_points_v135(pts[-1], exitp, mode="normal", seed=seed+9090)[1:])
    return remove_near_duplicates(pts, 0.7)

def insert_required_pins_into_route(base_route: List[LatLon], pins: Sequence[LatLon], pin_radius_m: float, seed: int) -> Tuple[List[LatLon], List[str]]:
    """v135: 色別ピングループ方式。
    - 同じ色/同じグループだけ、打った順番で接続
    - 別グループ同士は絶対につながない
    - グループ全体を通常ルート上の最寄り地点へ枝として挿入
    """
    logs=[]
    init_pin_groups_v135()
    groups=[]
    # 旧required_pinsしかない場合の互換: 1グループとして扱う
    if st.session_state.pin_groups_v135:
        source_groups=st.session_state.pin_groups_v135
    else:
        source_groups=[{"id":1,"name":"グループ1","color":"blue","points":list(pins or [])}]
    if not base_route:
        return base_route, logs
    for g in source_groups:
        pts=[]
        for p in g.get("points", []):
            try: pts.append((float(p[0]), float(p[1])))
            except Exception: pass
        if not pts:
            continue
        idxs=[nearest_index(base_route, p) for p in pts]
        entry_i=min(idxs); exit_i=max(idxs)
        if exit_i <= entry_i and entry_i < len(base_route)-1:
            exit_i=min(len(base_route)-1, entry_i+1)
        dmin=min(haversine_m(base_route[nearest_index(base_route,p)], p) for p in pts)
        groups.append((entry_i, exit_i, g, pts, dmin))
    groups.sort(reverse=True, key=lambda x:x[0])
    route=list(base_route)
    for gi,(entry_i, exit_i, g, pts, dmin) in enumerate(groups):
        entry=route[min(entry_i, len(route)-1)]
        exitp=route[min(exit_i, len(route)-1)]
        ordered=[(i,p) for i,p in enumerate(pts)]  # 打った順番を維持。近い順に並べ替えない。
        # 入口が最後のピンに近い場合だけ反転。ユーザー順の意図を極力残す。
        if len(ordered)>=2 and haversine_m(entry, ordered[-1][1]) + 20 < haversine_m(entry, ordered[0][1]):
            ordered=list(reversed(ordered))
        seg=_pin_chain_segment_v135(entry, exitp, ordered, seed=seed+int(g.get('id',gi))*1201, radius_m=pin_radius_m)
        if len(seg)<2:
            logs.append(f"{g.get('name','グループ')}: 生成失敗")
            continue
        route=route[:entry_i+1] + seg[1:] + route[exit_i+1:]
        logs.append(f"{g.get('name','グループ')}: {len(pts)}本を同色順番接続 / 最寄り道路 {dmin:.1f}m / 追加 {total_distance_m(seg):.1f}m")
    flatten_pin_groups_v135()
    return remove_near_duplicates(route, 0.8), logs


# -----------------------------
# v126: 前にできていた「OSM道路グラフで道路上を走る」方式を復旧
# -----------------------------

OSMNX_OK = ox is not None and nx is not None


def _polygon_latlon_to_shapely_for_ox(poly: Sequence[LatLon]):
    if Polygon is None or not poly or len(poly) < 3:
        return None
    try:
        return Polygon([(lon, lat) for lat, lon in poly]).buffer(0)
    except Exception:
        return None


def _combine_shapely_polygons(polys: Sequence[Sequence[LatLon]]):
    shapes = []
    for p in polys:
        shp = _polygon_latlon_to_shapely_for_ox(p)
        if shp is not None and not shp.is_empty:
            shapes.append(shp)
    if not shapes:
        return None, []
    try:
        return unary_union(shapes), shapes
    except Exception:
        return shapes[0], shapes


def _polygon_center_radius_for_ox(shapes: Sequence[Any], extra_m: float = 650.0) -> Tuple[float, float, float]:
    minx = min(g.bounds[0] for g in shapes)
    miny = min(g.bounds[1] for g in shapes)
    maxx = max(g.bounds[2] for g in shapes)
    maxy = max(g.bounds[3] for g in shapes)
    center_lat = (miny + maxy) / 2.0
    center_lon = (minx + maxx) / 2.0
    d1 = haversine_m((miny, minx), (maxy, maxx))
    d2 = haversine_m((miny, maxx), (maxy, minx))
    radius = max(d1, d2) / 2.0 + float(extra_m)
    return center_lat, center_lon, max(450.0, min(radius, 9000.0))


def _set_overpass_endpoint_v126(url: str) -> None:
    if ox is None:
        return
    try:
        ox.settings.overpass_url = url
    except Exception:
        pass
    try:
        ox.settings.overpass_endpoint = url
    except Exception:
        pass


def _road_cache_key_v126(center_lat: float, center_lon: float, radius_m: float) -> str:
    import hashlib
    key = json.dumps({
        "lat": round(center_lat, 2),
        "lon": round(center_lon, 2),
        "radius": int(math.ceil(radius_m / 1500.0) * 1500),
        "network": "walk",
        "version": "v126-osmnx-walk-graph",
    }, ensure_ascii=False)
    return hashlib.md5(key.encode("utf-8")).hexdigest()


def _load_graph_cache_v126(center_lat: float, center_lon: float, radius_m: float):
    if ox is None:
        return None
    path = ROAD_CACHE_DIR / f"{_road_cache_key_v126(center_lat, center_lon, radius_m)}.graphml"
    if path.exists():
        try:
            return ox.load_graphml(path)
        except Exception:
            try:
                path.unlink()
            except Exception:
                pass
    return None


def _save_graph_cache_v126(G, center_lat: float, center_lon: float, radius_m: float) -> None:
    if ox is None:
        return
    try:
        path = ROAD_CACHE_DIR / f"{_road_cache_key_v126(center_lat, center_lon, radius_m)}.graphml"
        ox.save_graphml(G, path)
    except Exception:
        pass


def _fetch_walk_graph_v126(center_lat: float, center_lon: float, radius_m: float):
    if ox is None:
        raise RuntimeError("osmnx がありません。pip install osmnx networkx を確認してください。")
    cached = _load_graph_cache_v126(center_lat, center_lon, radius_m)
    if cached is not None:
        return cached
    endpoints = [
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://overpass.osm.ch/api/interpreter",
    ]
    last_error = None
    for ep in endpoints:
        try:
            _set_overpass_endpoint_v126(ep)
            G = ox.graph_from_point((center_lat, center_lon), dist=int(radius_m), network_type="walk", simplify=True)
            _save_graph_cache_v126(G, center_lat, center_lon, radius_m)
            return G
        except Exception as e:
            last_error = e
            continue
    raise RuntimeError(f"OSM道路データ取得に失敗しました: {last_error}")


def _edge_highway_list_v126(value: Any) -> List[str]:
    if value is None:
        return []
    if isinstance(value, list):
        return [str(v) for v in value]
    return [str(value)]


def _exclude_edge_v126(data: Dict[str, Any]) -> bool:
    highways = set(_edge_highway_list_v126(data.get("highway")))
    # v127: 住宅配布の土台に使わない道を明示的に除外。
    # ここが甘いと、畑・河川敷・公園内の作業道まで拾ってしまう。
    if highways & {"motorway", "motorway_link", "trunk", "trunk_link", "raceway", "proposed", "construction"}:
        return True
    if highways & {"track", "bridleway", "cycleway", "steps"}:
        return True
    if str(data.get("access", "")).lower() in {"private", "no", "agricultural", "forestry"}:
        return True
    if str(data.get("service", "")).lower() in {"parking_aisle"}:
        return True
    return False


def _edge_linestring_v126(G, u, v, data):
    if data and data.get("geometry") is not None:
        return data["geometry"]
    if LineString is None:
        return None
    return LineString([(G.nodes[u]["x"], G.nodes[u]["y"]), (G.nodes[v]["x"], G.nodes[v]["y"])])


def _filter_graph_for_polygons_v126(G, shapes: Sequence[Any], strictness: str = "標準"):
    if nx is None or not shapes:
        return None
    edge_ids = []
    for u, v, k, data in G.edges(keys=True, data=True):
        if _exclude_edge_v126(data):
            continue
        line = _edge_linestring_v126(G, u, v, data)
        if line is None:
            continue
        use = False
        for poly in shapes:
            try:
                if strictness == "ゆるめ":
                    use = poly.intersects(line)
                elif strictness == "きびしめ":
                    use = poly.covers(line)
                else:
                    mid = line.interpolate(0.5, normalized=True)
                    use = poly.buffer(0.000015).covers(mid)
                if use:
                    break
            except Exception:
                pass
        if use:
            edge_ids.append((u, v, k))
    if not edge_ids:
        return None
    try:
        H = G.edge_subgraph(edge_ids).copy()
        return H if len(H.nodes) else None
    except Exception:
        return None




def _building_centers_for_shapes_v128(shapes: Sequence[Any], limit: int = 2500) -> List[LatLon]:
    """選択範囲周辺の建物中心を取得。畑・河川敷側の道路を避け、住宅地寄せに使う。"""
    if not shapes:
        return []
    try:
        minx = min(g.bounds[0] for g in shapes)
        miny = min(g.bounds[1] for g in shapes)
        maxx = max(g.bounds[2] for g in shapes)
        maxy = max(g.bounds[3] for g in shapes)
        # 少しだけ余白。大きく広げると関係ない建物を拾うので控えめ。
        pad = 0.00035
        buildings = overpass_buildings_in_bbox(miny - pad, minx - pad, maxy + pad, maxx + pad, timeout=18)
        centers: List[LatLon] = []
        for b in buildings[:limit]:
            if not b:
                continue
            lat = sum(x[0] for x in b) / len(b)
            lon = sum(x[1] for x in b) / len(b)
            # 建物中心が対象ポリゴン近辺にあるものを使う
            if Point is not None:
                pt = Point(lon, lat)
                ok = False
                for shp in shapes:
                    try:
                        if shp.buffer(0.00045).covers(pt):
                            ok = True; break
                    except Exception:
                        pass
                if not ok:
                    continue
            centers.append((lat, lon))
        return centers
    except Exception:
        return []


def _filter_graph_near_buildings_v128(H, building_centers: Sequence[LatLon], max_m: float = 85.0):
    """建物から遠い道路を落として、畑・公園・河川敷側へ吸われるのを防ぐ。
    建物データが薄い地域では無理に適用しない。
    """
    if H is None or nx is None or not building_centers or len(building_centers) < 3:
        return H
    keep_edges=[]
    centers=list(building_centers)
    for u, v, k, data in H.edges(keys=True, data=True):
        line = _edge_linestring_v126(H, u, v, data)
        if line is None:
            continue
        try:
            mid = line.interpolate(0.5, normalized=True)
            mp = (float(mid.y), float(mid.x))
        except Exception:
            mp = ((float(H.nodes[u]["y"]) + float(H.nodes[v]["y"])) / 2.0, (float(H.nodes[u]["x"]) + float(H.nodes[v]["x"])) / 2.0)
        # 近い建物があれば住宅配布用道路として採用
        best = min(haversine_m(mp, c) for c in centers)
        if best <= max_m:
            keep_edges.append((u, v, k))
    if len(keep_edges) < max(4, int(H.number_of_edges() * 0.18)):
        # 建物データ不足で削りすぎる場合は元に戻す
        return H
    try:
        HH = H.edge_subgraph(keep_edges).copy()
        return HH if len(HH.nodes) else H
    except Exception:
        return H
def _min_edge_data_v126(G, u, v):
    data = G.get_edge_data(u, v)
    if not data:
        return None
    best = None
    best_len = 1e18
    for _k, d in data.items():
        if isinstance(d, dict):
            ln = float(d.get("length", 1e18) or 1e18)
            if ln < best_len:
                best_len = ln
                best = d
    return best


def _edge_points_v126(G, u, v) -> List[LatLon]:
    d = _min_edge_data_v126(G, u, v)
    if d and d.get("geometry") is not None:
        coords = list(d["geometry"].coords)
        pts = [(lat, lon) for lon, lat in coords]
        start = (float(G.nodes[u]["y"]), float(G.nodes[u]["x"]))
        if pts and haversine_m(start, pts[-1]) < haversine_m(start, pts[0]):
            pts.reverse()
        return pts
    return [(float(G.nodes[u]["y"]), float(G.nodes[u]["x"])), (float(G.nodes[v]["y"]), float(G.nodes[v]["x"]))]


def _path_nodes_to_points_v126(G, path: Sequence[Any]) -> List[LatLon]:
    pts: List[LatLon] = []
    for u, v in zip(path[:-1], path[1:]):
        ep = _edge_points_v126(G, u, v)
        for p in ep:
            if not pts or haversine_m(pts[-1], p) > 0.3:
                pts.append(p)
    return pts


def _nearest_graph_node_v126(G, p: LatLon):
    if ox is not None:
        try:
            return ox.distance.nearest_nodes(G, p[1], p[0])
        except Exception:
            pass
    best = None
    best_d = 1e18
    for n in G.nodes:
        q = (float(G.nodes[n]["y"]), float(G.nodes[n]["x"]))
        d = haversine_m(p, q)
        if d < best_d:
            best = n
            best_d = d
    return best


def _choose_start_node_v126(H, seed: int):
    nodes = list(H.nodes)
    if not nodes:
        return None
    lat = sum(float(H.nodes[n]["y"]) for n in nodes) / len(nodes)
    lon = sum(float(H.nodes[n]["x"]) for n in nodes) / len(nodes)
    ranked = sorted(nodes, key=lambda n: haversine_m((lat, lon), (float(H.nodes[n]["y"]), float(H.nodes[n]["x"]))))
    rng = random.Random(seed + len(nodes) * 17)
    return rng.choice(ranked[:min(max(5, len(ranked)//4), 50, len(ranked))])


def _edge_key_v126(u, v, k) -> Tuple[str, str, str]:
    a, b = str(u), str(v)
    if a > b:
        a, b = b, a
    return (a, b, str(k))


def _route_nodes_for_component_v126(H, coverage_ratio: float, seed: int) -> List[Any]:
    edges = list(H.edges(keys=True, data=True))
    total_len = sum(float(d.get("length", 0) or 0) for _, _, _, d in edges)
    if total_len <= 0:
        return []
    target_len = total_len * max(0.05, min(1.0, coverage_ratio))
    current = _choose_start_node_v126(H, seed)
    if current is None:
        return []
    route_nodes = [current]
    uncovered = {}
    for u, v, k, d in edges:
        length = float(d.get("length", 0) or 0)
        if length > 0:
            uncovered[_edge_key_v126(u, v, k)] = {"u": u, "v": v, "k": k, "length": length}
    covered = 0.0
    previous = None
    rng = random.Random(seed + 91873)
    max_steps = max(80, len(uncovered) * 4)
    steps = 0

    def uv_pair(a, b):
        return tuple(sorted((str(a), str(b))))

    while uncovered and covered < target_len and steps < max_steps:
        steps += 1
        try:
            lengths = nx.single_source_dijkstra_path_length(H, current, weight="length")
        except Exception:
            break
        candidates = []
        for ek, e in uncovered.items():
            u = e["u"]; v = e["v"]; elen = max(1.0, e["length"])
            for tgt in (u, v):
                d = lengths.get(tgt, 1e18)
                if d >= 1e18:
                    continue
                # 近い未配布道路を拾いながら進む。遠すぎる枝を優先しない。
                score = (d * 0.80 + elen * 0.18) / elen
                if previous is not None and str(tgt) == str(previous):
                    score += 0.55
                score += rng.uniform(0, 0.03)
                candidates.append((score, ek, tgt, d, elen))
        if not candidates:
            break
        candidates.sort(key=lambda x: x[0])
        chosen = None
        chosen_path = None
        for _score, ek, tgt, _d, _elen in candidates[:60]:
            try:
                path = nx.shortest_path(H, current, tgt, weight="length")
            except Exception:
                path = None
            if path:
                chosen = (ek, tgt)
                chosen_path = path
                break
        if chosen is None or chosen_path is None:
            break
        # path上の未配布道路も消化
        for a, b in zip(chosen_path[:-1], chosen_path[1:]):
            previous = current
            route_nodes.append(b)
            pair = uv_pair(a, b)
            rem = []
            for ek2, e2 in uncovered.items():
                if uv_pair(e2["u"], e2["v"]) == pair:
                    covered += e2["length"]
                    rem.append(ek2)
            for rk in rem:
                uncovered.pop(rk, None)
            current = b
        ek, tgt = chosen
        if ek in uncovered:
            e = uncovered.pop(ek)
            nxt = e["v"] if current == e["u"] else e["u"]
            previous = current
            route_nodes.append(nxt)
            covered += e["length"]
            current = nxt
    return route_nodes


def _component_routes_points_v126(H, coverage_pct: int, seed: int) -> List[List[LatLon]]:
    if nx is None or H is None or len(H.nodes) == 0:
        return []
    # weakly connected componentsごと。大きい順に使う。
    try:
        comps = [H.subgraph(c).copy() for c in nx.weakly_connected_components(H)] if H.is_directed() else [H.subgraph(c).copy() for c in nx.connected_components(H)]
    except Exception:
        comps = [H]
    comps.sort(key=lambda g: sum(float(d.get("length", 0) or 0) for _, _, _, d in g.edges(keys=True, data=True)), reverse=True)
    keep = comps[:max(1, min(len(comps), 8))]
    out: List[List[LatLon]] = []
    cov = max(0.05, min(1.0, float(coverage_pct) / 100.0))
    for i, comp in enumerate(keep):
        rn = _route_nodes_for_component_v126(comp, cov, seed + i * 991)
        pts = _path_nodes_to_points_v126(comp, rn)
        if len(pts) >= 2 and total_distance_m(pts) > 20:
            pts = wiggle_polyline(pts, amp_m=1.15, every_m=6.5, seed=seed + i * 333)
            out.append(remove_near_duplicates(pts, 0.8))
    return out


def _road_path_between_osmnx_v126(G, a: LatLon, b: LatLon, seed: int, max_snap_m: float = 90.0, max_path_m: float = 1800.0) -> List[LatLon]:
    if G is None or nx is None or len(G.nodes) == 0:
        return []
    na = _nearest_graph_node_v126(G, a)
    nb = _nearest_graph_node_v126(G, b)
    if na is None or nb is None:
        return []
    da = haversine_m(a, (float(G.nodes[na]["y"]), float(G.nodes[na]["x"])))
    db = haversine_m(b, (float(G.nodes[nb]["y"]), float(G.nodes[nb]["x"])))
    if da > max_snap_m or db > max_snap_m:
        return []
    try:
        path = nx.shortest_path(G, na, nb, weight="length")
    except Exception:
        return []
    pts = _path_nodes_to_points_v126(G, path)
    if len(pts) >= 2 and total_distance_m(pts) <= max_path_m:
        return wiggle_polyline(pts, amp_m=0.65, every_m=8.0, seed=seed)
    return []


def build_pre_pin_route_v126_osmnx(boundary_polys: Sequence[Sequence[LatLon]], pins: Sequence[LatLon], density: float, pin_radius_m: float, seed: int, distance_mode: str, coverage_pct: int = 70) -> Tuple[List[LatLon], List[str]]:
    logs: List[str] = []
    if not OSMNX_OK:
        return [], ["osmnx/networkx が使えないため、道路グラフ方式に入れません。pip install osmnx networkx を確認してください。"]
    if not boundary_polys:
        return [], ["配布範囲がありません。町名候補を配布範囲へ追加してください。"]
    combined, shapes = _combine_shapely_polygons(boundary_polys)
    if not shapes:
        return [], ["配布範囲ポリゴンを読み込めませんでした。"]
    try:
        center_lat, center_lon, radius_m = _polygon_center_radius_for_ox(shapes, extra_m=700)
        G_all = _fetch_walk_graph_v126(center_lat, center_lon, radius_m)
    except Exception as e:
        return [], [str(e)]
    if G_all is None or len(G_all.nodes) == 0:
        return [], ["OSM道路グラフが空です。"]

    strictness = "標準"
    building_centers_all = _building_centers_for_shapes_v128(shapes)
    if building_centers_all:
        logs.append(f"住宅地寄せ: 建物中心 {len(building_centers_all)}件を使用")
    H_all = _filter_graph_for_polygons_v126(G_all, shapes, strictness=strictness)
    if H_all is not None:
        H_all = _filter_graph_near_buildings_v128(H_all, building_centers_all, max_m=92.0)
    if H_all is None or len(H_all.nodes) == 0:
        # 少しゆるめで再抽出。これでも無理なら止める。
        H_all = _filter_graph_for_polygons_v126(G_all, shapes, strictness="ゆるめ")
        if H_all is not None:
            H_all = _filter_graph_near_buildings_v128(H_all, building_centers_all, max_m=100.0)
        logs.append("標準抽出で道路が少なかったため、ゆるめ抽出に切り替えました。")
    if H_all is None or len(H_all.nodes) == 0:
        return [], logs + ["選択した境界内に使える道路が見つかりませんでした。横線の偽ルートは作りません。"]

    # 各町丁目境界ごとに抽出して、前にできていた道路上ルートを作る。
    area_routes: List[List[LatLon]] = []
    for i, shp in enumerate(shapes):
        H = _filter_graph_for_polygons_v126(G_all, [shp], strictness=strictness)
        bcenters = _building_centers_for_shapes_v128([shp])
        if H is not None:
            H = _filter_graph_near_buildings_v128(H, bcenters, max_m=92.0)
        if H is None or len(H.nodes) == 0:
            H = _filter_graph_for_polygons_v126(G_all, [shp], strictness="ゆるめ")
            if H is not None:
                H = _filter_graph_near_buildings_v128(H, bcenters, max_m=100.0)
        if H is None or len(H.nodes) == 0:
            logs.append(f"配布範囲{i+1}: 道路が見つからないためスキップ")
            continue
        routes = _component_routes_points_v126(H, int(coverage_pct), seed + i * 1000)
        if routes:
            # 同一町丁目内の複数コンポーネントは道路接続できるものだけつなぐ
            base = routes[0]
            for j, r in enumerate(routes[1:], start=2):
                conn = _road_path_between_osmnx_v126(H_all, base[-1], r[0], seed + i * 1000 + j, max_snap_m=140, max_path_m=4000)
                if conn:
                    base.extend(conn[1:]); base.extend(r[1:])
                elif haversine_m(base[-1], r[0]) < 25:
                    base.extend(densify([base[-1], r[0]], 6.0)[1:]); base.extend(r[1:])
            area_routes.append(remove_near_duplicates(base, 0.8))
            logs.append(f"配布範囲{i+1}: 道路上ルート {total_distance_m(base)/1000:.2f}km / {len(base)}点")
        else:
            logs.append(f"配布範囲{i+1}: ルート化できる道路がありませんでした。")

    if not area_routes:
        return [], logs + ["道路上ルートを生成できませんでした。"]

    # 町丁目間は道路グラフで接続。直線ジャンプは禁止。
    route = list(area_routes[0])
    for i, r in enumerate(area_routes[1:], start=2):
        conn = _road_path_between_osmnx_v126(G_all, route[-1], r[0], seed + 7000 + i, max_snap_m=180, max_path_m=9000)
        if conn:
            route.extend(conn[1:]); route.extend(r[1:])
            logs.append(f"配布範囲{i}へ道路で接続: {total_distance_m(conn):.1f}m")
        elif haversine_m(route[-1], r[0]) < 28:
            route.extend(densify([route[-1], r[0]], 6.0)[1:]); route.extend(r[1:])
            logs.append(f"配布範囲{i}へ短距離接続")
        else:
            logs.append(f"配布範囲{i}: 道路接続できないため、ジャンプ防止で未接続にしました。")

    # 密度/距離感は点列を荒く/細かくではなく、視覚揺れと点間密度だけで調整
    if distance_mode == "短め":
        step = 10.5
    elif distance_mode == "長め":
        step = 6.5
    else:
        step = 8.0
    route = densify(route, step_m=step)
    route = wiggle_polyline(route, amp_m=1.05 * max(0.75, float(density)), every_m=6.5, seed=seed + 4242)

    with_pins, pin_logs = insert_required_pins_into_route(route, pins, pin_radius_m=pin_radius_m, seed=seed + 9000)
    logs.extend(pin_logs)
    return remove_near_duplicates(with_pins, 0.7), logs


def build_pre_pin_route_v118(boundary_polys: Sequence[Sequence[LatLon]], pins: Sequence[LatLon], density: float, pin_radius_m: float, seed: int, distance_mode: str, coverage_pct: int = 70) -> Tuple[List[LatLon], List[str]]:
    """v127本体。

    回帰防止方針:
    - v126で崩れた「横線・道路無視・一部エリアだけ生成」を避ける。
    - 本命は osmnx/networkx の道路グラフ方式。前にできていた「道路上を走る」を最優先する。
    - 直接Overpassセグメント方式は補助に落とす。道路グラフが成功したら補助方式は使わない。
    - 複数町丁目は全エリアの道路ルートを生成し、町丁目間だけ道路グラフで接続する。
    - 接続距離上限を広げ、近い順の町丁目が未接続で消える問題を避ける。
    - 長距離直線ジャンプ、横線フォールバック、畑横断フォールバックは禁止。
    """
    logs: List[str] = []
    if not boundary_polys:
        return [], ["配布範囲がありません。町名検索で境界を追加してください。"]

    density_factor = float(density)
    pr = float(pin_radius_m)
    if distance_mode == "短め":
        density_factor *= 0.82
        pr *= 0.75
    elif distance_mode == "長め":
        density_factor *= 1.18
        pr *= 1.15

    # 1) 本命: 前に道路上生成ができていた osmnx/networkx 方式を先に使う。
    if OSMNX_OK:
        ox_route, ox_logs = build_pre_pin_route_v126_osmnx(
            boundary_polys,
            pins,
            density=density_factor,
            pin_radius_m=pr,
            seed=seed,
            distance_mode=distance_mode,
            coverage_pct=int(coverage_pct),
        )
        logs.extend(["本命: osmnx道路グラフ方式を実行"] + ox_logs)
        # 全エリアが完全かどうかはログで見るが、少なくとも十分な道路点列がある場合はこれを採用。
        if ox_route and len(ox_route) >= 2 and total_distance_m(ox_route) >= 30:
            return ox_route, logs
    else:
        logs.append("osmnx/networkx が使えません。pip install osmnx networkx を確認してください。")

    # 2) 補助: 直接Overpass道路セグメント方式。横線フォールバックは使わない。
    #    v126ではこちらが先に採用され、道路無視に見える回帰が出たため、v127では補助のみ。
    direct_logs: List[str] = []
    try:
        minlat, minlon, maxlat, maxlon = combine_bounds(boundary_polys, expand_m=260.0)
        all_roads = overpass_roads_in_bbox_cached(round(minlat, 6), round(minlon, 6), round(maxlat, 6), round(maxlon, 6))
    except Exception as e:
        all_roads = []
        direct_logs.append(f"補助: 直接道路取得エラー: {e}")

    if all_roads:
        connector_graph = _build_road_graph(all_roads)
        routes: List[List[LatLon]] = []
        for i, poly in enumerate(boundary_polys):
            r, area_logs = generate_normal_area_route(
                poly,
                seed=seed + i * 1000,
                density=density_factor,
                coverage_pct=int(coverage_pct),
                roads=all_roads,
                connector_graph=connector_graph,
            )
            direct_logs.extend([f"範囲{i+1}: {x}" for x in area_logs])
            if len(r) >= 2 and total_distance_m(r) >= 25:
                routes.append(r)
                direct_logs.append(f"範囲{i+1}: 補助道路ルート生成 {total_distance_m(r)/1000:.2f}km / {len(r)}点")
            else:
                direct_logs.append(f"範囲{i+1}: 補助道路ルート不足")

        if routes:
            base: List[LatLon] = list(routes[0])
            for i, r in enumerate(routes[1:], start=2):
                conn = _road_path_between(connector_graph, base[-1], r[0], seed=seed + 7000 + i, max_snap_m=140.0, max_path_m=8000.0)
                if conn:
                    base.extend(conn[1:])
                    base.extend(r[1:])
                    direct_logs.append(f"範囲{i}: 補助道路で接続 {total_distance_m(conn):.1f}m")
                elif haversine_m(base[-1], r[0]) <= 24:
                    base.extend(densify([base[-1], r[0]], step_m=5.0)[1:])
                    base.extend(r[1:])
                    direct_logs.append(f"範囲{i}: 近接短距離接続")
                else:
                    # 直線ジャンプは作らない。ただしエリア自体を黙って消すのは不可なのでログに明示。
                    direct_logs.append(f"範囲{i}: 補助道路接続不可。長距離直線ジャンプは禁止のため未接続")

            with_pins, pin_logs = insert_required_pins_into_route(base, pins, pin_radius_m=pr, seed=seed + 9000)
            direct_logs.extend(pin_logs)
            final = remove_near_duplicates(with_pins, 0.7)
            if len(final) >= 2 and total_distance_m(final) >= 30:
                return final, logs + ["補助: 直接OSM道路セグメント方式で生成"] + direct_logs

    return [], logs + direct_logs + [
        "道路上ルートを生成できませんでした。",
        "ただし、横線・畑横断・境界外直線ジャンプの偽ルートは作らない設定です。",
        "確認: osmnx/networkx、インターネット、data/kanto_boundaries.geojson、選択町丁目の境界を確認してください。",
    ]

def make_randomized_start_datetime(start_date: _dt.date, hour: int, minute: int, seed: int) -> _dt.datetime:
    """ユーザーは分まで指定、秒・ミリ秒は毎回切り番にならないようランダム付与。"""
    rng = random.Random(int(seed) * 100003 + int(hour) * 997 + int(minute) * 37)
    sec = rng.randint(1, 58)
    ms = rng.randint(111, 987)
    return _dt.datetime.combine(start_date, _dt.time(int(hour), int(minute), sec, ms * 1000))


def format_gpx_time(dt: _dt.datetime) -> str:
    """GPX/RouteHistory用。ミリ秒まで出して切り番感を消す。"""
    return dt.isoformat(timespec="milliseconds") + "Z"

def make_gpx_single_route_v118(points: Sequence[LatLon], start_time: _dt.datetime, speed_kmh: float, stop_total_min: float = 0.0, stop_count: int = 0) -> str:
    """RouteHistory向けに1trksegで出す。停止は座標を変えずtimeだけ加算。"""
    gpx = ET.Element("gpx", version="1.1", creator="ChatGPT v118 pre_pin_required_points_route_builder", xmlns="http://www.topografix.com/GPX/1/1")
    trk = ET.SubElement(gpx, "trk")
    ET.SubElement(trk, "name").text = "posting_route_v126"
    trkseg = ET.SubElement(trk, "trkseg")
    current = start_time
    speed_mps = max(speed_kmh / 3.6, 0.3)
    rng = random.Random(int(start_time.timestamp()) ^ 118123)
    stop_count = int(max(0, stop_count))
    stop_total_sec = max(0.0, float(stop_total_min) * 60.0)
    stop_indices = set()
    if stop_count > 0 and len(points) > 20:
        candidates = list(range(10, len(points)-10))
        rng.shuffle(candidates)
        stop_indices = set(sorted(candidates[:min(stop_count, len(candidates))]))
    each_stop = stop_total_sec / max(stop_count, 1) if stop_count else 0.0
    prev = None
    for idx, p in enumerate(points):
        if prev is not None:
            current += _dt.timedelta(seconds=haversine_m(prev, p) / speed_mps)
        if idx in stop_indices:
            # 停止時間はここでtimeだけ後ろへ。座標は触らない。
            jitter = rng.uniform(-0.18, 0.18) * each_stop
            current += _dt.timedelta(seconds=max(10, each_stop + jitter))
        trkpt = ET.SubElement(trkseg, "trkpt", lat=f"{p[0]:.8f}", lon=f"{p[1]:.8f}")
        ET.SubElement(trkpt, "ele").text = "3.0"
        ET.SubElement(trkpt, "time").text = format_gpx_time(current)
        prev = p
    return ET.tostring(gpx, encoding="utf-8", xml_declaration=True).decode("utf-8")

# -----------------------------
# Streamlit UI
# -----------------------------


# =========================================================
# v198 PATCH START: GPXuploader mobile UI clean
# =========================================================

def _v198_mobile_css():
    st.markdown("""
<style>
/* GPXuploader mobile-first polish */
#MainMenu {visibility: hidden;}
footer {visibility: hidden;}
header [data-testid="stToolbar"] {display: none;}

:root {
  --gpx-primary: #1d4ed8;
  --gpx-bg: #f7f8fb;
  --gpx-card: #ffffff;
  --gpx-border: #e5e7eb;
}

.block-container {
  padding-top: 1.0rem !important;
  padding-bottom: 4rem !important;
  max-width: 1180px;
}

[data-testid="stAppViewContainer"] {
  background: linear-gradient(180deg, #f8fafc 0%, #eef2ff 100%);
}

h1 {
  font-size: 2.05rem !important;
  font-weight: 900 !important;
  letter-spacing: -0.03em !important;
  margin-bottom: 0.15rem !important;
}

h2, h3 {
  letter-spacing: -0.02em !important;
}

div[data-testid="stSidebar"] {
  background: #ffffff;
  border-right: 1px solid #e5e7eb;
}

div[data-testid="stSidebar"] h2,
div[data-testid="stSidebar"] h3 {
  font-size: 1.03rem !important;
}

.stButton > button,
.stDownloadButton > button {
  border-radius: 14px !important;
  min-height: 46px !important;
  font-weight: 800 !important;
  border: 1px solid #dbeafe !important;
}

.stButton > button[kind="primary"],
.stDownloadButton > button[kind="primary"] {
  background: var(--gpx-primary) !important;
}

[data-testid="stFileUploader"] {
  background: #ffffff;
  border: 1px solid #e5e7eb;
  border-radius: 16px;
  padding: 0.75rem;
}

[data-testid="stMetric"] {
  background: #ffffff;
  border: 1px solid #e5e7eb;
  border-radius: 16px;
  padding: 0.7rem 0.8rem;
}

div[data-testid="stExpander"] {
  background: rgba(255,255,255,0.82);
  border: 1px solid #e5e7eb !important;
  border-radius: 16px !important;
  overflow: hidden;
}

[data-testid="stImage"] img {
  border-radius: 14px;
  border: 1px solid #e5e7eb;
  box-shadow: 0 4px 12px rgba(15, 23, 42, 0.08);
}

.stAlert {
  border-radius: 14px !important;
}

hr {
  margin: 1.2rem 0 !important;
}

/* Cards/galleries become easier on phones */
@media (max-width: 760px) {
  .block-container {
    padding-left: 0.70rem !important;
    padding-right: 0.70rem !important;
    padding-top: 0.55rem !important;
  }

  h1 {
    font-size: 1.65rem !important;
  }

  h2 {
    font-size: 1.25rem !important;
  }

  h3 {
    font-size: 1.10rem !important;
  }

  [data-testid="column"] {
    width: 100% !important;
    flex: 1 1 100% !important;
    min-width: 100% !important;
  }

  div[data-testid="stHorizontalBlock"] {
    gap: 0.55rem !important;
  }

  .stButton > button,
  .stDownloadButton > button {
    min-height: 50px !important;
    font-size: 0.96rem !important;
  }

  [data-testid="stMetric"] {
    margin-bottom: 0.45rem;
  }

  iframe {
    max-height: 520px !important;
  }
}
</style>
""", unsafe_allow_html=True)


def _v198_header():
    st.markdown("""
<div style="
  background: #ffffff;
  border: 1px solid #e5e7eb;
  border-radius: 18px;
  padding: 14px 16px;
  margin: 8px 0 14px 0;
  box-shadow: 0 8px 20px rgba(15,23,42,0.06);
">
  <div style="font-weight:900;font-size:1.05rem;">GPXuploader</div>
  <div style="color:#475569;font-size:0.92rem;line-height:1.55;">
    GPX作成・マンション看板画像取得・指定マンションExcel画像取得・チラシ合成までをまとめたスマホ向け作業画面です。
  </div>
</div>
""", unsafe_allow_html=True)

# =========================================================
# v198 PATCH END
# =========================================================


def main() -> None:
    st.set_page_config(page_title="GPXuploader", layout="wide", initial_sidebar_state="expanded")
    st.title("GPXuploader")
    st.caption("GPX作成・マンション画像取得・指定マンションExcel画像取得・チラシ合成をスマホでも使いやすくまとめた作業用アプリです。")
    _v198_mobile_css()
    _v198_header()

    missing = []
    if folium is None or st_folium is None:
        missing.append("streamlit-folium / folium")
    if requests is None:
        missing.append("requests")
    if missing:
        st.error("不足ライブラリ: " + ", ".join(missing))
        st.code("pip install streamlit folium streamlit-folium shapely requests", language="bat")
        return

    if "map_center" not in st.session_state:
        st.session_state.map_center = (35.8700, 140.0250)
    if "map_zoom" not in st.session_state:
        st.session_state.map_zoom = 15
    if "boundary_lines" not in st.session_state:
        st.session_state.boundary_lines = []
    # v174: プレビュー境界(boundary_lines)は座標だけなので、画像取得用に町丁目名を別保存する
    if "boundary_line_names_v174" not in st.session_state:
        st.session_state.boundary_line_names_v174 = []
    if "boundary_label" not in st.session_state:
        st.session_state.boundary_label = ""
    if "route_boundaries_v118" not in st.session_state:
        st.session_state.route_boundaries_v118 = []
    if "required_pins_v118" not in st.session_state:
        st.session_state.required_pins_v118 = []
    if "last_generated_route_v118" not in st.session_state:
        st.session_state.last_generated_route_v118 = []
    if "last_generated_logs_v118" not in st.session_state:
        st.session_state.last_generated_logs_v118 = []
    if "search_candidates_v126" not in st.session_state:
        st.session_state.search_candidates_v126 = []
    if "selected_candidate_idxs_v126" not in st.session_state:
        st.session_state.selected_candidate_idxs_v126 = []
    if "candidate_selection_sig_v126" not in st.session_state:
        st.session_state.candidate_selection_sig_v126 = None
    if "pin_click_mode_v126" not in st.session_state:
        st.session_state.pin_click_mode_v126 = False
    if "last_pin_click_sig_v126" not in st.session_state:
        st.session_state.last_pin_click_sig_v126 = None

    with st.sidebar:
        st.header("1. エリア検索")
        st.caption("市名だけなら市内の町丁目一覧、町名まで入れればその町の丁目一覧を出します。候補は1か所にまとめました。")
        query = st.text_input("町名/住所検索", "")
        search_clicked = st.button("候補検索", use_container_width=True)

        if search_clicked:
            try:
                candidates = _v179_sort_candidates(smart_search_place_candidates(query))
                st.session_state.search_candidates_v126 = candidates
                st.session_state.selected_candidate_idxs_v126 = []
                st.session_state.candidate_selection_sig_v126 = None
                if not candidates:
                    st.warning("検索候補がありませんでした。例: 我孫子市 / 我孫子市湖北台 / 東京都台東区浅草 のように入れてください。")
                else:
                    st.success(f"候補を{len(candidates)}件取得しました。下から必要な町丁目を選んでください。")
                    # 検索直後は候補全体が見える位置へ移動する。ピン打ち中にはこの処理は走らない。
                    first = candidates[0]
                    st.session_state.map_center = (float(first["lat"]), float(first["lon"]))
                    st.session_state.map_zoom = 14
                    st.session_state.boundary_label = "検索候補"
                    st.session_state.boundary_lines = []
                    st.session_state.boundary_line_names_v174 = []
            except Exception as e:
                st.error(f"候補検索に失敗しました: {e}")

        candidates = st.session_state.get("search_candidates_v126", []) or []
        if candidates:
            option_idxs = list(range(len(candidates)))
            selected_idxs = st.multiselect(
                "候補を選択（複数可）",
                options=option_idxs,
                default=st.session_state.get("selected_candidate_idxs_v126", []),
                format_func=lambda i: place_label(candidates[int(i)], int(i)),
                key="selected_candidate_idxs_v126",
            )
            selected_idxs = [int(i) for i in selected_idxs]

            # 選択候補は即プレビュー。ただし選択が変わった時だけ地図中心を動かす。
            selected_sig = tuple(selected_idxs)
            if selected_sig != st.session_state.get("candidate_selection_sig_v126"):
                st.session_state.candidate_selection_sig_v126 = selected_sig
                lines_for_preview = []
                names_for_preview = []
                lat_sum = lon_sum = n_sum = 0
                for idx in selected_idxs:
                    p = candidates[idx]
                    try:
                        preview_name = short_place_name(p)
                    except Exception:
                        preview_name = str(p.get("display_name", "") or p.get("name", "") or "") if isinstance(p, dict) else ""
                    lines = place_to_latlon_polylines(p, allow_bbox=False)
                    for line in lines:
                        if len(line) >= 3:
                            lines_for_preview.append(line)
                            if preview_name:
                                names_for_preview.append(preview_name)
                            for lat, lon in line:
                                lat_sum += lat
                                lon_sum += lon
                                n_sum += 1
                st.session_state.boundary_lines = lines_for_preview
                # v174: 追加ボタンを押さずにプレビュー境界から軌跡生成した場合でも町名を失わない
                st.session_state.boundary_line_names_v174 = list(dict.fromkeys(names_for_preview))
                st.session_state.boundary_label = "選択中の候補"
                if n_sum:
                    st.session_state.map_center = (lat_sum / n_sum, lon_sum / n_sum)
                    st.session_state.map_zoom = 15

            add_selected_clicked = st.button("選択候補を配布範囲に追加", use_container_width=True)
            if add_selected_clicked:
                added = 0
                for idx in selected_idxs:
                    p = candidates[idx]
                    lines = place_to_latlon_polylines(p, allow_bbox=False)
                    for line in lines:
                        if len(line) >= 3:
                            st.session_state.route_boundaries_v118.append({
                                "name": short_place_name(p),
                                "coords": line,
                                "precise": _has_polygon_geojson(p),
                            })
                            added += 1
                if added:
                    st.success(f"配布範囲を{added}件追加しました。")
                else:
                    st.warning("正確な町丁目境界を追加できませんでした。検索語を変えてください。")

        c_clear1, c_clear2 = st.columns(2)
        with c_clear1:
            clear_boundary_clicked = st.button("選択表示をクリア", use_container_width=True)
        with c_clear2:
            clear_route_boundaries_clicked = st.button("配布範囲を全削除", use_container_width=True)
        if clear_boundary_clicked:
            st.session_state.boundary_lines = []
            st.session_state.boundary_line_names_v174 = []
            st.session_state.boundary_label = ""
            st.session_state.selected_candidate_idxs_v126 = []
            st.session_state.candidate_selection_sig_v126 = None
            st.rerun()
        if clear_route_boundaries_clicked:
            st.session_state.route_boundaries_v118 = []
            st.success("配布範囲を全削除しました。")

        if st.session_state.get("route_boundaries_v118"):
            st.caption("登録済み配布範囲（不要なものは削除）")
            for i, item in enumerate(list(st.session_state.route_boundaries_v118)):
                nm = item.get("name", f"配布範囲{i+1}") if isinstance(item, dict) else f"配布範囲{i+1}"
                c_name, c_del = st.columns([0.78, 0.22])
                c_name.write(f"{i+1}. {str(nm)[:22]}")
                if c_del.button("削除", key=f"del_boundary_v126_{i}"):
                    st.session_state.route_boundaries_v118.pop(i)
                    st.rerun()

        st.divider()
        st.header("2. 通過ピン")
        init_pin_groups_v135()
        st.caption("ピンONで1グループ開始 → 同じ団地内にマーカーを連続配置 → 取り込み → ピンOFFで終了。次にONで別色グループです。")
        c_pin0, c_pin1, c_pin2 = st.columns(3)
        with c_pin0:
            toggle_group_clicked = st.button("ピンON/OFF", use_container_width=True)
        with c_pin1:
            undo_pin_clicked = st.button("最後のピンを削除", use_container_width=True)
        with c_pin2:
            clear_pins_clicked = st.button("ピン全削除", use_container_width=True)
        import_drawn_pins_clicked = st.button("地図上のマーカーを現在グループへ取り込み", use_container_width=True)
        active_g = active_group_v135()
        if active_g:
            st.info(f"追加中: {active_g.get('name')} / 色: {active_g.get('color')} / {len(active_g.get('points', []))}本")
        else:
            st.caption("現在ピン追加OFF。ピンON/OFFを押すと新しい色グループを開始します。")
        with st.expander("ピングループ設定", expanded=False):
            st.number_input("同色ピンを直接つなぐ最大距離m", 30.0, 400.0, float(st.session_state.get("pin_group_direct_connect_limit_m_v135", 170.0)), 10.0, key="pin_group_direct_connect_limit_m_v135")
            st.number_input("通常/ピン区間GPSブレm", 0.0, 3.0, float(st.session_state.get("normal_wiggle_m_v135", 2.75)), 0.05, key="normal_wiggle_m_v135")
            st.number_input("丁目移動GPSブレm", 0.0, 2.0, float(st.session_state.get("move_wiggle_m_v135", 0.30)), 0.05, key="move_wiggle_m_v135")
        if st.session_state.get("pin_groups_v135"):
            st.caption("登録済みグループ")
            for g in st.session_state.pin_groups_v135:
                st.write(f"{g.get('name')} / {g.get('color')} / {len(g.get('points', []))}本")
        flatten_pin_groups_v135()
        st.divider()
        st.header("3. GPX作成条件")
        coverage_pct = st.select_slider("配布率", options=[40, 50, 60, 70, 80, 90, 100], value=70)
        density = st.slider("通常住宅街ルート密度", 0.5, 2.0, 1.0, 0.1)
        distance_mode = st.selectbox("距離感", ["短め", "標準", "長め"], index=1)
        route_order_mode = st.selectbox(
            "町丁目の回る順番",
            ["選択した順", "近い順（最初に選んだ町から開始）"],
            index=0,
            help="複数の配布範囲を登録した時の順番です。近い順でも、最初に選んだ町丁目は必ずスタート地点として固定します。",
        )
        target_distance_km = st.number_input("指定距離 km（0なら自動）", 0.00, 200.00, 0.00, 0.01, help="例: 24.13。0の時は距離指定なし。指定した場合は、この距離に近づくよう配布率を全エリア均等に調整します。末尾カットはしません。")
        target_jitter_m = st.number_input("指定距離の末尾ランダム幅 m", 0.0, 300.0, 35.0, 1.0, help="指定距離ぴったりではなく、数m〜数十mだけランダムに前後させます。")
        pin_radius = st.slider("通過ピン周辺の回り込み量 m", 0, 45, 18, 1)
        speed = st.number_input("平均速度 km/h", 2.5, 8.0, 3.7, 0.1)
        stop_min = st.number_input("追加停止時間 合計分", 0.0, 300.0, 0.0, 1.0)
        stop_count = st.number_input("停止回数", 0, 300, 0, 1)
        start_date = st.date_input("開始日", value=_dt.date.today())
        c_time_h, c_time_m = st.columns(2)
        start_hour = c_time_h.number_input("開始 時", 0, 23, 9, 1)
        start_minute = c_time_m.number_input("開始 分", 0, 59, 0, 1)
        seed = st.number_input("乱数seed", 1, 999999, 122, 1)
        filename = st.text_input("出力ファイル名", "posting_route_v153.gpx")

    center = map_center_from_state((35.8700, 140.0250))
    m = folium.Map(location=[center[0], center[1]], zoom_start=int(st.session_state.get("map_zoom", 15)), tiles="OpenStreetMap")
    folium.TileLayer("cartodbpositron", name="薄い地図").add_to(m)

    # 検索境界
    for line in st.session_state.boundary_lines:
        folium.PolyLine(line, color="red", weight=4, opacity=0.75, tooltip=st.session_state.boundary_label or "検索境界").add_to(m)

    # 登録済み配布範囲
    for i, item in enumerate(st.session_state.route_boundaries_v118, start=1):
        poly = item.get("coords") if isinstance(item, dict) else item
        nm = item.get("name", f"配布範囲{i}") if isinstance(item, dict) else f"配布範囲{i}"
        if poly:
            folium.Polygon(poly, color="blue", weight=3, fill=True, fill_opacity=0.08, tooltip=str(nm)[:80]).add_to(m)

    # 通過ピン（色別グループ）
    draw_pin_groups_v135(m)

    # v126: 地図左上のマーカー描画でクライアント側に連続配置できるようにする。
    # 後で「地図上のマーカーを通過ピンへ取り込み」を押す方式なので、クリックごとの重い再描画を避ける。
    try:
        Draw(
            export=False,
            draw_options={
                "polyline": False,
                "polygon": False,
                "rectangle": False,
                "circle": False,
                "circlemarker": False,
                "marker": {"repeatMode": True},
            },
            edit_options={"edit": True, "remove": True},
        ).add_to(m)
    except Exception:
        pass

    # 生成済みルート
    if st.session_state.last_generated_route_v118:
        folium.PolyLine(st.session_state.last_generated_route_v118, color="purple", weight=4, opacity=0.9, tooltip="生成ルート").add_to(m)

    folium.LayerControl().add_to(m)

    st.info("①町名検索 → ②配布範囲追加 → ③必要なら通過ピン → ④GPX生成、の順で使います。")
    map_data = st_folium(m, height=620, width=None, returned_objects=["last_clicked", "all_drawings", "zoom", "center"])

    if toggle_group_clicked:
        g = toggle_pin_group_v135()
        st.session_state.last_generated_route_v118 = []
        if g:
            st.success(f"{g.get('name')}（{g.get('color')}）を開始しました。地図左上のマーカーでピンを置いて、取り込みボタンを押してください。")
        else:
            st.info("現在のピングループを終了しました。")
        st.rerun()


    if clear_pins_clicked:
        clear_pin_groups_v135()
        st.session_state.last_generated_route_v118 = []
        st.success("通過ピンを全削除しました。")
        st.rerun()

    if undo_pin_clicked:
        if undo_pin_group_v135():
            st.session_state.last_generated_route_v118 = []
            st.success("最後の通過ピンを削除しました。")
            st.rerun()
        else:
            st.info("削除する通過ピンがありません。")

    # v135: Drawで置いたマーカーを現在の色グループへ一括取り込み。
    if import_drawn_pins_clicked:
        if active_group_v135() is None:
            start_pin_group_v135()
        drawings = (map_data or {}).get("all_drawings") or []
        added = 0
        for f in drawings:
            pt = parse_marker_feature_to_point(f)
            if not pt:
                continue
            if add_pin_to_active_group_v135(pt):
                added += 1
        st.session_state.last_generated_route_v118 = []
        st.success(f"現在グループへ通過ピンを{added}本取り込みました。")
        st.rerun()

    # v135: 通常クリック即追加は廃止。マーカー連続配置→現在グループへ取り込み方式に統一。

    st.subheader("現在の設定")
    b_count = len(boundary_polygon_for_generation())
    flatten_pin_groups_v135()
    p_count = len(st.session_state.required_pins_v118)
    cols = st.columns(5)
    cols[0].metric("配布範囲", f"{b_count}件")
    cols[1].metric("通過ピン", f"{p_count}本")
    cols[2].metric("配布率", f"{int(coverage_pct)}%")
    cols[3].metric("距離感", distance_mode)
    cols[4].metric("速度", f"{speed:.2f} km/h")
    try:
        st.caption(f"町丁目順番: {route_order_mode}")
    except Exception:
        pass

    generate_clicked = st.button("GPX軌跡を生成/更新", type="primary", use_container_width=True)

    if generate_clicked:
        # v173: 「この条件で軌跡を生成」時に、実際に使った町丁目名を保存する。
        # ルート生成は、配布範囲に追加済みが無い場合でも「現在プレビュー中の境界(boundary_lines)」で生成できる。
        # そのため画像取得側が route_boundaries_v118 だけを見ると、生成済みなのに町丁目名が空になることがあった。
        try:
            st.session_state["last_generated_area_names_v173"] = _v173_collect_area_names_for_image()
        except Exception:
            st.session_state["last_generated_area_names_v173"] = []
        polys = boundary_polygon_for_generation()
        try:
            polys, order_logs = order_boundary_polys_v152(polys, route_order_mode)
        except Exception as e:
            order_logs = [f"町丁目順番の並べ替えをスキップ: {e}"]
        pins = list(st.session_state.required_pins_v118)
        progress = st.progress(0, text="生成準備中です...")
        with st.spinner("ルート生成中です。地図データ取得・ルート計算をしています..."):
            progress.progress(10, text="境界・ピン情報を確認中...")
            try:
                route, logs = build_route_distance_coverage_balance_v141(
                    polys,
                    pins,
                    density=float(density),
                    pin_radius_m=float(pin_radius),
                    seed=int(seed),
                    distance_mode=distance_mode,
                    coverage_pct=int(coverage_pct),
                    target_distance_km=float(target_distance_km),
                    target_jitter_m=float(target_jitter_m),
                    progress=progress,
                )
            except Exception as e:
                route, logs = [], [f"距離・配布率バランス生成エラー: {e}"]
            try:
                logs = list(order_logs) + list(logs)
            except Exception:
                pass
            progress.progress(92, text="ルート整形中...")
        st.session_state.last_generated_route_v118 = route
        st.session_state.last_generated_logs_v118 = logs
        progress.progress(100, text="生成完了。地図を更新します...")
        # 地図は生成ボタンより上に描画されるため、生成直後に再読込して上部プレビューへ反映する。
        st.rerun()

    route = st.session_state.last_generated_route_v118
    logs = st.session_state.last_generated_logs_v118
    if (not route) and logs:
        st.subheader("生成結果")
        st.error("道路上ルートを生成できませんでした。下の処理ログを確認してください。")
        with st.expander("処理ログ", expanded=True):
            for x in logs:
                st.write("- " + str(x))
    if route:
        dist_km = total_distance_m(route) / 1000.0
        max_step = max_step_m([route])
        moving_sec = (dist_km * 1000) / max(float(speed) / 3.6, 0.3)
        total_sec = moving_sec + float(stop_min) * 60
        start_dt = make_randomized_start_datetime(start_date, int(start_hour), int(start_minute), int(seed))
        finish_dt = start_dt + _dt.timedelta(seconds=total_sec)
        effective_speed_kmh = dist_km / max(total_sec / 3600.0, 1e-9)
        st.subheader("生成結果")
        c1, c2, c3, c4, c5, c6 = st.columns(6)
        c1.metric("距離", f"{dist_km:.2f} km")
        c2.metric("点数", f"{len(route)}")
        c3.metric("最大点間距離", f"{max_step:.1f} m")
        c4.metric("終了時刻", finish_dt.strftime("%H:%M:%S") + f".{finish_dt.microsecond//1000:03d}")
        c5.metric("合計時間", str(_dt.timedelta(seconds=int(total_sec))))
        c6.metric("停止込み平均速度", f"{effective_speed_kmh:.2f} km/h")
        st.caption(f"設定移動速度: {float(speed):.2f} km/h / 追加停止時間: {float(stop_min):.1f}分 / 停止込み平均速度: {effective_speed_kmh:.2f} km/h")
        if max_step > 75:
            st.warning("最大点間距離が大きめです。通過ピンが通常ルートから遠すぎる可能性があります。密度を上げるか、ピン位置を調整してください。")
        else:
            st.success("大きな点間ジャンプは出にくい点列です。")
        with st.expander("処理ログ", expanded=False):
            for x in logs:
                st.write("- " + x)

        st.caption("速度・密度・距離感・通過ピン回り込み量を変えたら、『この条件で軌跡を生成/更新』を押すと、座標を直接編集せずに再生成します。")
        start_dt = make_randomized_start_datetime(start_date, int(start_hour), int(start_minute), int(seed))
        gpx_text = make_gpx_single_route_v118(route, start_dt, speed_kmh=float(speed), stop_total_min=float(stop_min), stop_count=int(stop_count))
        out_name = filename if filename.lower().endswith(".gpx") else filename + ".gpx"
        st.download_button("GPXをダウンロード", data=gpx_text.encode("utf-8"), file_name=out_name, mime="application/gpx+xml", use_container_width=True)



    # v170: 選択済み町丁目から、リバブル町名ページ→詳細ページ→マンション名看板画像を取得
    try:
        render_selected_area_livable_sign_images_v170()
    except Exception as e:
        st.error(f"v170マンション名看板画像機能でエラー: {e}")

    st.divider()
    with st.expander("補足メモ", expanded=False):
        st.caption("内部ロジックは既存版のまま維持しています。画面だけスマホ向けに整理しています。")





# ==================================================
# v135 ACTIVE OVERRIDES
# 目的:
# 1) 通常配布線の揺れを本当に不規則化する
# 2) ピン周りの丸/四角囲みを完全に消し、ピンは通過点だけにする
# 3) 配布率70%で見た目100%になる問題を、接続線込みで抑える
# ==================================================

def wiggle_polyline(points: Sequence[LatLon], amp_m: float, every_m: float, seed: int) -> List[LatLon]:
    """v135: 不規則GPSブレ。
    以前はサイン波ベースで、振れ幅が同じように続いて見えた。
    今回は一定距離ごとに揺れ強度そのものを変え、大/中/小が混ざるようにする。
    """
    if len(points) < 2:
        return list(points)
    rng = random.Random(seed)
    dense = densify(points, every_m)
    if len(dense) < 2:
        return list(points)

    out = [dense[0]]
    current_offset = 0.0
    target_offset = 0.0
    hold = 0
    for i in range(1, len(dense) - 1):
        prev_p, p, next_p = dense[i - 1], dense[i], dense[i + 1]
        origin = p
        x1, y1 = local_xy(origin, prev_p)
        x2, y2 = local_xy(origin, next_p)
        vx, vy = x2 - x1, y2 - y1
        norm = math.hypot(vx, vy) or 1.0
        nxv, nyv = -vy / norm, vx / norm

        # 3〜10点ごとに「次の揺れ幅」を作り直す。これで同じ幅が続かない。
        if hold <= 0:
            scale = rng.choice([0.12, 0.22, 0.35, 0.55, 0.85, 1.15, 1.45, 1.85])
            # たまに大きめ、たまにほぼ道路上
            if rng.random() < 0.16:
                scale *= rng.uniform(1.25, 1.75)
            if rng.random() < 0.18:
                scale *= rng.uniform(0.15, 0.40)
            target_offset = rng.choice([-1.0, 1.0]) * amp_m * scale
            hold = rng.randint(3, 10)
        hold -= 1

        # 急に折れすぎないように、ただし同じ波形にならない程度に追従
        current_offset = current_offset * rng.uniform(0.42, 0.68) + target_offset * rng.uniform(0.32, 0.58)
        current_offset += rng.uniform(-0.22, 0.22) * amp_m
        # 上限だけかける
        current_offset = max(-amp_m * 2.35, min(amp_m * 2.35, current_offset))
        out.append(local_ll(origin, (nxv * current_offset, nyv * current_offset)))
    out.append(dense[-1])
    return out


def route_between_points_v135(a: LatLon, b: LatLon, mode: str = "normal", seed: int = 0) -> List[LatLon]:
    amp = float(st.session_state.get("move_wiggle_m_v135", 0.30)) if mode == "move" else float(st.session_state.get("normal_wiggle_m_v135", 2.75))
    step = 8.0 if mode == "move" else 4.6
    return wiggle_polyline([a, b], amp_m=amp, every_m=step, seed=seed)

# 旧UI/旧関数名から呼ばれてもv135へ流す
route_between_points_v132 = route_between_points_v135


def wiggle_through_waypoints_v135(waypoints: Sequence[LatLon], amp_m: float, seed: int) -> List[LatLon]:
    """ピン通過用。
    各ピンは必ず通過する。ただしピン周りに丸/四角を作らない。
    セグメントごとに揺らし、終点は必ずピン座標に戻す。
    """
    pts = [tuple(p) for p in waypoints if p is not None]
    if len(pts) < 2:
        return pts
    out = [pts[0]]
    for i, (a, b) in enumerate(zip(pts[:-1], pts[1:])):
        d = haversine_m(a, b)
        if d < 0.8:
            continue
        # ピン同士/ピン接続は丸を作らないため、短距離は直線寄りにする
        local_amp = min(amp_m, max(0.35, d * 0.055))
        seg = wiggle_polyline([a, b], amp_m=local_amp, every_m=4.8, seed=seed + i * 137)
        # 終点を必ずbにする。これでピンの周りを囲って戻る動きが出ない。
        if seg:
            seg[-1] = b
        out.extend(seg[1:] if len(seg) > 1 else [b])
    return remove_near_duplicates(out, 0.45)


def _pin_chain_segment_v135(entry: LatLon, exitp: LatLon, ordered_pins: List[Tuple[int, LatLon]], seed: int, radius_m: float) -> List[LatLon]:
    if not ordered_pins:
        return [entry, exitp]
    pins_only = [p for _idx, p in ordered_pins]
    waypoints = [entry] + pins_only + [exitp]
    amp = float(st.session_state.get("normal_wiggle_m_v135", 2.75))
    return wiggle_through_waypoints_v135(waypoints, amp_m=amp, seed=seed)

# 旧名からもv135へ流す
_pin_chain_segment_v132 = _pin_chain_segment_v135


def insert_required_pins_into_route(base_route: List[LatLon], pins: Sequence[LatLon], pin_radius_m: float, seed: int) -> Tuple[List[LatLon], List[str]]:
    """v135: ピンは同色グループ内で順番通過。丸/四角ループは作らない。"""
    logs = []
    init_pin_groups_v135()
    if not base_route:
        return base_route, logs
    if st.session_state.pin_groups_v135:
        source_groups = st.session_state.pin_groups_v135
    else:
        source_groups = [{"id": 1, "name": "グループ1", "color": "blue", "points": list(pins or [])}]

    groups = []
    for gi, g in enumerate(source_groups):
        pts = []
        for p in g.get("points", []):
            try:
                pts.append((float(p[0]), float(p[1])))
            except Exception:
                pass
        if not pts:
            continue
        first_idx = nearest_index(base_route, pts[0])
        last_idx = nearest_index(base_route, pts[-1])
        entry_i = min(first_idx, last_idx)
        exit_i = max(first_idx, last_idx)
        ordered = [(i, p) for i, p in enumerate(pts)]
        if first_idx > last_idx:
            ordered = list(reversed(ordered))
        dmin = min(haversine_m(base_route[nearest_index(base_route, p)], p) for p in pts)
        groups.append((entry_i, exit_i, g, ordered, dmin, gi))

    groups.sort(reverse=True, key=lambda x: x[0])
    route = list(base_route)
    for entry_i, exit_i, g, ordered, dmin, gi in groups:
        entry = route[min(entry_i, len(route) - 1)]
        exitp = route[min(exit_i, len(route) - 1)]
        seg = _pin_chain_segment_v135(entry, exitp, ordered, seed=seed + int(g.get('id', gi)) * 1201, radius_m=pin_radius_m)
        if len(seg) < 2:
            logs.append(f"{g.get('name', 'グループ')}: 生成失敗")
            continue
        route = route[:entry_i + 1] + seg[1:] + route[exit_i + 1:]
        logs.append(f"{g.get('name', 'グループ')}: {len(ordered)}本を順番通過 / ピン囲みなし / 最寄り道路 {dmin:.1f}m")
    flatten_pin_groups_v135()
    return remove_near_duplicates(route, 0.7), logs


def _component_routes_points_v126(H, coverage_pct: int, seed: int) -> List[List[LatLon]]:
    """v135: 配布率が見た目100%に膨らむ原因を補正。
    原因: 未配布道路へ移動する接続線も地図上では配布線として見えるため、
    70%指定でも表示上はほぼ全道路に線が付いていた。
    対策: 道路エッジの消化目標を控えめにし、接続線込みで70%前後に見えるようにする。
    """
    if nx is None or H is None or len(H.nodes) == 0:
        return []
    try:
        comps = [H.subgraph(c).copy() for c in nx.weakly_connected_components(H)] if H.is_directed() else [H.subgraph(c).copy() for c in nx.connected_components(H)]
    except Exception:
        comps = [H]
    comps.sort(key=lambda g: sum(float(d.get("length", 0) or 0) for _, _, _, d in g.edges(keys=True, data=True)), reverse=True)
    keep = comps[:max(1, min(len(comps), 6))]
    out: List[List[LatLon]] = []
    raw_cov = max(0.05, min(1.0, float(coverage_pct) / 100.0))
    # 接続線で増える分を引く。70%なら内部エッジは約28%から開始。
    # これ以上高いと、グリッド住宅地では見た目がほぼ100%になる。
    effective_cov = max(0.04, min(0.62, raw_cov * 0.40))
    for i, comp in enumerate(keep):
        rn = _route_nodes_for_component_v126(comp, effective_cov, seed + i * 991)
        pts = _path_nodes_to_points_v126(comp, rn)
        if len(pts) >= 2 and total_distance_m(pts) > 20:
            amp = float(st.session_state.get("normal_wiggle_m_v135", 2.75))
            pts = wiggle_polyline(pts, amp_m=amp, every_m=4.8, seed=seed + i * 333)
            out.append(remove_near_duplicates(pts, 0.7))
    return out



# ==================================================
# v135 ACTIVE OVERRIDES
# 目的:
# 1) 通常配布線に、建物側へ少し入る「ちょん入り・ギザギザ」を追加
# 2) GPX時刻をRouteHistoryで入力時刻どおりに見えるようJST→UTC変換して出力
# 3) 標高を3.0固定ではなく自然なランダム勾配にする
# 4) ピンは囲わず、通過点のまま維持
# ==================================================

JST_OFFSET_HOURS_V135 = 9


def format_gpx_time(dt: _dt.datetime) -> str:
    """v135: 画面入力は日本時間として扱い、GPXにはUTC(Z)で出す。
    例: 画面で09:02ならGPXは00:02Z。RouteHistory側では09:02表示になる。
    """
    utc_dt = dt - _dt.timedelta(hours=JST_OFFSET_HOURS_V135)
    return utc_dt.isoformat(timespec="milliseconds") + "Z"


def add_posting_spurs_v135(points: Sequence[LatLon], seed: int, density: float = 1.0, max_spur_m: float = 7.5) -> List[LatLon]:
    """道路を歩くだけに見えないよう、配布中の短い建物寄り入り込みを混ぜる。
    大きな枝道ではなく、数m〜十数m弱の「ちょん」とした入り込みだけ。
    点間ジャンプを出さないよう、必ず小さい点列で戻る。
    """
    pts = [tuple(p) for p in points if p is not None]
    if len(pts) < 6:
        return pts
    rng = random.Random(seed * 9176 + 134)
    out: List[LatLon] = [pts[0]]
    dist_since = 0.0
    next_spur = rng.uniform(34.0, 78.0) / max(0.35, density)

    for i in range(1, len(pts) - 1):
        prev_p, p, next_p = pts[i - 1], pts[i], pts[i + 1]
        out.append(p)
        step_d = haversine_m(prev_p, p)
        dist_since += step_d

        # 短すぎる場所/交差点っぽい連続折れでは入れすぎない
        if dist_since < next_spur:
            continue
        if rng.random() > 0.62:
            dist_since = 0.0
            next_spur = rng.uniform(30.0, 85.0) / max(0.35, density)
            continue

        origin = p
        x1, y1 = local_xy(origin, prev_p)
        x2, y2 = local_xy(origin, next_p)
        vx, vy = x2 - x1, y2 - y1
        norm = math.hypot(vx, vy)
        if norm < 1.5:
            continue
        nxv, nyv = -vy / norm, vx / norm

        # 左右どちらかへ、距離も毎回変える。規則的な櫛形にならないようにする。
        side = rng.choice([-1.0, 1.0])
        depth = rng.uniform(2.8, max_spur_m)
        if rng.random() < 0.18:
            depth *= rng.uniform(1.15, 1.55)
        depth = min(depth, 11.5)

        # 少し前後方向にもずらし、ただの三角形ではなく自然なチョン入りにする。
        along = rng.uniform(-1.4, 2.2)
        spur1 = local_ll(origin, (nxv * side * depth * 0.55 + (vx / norm) * along * 0.35,
                                  nyv * side * depth * 0.55 + (vy / norm) * along * 0.35))
        spur2 = local_ll(origin, (nxv * side * depth + (vx / norm) * along,
                                  nyv * side * depth + (vy / norm) * along))
        back = local_ll(origin, ((vx / norm) * rng.uniform(1.2, 3.2),
                                 (vy / norm) * rng.uniform(1.2, 3.2)))

        # 点間ジャンプ防止: p -> spur1 -> spur2 -> back
        out.extend([spur1, spur2, back])
        dist_since = 0.0
        next_spur = rng.uniform(36.0, 92.0) / max(0.35, density)

    out.append(pts[-1])
    return remove_near_duplicates(out, 0.45)


def wiggle_polyline(points: Sequence[LatLon], amp_m: float, every_m: float, seed: int) -> List[LatLon]:
    """v135: ブレ幅を一定に見せない。大/中/小/ほぼ道路上が混ざるGPSブレ。"""
    if len(points) < 2:
        return list(points)
    rng = random.Random(seed * 1009 + 134)
    dense = densify(points, every_m)
    if len(dense) < 2:
        return list(points)

    out = [dense[0]]
    offset = 0.0
    target = 0.0
    hold = 0
    quiet_until = 0

    for i in range(1, len(dense) - 1):
        prev_p, p, next_p = dense[i - 1], dense[i], dense[i + 1]
        origin = p
        x1, y1 = local_xy(origin, prev_p)
        x2, y2 = local_xy(origin, next_p)
        vx, vy = x2 - x1, y2 - y1
        norm = math.hypot(vx, vy) or 1.0
        nxv, nyv = -vy / norm, vx / norm

        if hold <= 0:
            # たまに小さく、たまに大きく。連続同一幅にならないよう更新間隔も変える。
            if quiet_until > 0:
                scale = rng.uniform(0.05, 0.22)
                quiet_until -= 1
            else:
                scale = rng.choice([0.10, 0.18, 0.32, 0.55, 0.80, 1.10, 1.45, 1.90])
                if rng.random() < 0.16:
                    scale *= rng.uniform(1.25, 1.85)
                if rng.random() < 0.14:
                    quiet_until = rng.randint(2, 5)
            target = rng.choice([-1.0, 1.0]) * amp_m * scale
            hold = rng.randint(2, 9)
        hold -= 1

        offset = offset * rng.uniform(0.38, 0.72) + target * rng.uniform(0.28, 0.62)
        offset += rng.uniform(-0.28, 0.28) * amp_m
        offset = max(-amp_m * 2.55, min(amp_m * 2.55, offset))
        out.append(local_ll(origin, (nxv * offset, nyv * offset)))
    out.append(dense[-1])
    return remove_near_duplicates(out, 0.45)


def route_between_points_v135(a: LatLon, b: LatLon, mode: str = "normal", seed: int = 0) -> List[LatLon]:
    amp = float(st.session_state.get("move_wiggle_m_v135", 0.30)) if mode == "move" else float(st.session_state.get("normal_wiggle_m_v135", 2.80))
    step = 8.0 if mode == "move" else 4.6
    pts = wiggle_polyline([a, b], amp_m=amp, every_m=step, seed=seed)
    # 移動線は弱ブレだけ。配布線だけにチョン入りを入れる。
    if mode != "move":
        pts = add_posting_spurs_v135(pts, seed=seed + 4000, density=0.55, max_spur_m=5.6)
    return pts


# 旧名からもv135へ流す
route_between_points_v133 = route_between_points_v135
route_between_points_v132 = route_between_points_v135


def wiggle_through_waypoints_v135(waypoints: Sequence[LatLon], amp_m: float, seed: int) -> List[LatLon]:
    """ピン通過用。ピンは囲わず、ピン間を通過する。必要に応じて小さいチョン入りを混ぜる。"""
    pts = [tuple(p) for p in waypoints if p is not None]
    if len(pts) < 2:
        return pts
    out = [pts[0]]
    rng = random.Random(seed + 55134)
    for i, (a, b) in enumerate(zip(pts[:-1], pts[1:])):
        d = haversine_m(a, b)
        if d < 0.8:
            continue
        local_amp = min(amp_m, max(0.35, d * 0.050))
        seg = wiggle_polyline([a, b], amp_m=local_amp, every_m=4.8, seed=seed + i * 137)
        # ピン周りを丸で囲まない。終点は必ずピン/出口に戻す。
        if seg:
            seg[-1] = b
        # ピン間が長い時だけ、控えめに配布チョン入りを混ぜる
        if d > 22 and rng.random() < 0.65:
            seg = add_posting_spurs_v135(seg, seed=seed + i * 1777, density=0.45, max_spur_m=4.8)
            if seg:
                seg[-1] = b
        out.extend(seg[1:] if len(seg) > 1 else [b])
    return remove_near_duplicates(out, 0.45)


def _pin_chain_segment_v135(entry: LatLon, exitp: LatLon, ordered_pins: List[Tuple[int, LatLon]], seed: int, radius_m: float) -> List[LatLon]:
    if not ordered_pins:
        return [entry, exitp]
    pins_only = [p for _idx, p in ordered_pins]
    waypoints = [entry] + pins_only + [exitp]
    amp = float(st.session_state.get("normal_wiggle_m_v135", 2.80))
    return wiggle_through_waypoints_v135(waypoints, amp_m=amp, seed=seed)


_pin_chain_segment_v133 = _pin_chain_segment_v135
_pin_chain_segment_v132 = _pin_chain_segment_v135


def insert_required_pins_into_route(base_route: List[LatLon], pins: Sequence[LatLon], pin_radius_m: float, seed: int) -> Tuple[List[LatLon], List[str]]:
    """v135: ピンは同色グループ内で順番通過。丸/四角ループは作らない。"""
    logs = []
    init_pin_groups_v135()
    if not base_route:
        return base_route, logs
    if st.session_state.pin_groups_v135:
        source_groups = st.session_state.pin_groups_v135
    else:
        source_groups = [{"id": 1, "name": "グループ1", "color": "blue", "points": list(pins or [])}]

    groups = []
    for gi, g in enumerate(source_groups):
        pts = []
        for p in g.get("points", []):
            try:
                pts.append((float(p[0]), float(p[1])))
            except Exception:
                pass
        if not pts:
            continue
        first_idx = nearest_index(base_route, pts[0])
        last_idx = nearest_index(base_route, pts[-1])
        entry_i = min(first_idx, last_idx)
        exit_i = max(first_idx, last_idx)
        ordered = [(i, p) for i, p in enumerate(pts)]
        if first_idx > last_idx:
            ordered = list(reversed(ordered))
        dmin = min(haversine_m(base_route[nearest_index(base_route, p)], p) for p in pts)
        groups.append((entry_i, exit_i, g, ordered, dmin, gi))

    groups.sort(reverse=True, key=lambda x: x[0])
    route = list(base_route)
    for entry_i, exit_i, g, ordered, dmin, gi in groups:
        entry = route[min(entry_i, len(route) - 1)]
        exitp = route[min(exit_i, len(route) - 1)]
        seg = _pin_chain_segment_v135(entry, exitp, ordered, seed=seed + int(g.get('id', gi)) * 1201, radius_m=pin_radius_m)
        if len(seg) < 2:
            logs.append(f"{g.get('name', 'グループ')}: 生成失敗")
            continue
        route = route[:entry_i + 1] + seg[1:] + route[exit_i + 1:]
        logs.append(f"{g.get('name', 'グループ')}: {len(ordered)}本を順番通過 / ピン囲みなし / 最寄り道路 {dmin:.1f}m")
    flatten_pin_groups_v135()
    return remove_near_duplicates(route, 0.7), logs


def _component_routes_points_v126(H, coverage_pct: int, seed: int) -> List[List[LatLon]]:
    """v135: 配布率補正を維持しつつ、通常配布線にチョン入りを混ぜる。"""
    if nx is None or H is None or len(H.nodes) == 0:
        return []
    try:
        comps = [H.subgraph(c).copy() for c in nx.weakly_connected_components(H)] if H.is_directed() else [H.subgraph(c).copy() for c in nx.connected_components(H)]
    except Exception:
        comps = [H]
    comps.sort(key=lambda g: sum(float(d.get("length", 0) or 0) for _, _, _, d in g.edges(keys=True, data=True)), reverse=True)
    keep = comps[:max(1, min(len(comps), 6))]
    out: List[List[LatLon]] = []
    raw_cov = max(0.05, min(1.0, float(coverage_pct) / 100.0))
    # 接続線で表示が膨らむため、内部エッジ消化率は控えめ。
    effective_cov = max(0.04, min(0.62, raw_cov * 0.40))
    for i, comp in enumerate(keep):
        rn = _route_nodes_for_component_v126(comp, effective_cov, seed + i * 991)
        pts = _path_nodes_to_points_v126(comp, rn)
        if len(pts) >= 2 and total_distance_m(pts) > 20:
            amp = float(st.session_state.get("normal_wiggle_m_v135", 2.80))
            pts = wiggle_polyline(pts, amp_m=amp, every_m=4.8, seed=seed + i * 333)
            pts = add_posting_spurs_v135(pts, seed=seed + i * 555, density=max(0.45, raw_cov), max_spur_m=7.8)
            out.append(remove_near_duplicates(pts, 0.7))
    return out


def _random_elevation_series_v135(n: int, seed: int, base: float = 3.0) -> List[float]:
    rng = random.Random(seed * 31337 + 134)
    ele = base + rng.uniform(-0.7, 0.7)
    target = ele
    hold = 0
    out = []
    for i in range(max(0, n)):
        if hold <= 0:
            target = base + rng.uniform(-1.8, 2.2)
            if rng.random() < 0.12:
                target += rng.choice([-1, 1]) * rng.uniform(0.8, 1.7)
            hold = rng.randint(8, 28)
        hold -= 1
        ele = ele * 0.93 + target * 0.07 + rng.uniform(-0.08, 0.08)
        ele = max(0.8, min(8.5, ele))
        out.append(ele)
    return out


def make_gpx_single_route_v118(points: Sequence[LatLon], start_time: _dt.datetime, speed_kmh: float, stop_total_min: float = 0.0, stop_count: int = 0) -> str:
    """v135: RouteHistory向け。
    - 入力時刻はJST、GPXはUTC Zへ変換
    - 速度は微妙に揺らしつつ、全体の所要時間は指定速度ベースに合わせる
    - 標高は3.0固定にせず、ランダム勾配にする
    """
    pts = [tuple(p) for p in points if p is not None]
    gpx = ET.Element("gpx", version="1.1", creator="ChatGPT v135 posting_route_builder", xmlns="http://www.topografix.com/GPX/1/1")
    trk = ET.SubElement(gpx, "trk")
    ET.SubElement(trk, "name").text = "posting_route_v135"
    trkseg = ET.SubElement(trk, "trkseg")
    if not pts:
        return ET.tostring(gpx, encoding="utf-8", xml_declaration=True).decode("utf-8")

    base_speed_mps = max(float(speed_kmh) / 3.6, 0.3)
    rng = random.Random(int(start_time.timestamp()) ^ 134134)
    raw_steps = [0.0]
    for a, b in zip(pts[:-1], pts[1:]):
        d = haversine_m(a, b)
        # 歩行速度の自然な揺れ。短いギザギザでは少し遅く、直線移動では少し速いことがある。
        factor = rng.uniform(0.78, 1.22)
        if d < 3.0:
            factor *= rng.uniform(0.70, 0.95)
        raw_steps.append(d / max(0.25, base_speed_mps * factor))

    target_moving = sum(haversine_m(a, b) for a, b in zip(pts[:-1], pts[1:])) / base_speed_mps
    raw_moving = sum(raw_steps)
    scale = target_moving / raw_moving if raw_moving > 0 else 1.0
    steps = [s * scale for s in raw_steps]

    stop_count = int(max(0, stop_count))
    stop_total_sec = max(0.0, float(stop_total_min) * 60.0)
    stop_indices = set()
    if stop_count > 0 and len(pts) > 30:
        candidates = list(range(12, len(pts) - 12))
        rng.shuffle(candidates)
        stop_indices = set(sorted(candidates[:min(stop_count, len(candidates))]))
    each_stop = stop_total_sec / max(stop_count, 1) if stop_count else 0.0
    elevations = _random_elevation_series_v135(len(pts), seed=int(start_time.timestamp() % 100000))

    current = start_time
    for idx, p in enumerate(pts):
        if idx > 0:
            current += _dt.timedelta(seconds=steps[idx])
        if idx in stop_indices:
            jitter = rng.uniform(-0.22, 0.22) * each_stop
            current += _dt.timedelta(seconds=max(8.0, each_stop + jitter))
        trkpt = ET.SubElement(trkseg, "trkpt", lat=f"{p[0]:.8f}", lon=f"{p[1]:.8f}")
        ET.SubElement(trkpt, "ele").text = f"{elevations[idx]:.2f}"
        ET.SubElement(trkpt, "time").text = format_gpx_time(current)
    return ET.tostring(gpx, encoding="utf-8", xml_declaration=True).decode("utf-8")


# 旧複数trkseg出力側が呼ばれた場合もv135標高/時刻にする
def make_gpx(segments: Sequence[Sequence[LatLon]], start_time: _dt.datetime, speed_kmh: float, stop_total_min: float = 0.0) -> str:
    pts: List[LatLon] = []
    for seg in segments:
        pts.extend([tuple(p) for p in seg if p is not None])
    return make_gpx_single_route_v118(pts, start_time, speed_kmh, stop_total_min=stop_total_min, stop_count=0)




# ==================================================
# v135 ACTIVE OVERRIDE: 同じ道を何度も往復しすぎる問題の抑制
# ==================================================

def _route_nodes_for_component_v126(H, coverage_ratio: float, seed: int) -> List[Any]:
    """v135: 近い未配布道路だけを追う方式から、同一道路反復ペナルティ付き探索へ変更。
    目的:
    - 同じ幹線/同じ通路を3回4回も往復しない
    - 近くの未配布枝を優先しつつ、既に通った道を接続路として何度も使う候補は避ける
    - どうしても必要な接続だけは許容するので、ジャンプは作らない
    """
    if nx is None or H is None or len(H.nodes) == 0:
        return []
    edges = list(H.edges(keys=True, data=True))
    total_len = sum(float(d.get("length", 0) or 0) for _, _, _, d in edges)
    if total_len <= 0:
        return []
    target_len = total_len * max(0.05, min(1.0, coverage_ratio))
    current = _choose_start_node_v126(H, seed)
    if current is None:
        return []

    rng = random.Random(seed + 135135)
    route_nodes: List[Any] = [current]

    def uv_pair(a, b):
        return tuple(sorted((str(a), str(b))))

    # edge辞書
    uncovered = {}
    pair_len = {}
    adjacency_uncovered = {}
    for u, v, k, d in edges:
        length = float(d.get("length", 0) or 0)
        if length <= 0:
            continue
        ek = _edge_key_v126(u, v, k)
        uncovered[ek] = {"u": u, "v": v, "k": k, "length": length}
        pair = uv_pair(u, v)
        pair_len[pair] = max(pair_len.get(pair, 0.0), length)
        adjacency_uncovered.setdefault(u, set()).add(ek)
        adjacency_uncovered.setdefault(v, set()).add(ek)

    traversed_count = {}
    covered = 0.0
    max_steps = max(120, len(uncovered) * 5)
    steps = 0
    previous = None

    def mark_pair(a, b):
        pair = uv_pair(a, b)
        traversed_count[pair] = traversed_count.get(pair, 0) + 1
        # path上で未配布だったものは消化する
        rem = []
        for ek2, e2 in uncovered.items():
            if uv_pair(e2["u"], e2["v"]) == pair:
                rem.append(ek2)
        gained = 0.0
        for rk in rem:
            e = uncovered.pop(rk, None)
            if e:
                gained += float(e.get("length", 0) or 0)
        return gained

    def incident_uncovered_edges(n):
        out = []
        for ek in list(adjacency_uncovered.get(n, set())):
            if ek in uncovered:
                out.append(ek)
        return out

    def path_repeat_penalty(path):
        if not path or len(path) < 2:
            return 0.0
        pen = 0.0
        for a, b in zip(path[:-1], path[1:]):
            pair = uv_pair(a, b)
            cnt = traversed_count.get(pair, 0)
            if cnt:
                # 1回目の再利用は少し、2回目以降はかなり重くする
                pen += pair_len.get(pair, 8.0) * (3.5 * cnt + 2.0 * max(0, cnt - 1))
        return pen

    def path_length(path):
        if not path or len(path) < 2:
            return 0.0
        total = 0.0
        for a, b in zip(path[:-1], path[1:]):
            pair = uv_pair(a, b)
            total += pair_len.get(pair, 8.0)
        return total

    while uncovered and covered < target_len and steps < max_steps:
        steps += 1

        # 1) 今いる地点から直接未配布枝へ入れるなら、それを最優先。
        local_edges = incident_uncovered_edges(current)
        if local_edges:
            cand = []
            for ek in local_edges:
                e = uncovered.get(ek)
                if not e:
                    continue
                nxt = e["v"] if str(current) == str(e["u"]) else e["u"]
                pair = uv_pair(current, nxt)
                cnt = traversed_count.get(pair, 0)
                # 戻り方向・既通過回数を少し嫌う
                score = cnt * 8.0 + rng.uniform(0, 0.25)
                if previous is not None and str(nxt) == str(previous):
                    score += 4.0
                # 短い枝だけを過剰に拾わない
                score += 1.0 / max(1.0, float(e.get("length", 1.0)))
                cand.append((score, ek, nxt))
            cand.sort(key=lambda x: x[0])
            _score, ek, nxt = cand[0]
            previous = current
            route_nodes.append(nxt)
            gained = mark_pair(current, nxt)
            if ek in uncovered:
                e = uncovered.pop(ek)
                gained += float(e.get("length", 0) or 0)
            covered += gained
            current = nxt
            continue

        # 2) 近くの未配布道路へ道路上で移動。ただし既に何回も通った道を強く嫌う。
        try:
            lengths = nx.single_source_dijkstra_path_length(H, current, weight="length")
        except Exception:
            break
        endpoint_candidates = []
        # 近すぎ/遠すぎを制御。大量候補を全探索しない。
        for ek, e in uncovered.items():
            for tgt in (e["u"], e["v"]):
                d = lengths.get(tgt, 1e18)
                if d >= 1e18:
                    continue
                endpoint_candidates.append((d, ek, tgt, float(e.get("length", 1.0) or 1.0)))
        if not endpoint_candidates:
            break
        endpoint_candidates.sort(key=lambda x: x[0])

        best = None
        best_path = None
        # 近い候補だけでなく、少し先でも反復が少ない候補を選ぶ。
        for d, ek, tgt, elen in endpoint_candidates[:min(90, len(endpoint_candidates))]:
            try:
                path = nx.shortest_path(H, current, tgt, weight="length")
            except Exception:
                continue
            if not path or len(path) < 1:
                continue
            plen = path_length(path)
            repeat = path_repeat_penalty(path)
            # 未配布道路が長いほど少し優先。ただし反復ペナルティを重視。
            score = plen + repeat - min(45.0, elen * 0.35) + rng.uniform(0, 2.0)
            # 前の点へ戻るだけの候補を避ける
            if previous is not None and len(path) >= 2 and str(path[1]) == str(previous):
                score += 35.0
            if best is None or score < best[0]:
                best = (score, ek, tgt)
                best_path = path
        if best is None or best_path is None:
            break

        # 接続路を追加。ここは移動のため、既通過でも仕方ないが、以降の候補でさらに嫌われる。
        for a, b in zip(best_path[:-1], best_path[1:]):
            previous = current
            route_nodes.append(b)
            covered += mark_pair(a, b)
            current = b

        ek, tgt = best[1], best[2]
        if ek in uncovered:
            e = uncovered.pop(ek)
            nxt = e["v"] if str(current) == str(e["u"]) else e["u"]
            previous = current
            route_nodes.append(nxt)
            covered += mark_pair(current, nxt)
            covered += float(e.get("length", 0) or 0)
            current = nxt

    # 連続同一点と極端な局所往復 A-B-A を軽く整理
    cleaned = []
    for n in route_nodes:
        if cleaned and str(cleaned[-1]) == str(n):
            continue
        if len(cleaned) >= 2 and str(cleaned[-2]) == str(n):
            # A-B-A は配布というより無駄往復に見えやすいので基本抑制
            if rng.random() < 0.82:
                cleaned.pop()
                continue
        cleaned.append(n)
    return cleaned




# ==================================================
# v140 ACTIVE OVERRIDES
# ベースはv135へ戻す。
# 追加機能: 指定距離kmに収めるため、重複往復・局所ループを優先削除する。
# ==================================================

APP_VERSION = "app_mansion_photo_v141_v135_base_distance_coverage_balance"


def _distance_prefix_v140(points: Sequence[LatLon]) -> List[float]:
    pref = [0.0]
    for a, b in zip(points[:-1], points[1:]):
        pref.append(pref[-1] + haversine_m(a, b))
    return pref


def _point_key_v140(p: LatLon, grid_m: float = 12.0) -> Tuple[int, int]:
    # 緯度経度をざっくりメートル換算して同じ道路付近の重複検知に使う
    lat, lon = p
    return (int(round(lat * 111320.0 / grid_m)), int(round(lon * 91000.0 / grid_m)))


def _remove_spatial_loops_once_v140(points: List[LatLon], target_m: float, seed: int) -> Tuple[List[LatLon], bool, str]:
    """同じ場所へ戻ってくるだけの無駄な往復を1つ削る。
    町全体を削るのではなく、近距離で戻っている局所ループを優先。
    """
    if len(points) < 60:
        return points, False, "点数不足"
    pref = _distance_prefix_v140(points)
    cur_m = pref[-1]
    if cur_m <= target_m:
        return points, False, "指定距離以内"

    seen: Dict[Tuple[int,int], int] = {}
    candidates = []
    # 先頭/末尾は残す。短すぎるループは消さない。
    for i, p in enumerate(points):
        if i < 15 or i > len(points) - 16:
            continue
        k = _point_key_v140(p, 12.0)
        j = seen.get(k)
        if j is not None and i - j > 18:
            loop_len = pref[i] - pref[j]
            direct = haversine_m(points[j], points[i])
            # 近い場所に戻ってきているのに間が長い＝無駄往復/団子候補
            if loop_len > 80 and direct < 18:
                # 削りすぎるとスカスカになるので、必要超過量に近いものを優先
                overshoot = cur_m - target_m
                score = abs(loop_len - min(max(overshoot, 100), 900)) - loop_len * 0.08
                candidates.append((score, j, i, loop_len, direct))
        else:
            seen[k] = i
    if not candidates:
        return points, False, "削除候補なし"
    candidates.sort(key=lambda x: x[0])
    _score, j, i, loop_len, direct = candidates[0]
    # jとiは同じ場所付近なので、j→iを消しても大ジャンプになりにくい
    new_points = points[:j+1] + points[i:]
    return remove_near_duplicates(new_points, 0.45), True, f"局所重複ループ削除 {loop_len:.0f}m / 接続差 {direct:.1f}m"


def _cap_by_distance_prefix_v140(points: List[LatLon], target_m: float) -> List[LatLon]:
    """最終手段: 指定距離地点で止める。必要なら最後の点を補間する。"""
    if len(points) < 2 or target_m <= 0:
        return points
    out = [points[0]]
    acc = 0.0
    for a, b in zip(points[:-1], points[1:]):
        d = haversine_m(a, b)
        if acc + d < target_m:
            out.append(b)
            acc += d
            continue
        remain = max(0.0, target_m - acc)
        if d > 0.01 and remain > 0.1:
            # a->b の途中で止める。local_xyで補間
            x, y = local_xy(a, b)
            ratio = min(1.0, max(0.0, remain / d))
            out.append(local_ll(a, (x * ratio, y * ratio)))
        break
    return remove_near_duplicates(out, 0.45)


def apply_target_distance_cap_v140(route: Sequence[LatLon], target_km: float, jitter_m: float, seed: int) -> Tuple[List[LatLon], List[str]]:
    """v140: 指定距離に収める。
    1) 指定がなければv135そのまま。
    2) まず局所的な重複往復を削る。
    3) それでも超える場合だけ、末尾を指定距離でカット。
    """
    pts = [tuple(p) for p in route if p is not None]
    logs: List[str] = []
    if len(pts) < 2 or float(target_km) <= 0:
        return pts, logs
    rng = random.Random(int(seed) * 17117 + 140)
    # ユーザー指定の小数2桁は尊重。末尾だけランダムで数m前後。
    jm = max(0.0, float(jitter_m))
    offset = rng.uniform(-jm, jm) if jm > 0 else 0.0
    target_m = max(300.0, float(target_km) * 1000.0 + offset)
    before_m = total_distance_m(pts)
    logs.append(f"指定距離調整: 目標 {target_m/1000:.3f}km（入力 {float(target_km):.2f}km / ランダム {offset:+.1f}m）")
    if before_m <= target_m:
        logs.append(f"指定距離調整: 元距離 {before_m/1000:.2f}km は目標以内のため未カット")
        return pts, logs

    # 局所ループ削除を繰り返す。ただし配布線を消しすぎないよう上限回数を設ける。
    cur = list(pts)
    for n in range(80):
        if total_distance_m(cur) <= target_m:
            break
        cur, changed, msg = _remove_spatial_loops_once_v140(cur, target_m, seed + n)
        if not changed:
            logs.append("指定距離調整: これ以上安全に削れる局所重複がありません")
            break
        if n < 12 or n % 10 == 9:
            logs.append("指定距離調整: " + msg)

    mid_m = total_distance_m(cur)
    if mid_m > target_m:
        # 最終手段。距離指定を守るために末尾をカット。
        cur = _cap_by_distance_prefix_v140(cur, target_m)
        logs.append(f"指定距離調整: 最終カット {mid_m/1000:.2f}km → {total_distance_m(cur)/1000:.2f}km")
    else:
        logs.append(f"指定距離調整: 重複整理で {before_m/1000:.2f}km → {mid_m/1000:.2f}km")
    return remove_near_duplicates(cur, 0.45), logs




# ==================================================
# v141 ACTIVE OVERRIDES
# 目的:
# - v135系の見た目へ戻したまま、指定距離で末尾カットしない。
# - 指定距離がある場合は、各町丁目を途中で切らず、全エリアに均等に配布率調整をかける。
# - 70%を守れる距離なら70%のまま。指定距離と70%が物理的に合わない場合だけ、全体均等に近い配布率へ寄せる。
# ==================================================

APP_VERSION = "app_mansion_photo_v141_v135_base_distance_coverage_balance"


def _target_distance_m_v141(target_km: float, jitter_m: float, seed: int) -> Tuple[float, float]:
    if float(target_km) <= 0:
        return 0.0, 0.0
    rng = random.Random(int(seed) * 19141 + 141)
    jm = max(0.0, float(jitter_m))
    offset = rng.uniform(-jm, jm) if jm > 0 else 0.0
    return max(300.0, float(target_km) * 1000.0 + offset), offset


def _coverage_candidates_v141(base_cov: int, target_m: float, first_m: float) -> List[int]:
    """指定距離に合わせるための配布率候補。
    まず指定配布率を最優先。足りなければ上、長すぎれば下を試す。
    """
    base = int(base_cov)
    vals = [base]
    if target_m <= 0 or first_m <= 0:
        return vals
    # 70%時の距離と目標距離の比率から、近そうな配布率を推定
    est = int(round(base * (target_m / max(first_m, 1.0))))
    est = max(40, min(100, est))
    for d in [0, -5, 5, -10, 10, -15, 15, -20, 20, -25, 25, -30, 30, -35, 35, -40, 40, -45, 45, -50, 50, -55, 55, -60, 60]:
        for v in [est + d, base + d]:
            v = max(40, min(100, int(round(v / 5) * 5)))
            if v not in vals:
                vals.append(v)
    # baseから離れすぎる候補は後ろへ
    vals = sorted(set(vals), key=lambda x: (0 if x == base else 1, abs(x - est), abs(x - base)))
    return vals[:13]


def _score_route_for_target_v141(dist_m: float, target_m: float, cov_try: int, requested_cov: int) -> float:
    """距離だけではなく、指定配布率から離れすぎないように採点。"""
    if target_m <= 0:
        return abs(cov_try - requested_cov)
    dist_err = abs(dist_m - target_m)
    # 配布率を1%落とす/上げることに約70mぶんのペナルティを置く。
    # これにより、距離だけ合わせるために70%から極端に離れるのを防ぐ。
    cov_pen = abs(int(cov_try) - int(requested_cov)) * 70.0
    # 目標超過は時間が伸びるので少し重くする。ただし末尾カットはしない。
    over_pen = max(0.0, dist_m - target_m) * 0.35
    return dist_err + cov_pen + over_pen


def _safe_local_loop_cleanup_v141(points: Sequence[LatLon], max_passes: int = 18) -> List[LatLon]:
    """局所的な団子だけを軽く削る。町全体や末尾は絶対に切らない。"""
    cur = [tuple(p) for p in points if p is not None]
    for n in range(max_passes):
        if len(cur) < 80:
            break
        pref = _distance_prefix_v140(cur)
        seen: Dict[Tuple[int,int], int] = {}
        cand = []
        for i, p in enumerate(cur):
            if i < 20 or i > len(cur) - 20:
                continue
            k = _point_key_v140(p, 9.0)
            j = seen.get(k)
            if j is None:
                seen[k] = i
                continue
            if i - j < 18:
                continue
            loop_len = pref[i] - pref[j]
            direct = haversine_m(cur[j], cur[i])
            # 近くに戻っているのに長く回っている小さい団子だけ対象。
            # ここを強くしすぎるとまたスカスカになるので控えめ。
            if 90.0 <= loop_len <= 520.0 and direct <= 13.0:
                cand.append((loop_len, j, i, direct))
        if not cand:
            break
        # 短い団子から削る。大きな配布ブロックは消さない。
        cand.sort(key=lambda x: x[0])
        _loop_len, j, i, _direct = cand[0]
        cur = cur[:j+1] + cur[i:]
        cur = remove_near_duplicates(cur, 0.45)
    return cur


def build_route_distance_coverage_balance_v141(
    boundary_polys: Sequence[Sequence[LatLon]],
    pins: Sequence[LatLon],
    density: float,
    pin_radius_m: float,
    seed: int,
    distance_mode: str,
    coverage_pct: int,
    target_distance_km: float,
    target_jitter_m: float,
    progress=None,
) -> Tuple[List[LatLon], List[str]]:
    """v141: 指定距離で末尾カットしない生成。
    距離指定なし: v135/v140ベースでそのまま生成。
    距離指定あり: まず指定配布率で全エリア生成し、長さが合わない時だけ配布率候補を全エリア均等に変えて再生成。
    """
    logs: List[str] = []
    target_m, offset_m = _target_distance_m_v141(target_distance_km, target_jitter_m, seed)
    requested_cov = int(coverage_pct)

    if target_m <= 0:
        if progress:
            progress.progress(45, text="距離指定なし: 指定配布率で生成中...")
        route, logs0 = build_pre_pin_route_v118(
            boundary_polys, pins,
            density=float(density), pin_radius_m=float(pin_radius_m), seed=int(seed),
            distance_mode=distance_mode, coverage_pct=requested_cov,
        )
        return route, logs0 + ["v141: 距離指定なしのため、指定配布率をそのまま使用"]

    logs.append(f"v141距離指定: 入力 {float(target_distance_km):.2f}km / ランダム {offset_m:+.1f}m / 目標 {target_m/1000:.3f}km")
    logs.append("v141方針: 末尾カット禁止。全エリアを途中で切らず、必要な場合だけ配布率を全エリア均等に調整します。")

    # まず指定配布率そのものを試す
    if progress:
        progress.progress(24, text=f"まず指定配布率{requested_cov}%で生成中...")
    base_route, base_logs = build_pre_pin_route_v118(
        boundary_polys, pins,
        density=float(density), pin_radius_m=float(pin_radius_m), seed=int(seed),
        distance_mode=distance_mode, coverage_pct=requested_cov,
    )
    base_route = _safe_local_loop_cleanup_v141(base_route, max_passes=10)
    base_m = total_distance_m(base_route) if base_route else 0.0
    logs.append(f"指定配布率{requested_cov}%で生成: {base_m/1000:.2f}km / {len(base_route)}点")

    # 目標±3%か±350m以内なら配布率優先で採用
    tolerance = max(350.0, target_m * 0.03)
    if base_route and abs(base_m - target_m) <= tolerance:
        logs.extend(["採用: 指定配布率を維持し、距離も許容範囲内"] + base_logs[:18])
        return base_route, logs

    candidates = _coverage_candidates_v141(requested_cov, target_m, base_m)
    best_route = base_route
    best_logs = base_logs
    best_cov = requested_cov
    best_m = base_m
    best_score = _score_route_for_target_v141(base_m, target_m, requested_cov, requested_cov) if base_route else 10**18

    tried = {requested_cov}
    for idx, cov in enumerate(candidates):
        if cov in tried:
            continue
        tried.add(cov)
        if progress:
            pct = min(88, 30 + idx * 5)
            progress.progress(pct, text=f"距離に近い配布率候補 {cov}% を試行中...")
        route, logs_try = build_pre_pin_route_v118(
            boundary_polys, pins,
            density=float(density), pin_radius_m=float(pin_radius_m), seed=int(seed) + cov * 17,
            distance_mode=distance_mode, coverage_pct=int(cov),
        )
        if not route or len(route) < 2:
            logs.append(f"試行 {cov}%: 生成失敗")
            continue
        route = _safe_local_loop_cleanup_v141(route, max_passes=10)
        dist_m = total_distance_m(route)
        score = _score_route_for_target_v141(dist_m, target_m, int(cov), requested_cov)
        logs.append(f"試行 {cov}%: {dist_m/1000:.2f}km / 目標差 {(dist_m-target_m)/1000:+.2f}km / score {score:.0f}")
        if score < best_score:
            best_route, best_logs, best_cov, best_m, best_score = route, logs_try, int(cov), dist_m, score

    if not best_route:
        return [], logs + ["v141: 距離・配布率バランス生成に失敗しました。"]

    # 最後も末尾カットはしない。距離と配布率のどちらを優先したかログに明示。
    diff_m = best_m - target_m
    if best_cov == requested_cov:
        logs.append(f"採用: 指定配布率{requested_cov}%を維持 / 距離 {best_m/1000:.2f}km（目標差 {diff_m/1000:+.2f}km）")
    else:
        logs.append(f"採用: 距離優先のため全エリア均等に {requested_cov}% → {best_cov}% へ調整 / 距離 {best_m/1000:.2f}km（目標差 {diff_m/1000:+.2f}km）")
        logs.append("注意: 指定距離と指定配布率が同時に成立しない場合は、末尾カットではなく全エリア均等調整にしています。")
    logs.extend(best_logs[:22])
    return best_route, logs


# v140の末尾カット関数は残すが、v141のmainからは呼ばない。

# ==================================================
# v148 ACTIVE OVERRIDES - v141 base / long same-road return guard
# 重要:
# - v141の配布率・距離・ピン処理・GPS揺れは変えない。
# - 生成後に「一本道を行って戻るだけ」「同じ細長い道路を何度もなぞる」部分だけを検査して削る。
# - 70/80/90/100% の変化は v141 の道路選択へ任せる。ここでは配布率を再計算しない。
# ==================================================

APP_VERSION = "app_mansion_photo_v148_v141_base_corridor_return_guard_verified"


def _v148_distance_prefix(points: Sequence[LatLon]) -> List[float]:
    pref = [0.0]
    for a, b in zip(points[:-1], points[1:]):
        pref.append(pref[-1] + haversine_m(a, b))
    return pref


def _v148_interp_by_prefix(points: Sequence[LatLon], pref: Sequence[float], s: float) -> LatLon:
    if not points:
        return (0.0, 0.0)
    if s <= 0:
        return points[0]
    if s >= pref[-1]:
        return points[-1]
    lo, hi = 0, len(pref) - 1
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if pref[mid] <= s:
            lo = mid
        else:
            hi = mid
    span = max(0.001, pref[hi] - pref[lo])
    t = (s - pref[lo]) / span
    return lerp(points[lo], points[hi], t)


def _v148_mirror_return_score(points: Sequence[LatLon], pref: Sequence[float], j: int, i: int, samples: int = 15) -> Tuple[float, float]:
    """j..i が同じ道を往復しているかを、前半と後半の鏡写し距離で判定。"""
    a, b = pref[j], pref[i]
    if b <= a:
        return 1e9, 1e9
    dists = []
    # 端点は交差点で近いのが当然なので少し内側を多めに見る
    for n in range(1, samples + 1):
        f = n / (samples + 1)
        p1 = _v148_interp_by_prefix(points, pref, a + (b - a) * f)
        p2 = _v148_interp_by_prefix(points, pref, b - (b - a) * f)
        dists.append(haversine_m(p1, p2))
    if not dists:
        return 1e9, 1e9
    return sum(dists) / len(dists), max(dists)


def _v148_thinness(points: Sequence[LatLon], j: int, i: int) -> Tuple[float, float]:
    """区間j..iの長さ方向/幅方向をざっくり測る。細長い往復だけを削るため。"""
    seg = list(points[j:i+1])
    if len(seg) < 4:
        return 0.0, 0.0
    origin = seg[0]
    xy = [local_xy(origin, p) for p in seg]
    mx = sum(x for x, y in xy) / len(xy)
    my = sum(y for x, y in xy) / len(xy)
    xx = sum((x-mx)*(x-mx) for x, y in xy) / len(xy)
    yy = sum((y-my)*(y-my) for x, y in xy) / len(xy)
    xyv = sum((x-mx)*(y-my) for x, y in xy) / len(xy)
    # 主成分方向
    if abs(xyv) < 1e-9 and abs(xx-yy) < 1e-9:
        vx, vy = 1.0, 0.0
    else:
        ang = 0.5 * math.atan2(2*xyv, xx-yy)
        vx, vy = math.cos(ang), math.sin(ang)
    nx, ny = -vy, vx
    along = [x*vx + y*vy for x, y in xy]
    across = [x*nx + y*ny for x, y in xy]
    return (max(along)-min(along), max(across)-min(across))


def _v148_point_key(p: LatLon, origin: LatLon, cell_m: float = 13.0) -> Tuple[int, int]:
    x, y = local_xy(origin, p)
    return (int(round(x / cell_m)), int(round(y / cell_m)))


def _v148_remove_long_same_road_returns(points: Sequence[LatLon], max_passes: int = 30) -> Tuple[List[LatLon], List[str]]:
    """長い一本道往復を消す。

    判定条件を複数重ねて、住宅街の普通の面ループは残し、
    「行って戻るだけ」の細長い戻りだけを削る。
    """
    cur: List[LatLon] = [tuple(p) for p in points if p is not None]
    logs: List[str] = []
    if len(cur) < 60:
        return cur, logs

    removed_total_m = 0.0
    removed_count = 0
    for _pass in range(int(max_passes)):
        if len(cur) < 60:
            break
        pref = _v148_distance_prefix(cur)
        if pref[-1] < 300:
            break
        origin = cur[0]
        seen: Dict[Tuple[int, int], List[int]] = {}
        best = None
        # 少し間引いて探索。削除位置は点列そのものを使うのでGPS揺れは作り直さない。
        step_i = 3
        for i in range(18, len(cur) - 18, step_i):
            k = _v148_point_key(cur[i], origin, 14.0)
            prevs = seen.get(k, [])
            for j in prevs[-8:]:
                if i - j < 24:
                    continue
                loop_len = pref[i] - pref[j]
                if loop_len < 115.0 or loop_len > 2400.0:
                    continue
                close = haversine_m(cur[j], cur[i])
                if close > 28.0:
                    continue
                avg_mirror, max_mirror = _v148_mirror_return_score(cur, pref, j, i, samples=13)
                along, width = _v148_thinness(cur, j, i)
                # 本当に同じ道を戻っている時は、鏡写し距離が小さく、形も細長い。
                mirror_ok = (avg_mirror <= 24.0 and max_mirror <= 62.0)
                thin_ok = (along >= 55.0 and width <= max(32.0, along * 0.34))
                # 幅がかなり細いものは鏡写しが多少荒くても削る。
                very_thin_ok = (along >= 90.0 and width <= 24.0 and avg_mirror <= 34.0)
                if not ((mirror_ok and thin_ok) or very_thin_ok):
                    continue
                # 長いものを優先的に削る。短い住宅街の小戻りは残りやすくする。
                score = loop_len - width * 3.0 - avg_mirror * 2.0
                if best is None or score > best[0]:
                    best = (score, j, i, loop_len, close, avg_mirror, max_mirror, along, width)
            seen.setdefault(k, []).append(i)
        if best is None:
            break
        _score, j, i, loop_len, close, avg_mirror, max_mirror, along, width = best
        before_n = len(cur)
        # j と i は近接しているので、間を削っても大ジャンプにならない。
        cur = cur[:j+1] + cur[i:]
        cur = remove_near_duplicates(cur, 0.45)
        removed_total_m += loop_len
        removed_count += 1
        logs.append(
            f"v148一本道往復削除{removed_count}: {loop_len:.0f}m / 幅{width:.1f}m / 鏡平均{avg_mirror:.1f}m / 点 {before_n}->{len(cur)}"
        )
    if removed_count:
        logs.append(f"v148一本道往復削除合計: {removed_count}箇所 / 約{removed_total_m/1000:.2f}kmを整理")
    return cur, logs


def _v148_repeated_edge_report(points: Sequence[LatLon], cell_m: float = 12.0) -> Tuple[int, int, float]:
    """検査用: 同じ粗い道路片を何度も通っていないか数える。"""
    if len(points) < 2:
        return 0, 0, 0.0
    origin = points[0]
    counts: Dict[Tuple[Tuple[int,int], Tuple[int,int]], int] = {}
    dist_by_key: Dict[Tuple[Tuple[int,int], Tuple[int,int]], float] = {}
    for a, b in zip(points[:-1], points[1:]):
        ka = _v148_point_key(a, origin, cell_m)
        kb = _v148_point_key(b, origin, cell_m)
        if ka == kb:
            continue
        key = tuple(sorted((ka, kb)))  # 方向を無視。往復も同一道路扱い。
        counts[key] = counts.get(key, 0) + 1
        dist_by_key[key] = dist_by_key.get(key, 0.0) + haversine_m(a, b)
    repeated_keys = sum(1 for k, c in counts.items() if c >= 3)
    heavy_keys = sum(1 for k, c in counts.items() if c >= 4)
    repeated_m = sum(dist_by_key[k] for k, c in counts.items() if c >= 3)
    return repeated_keys, heavy_keys, repeated_m


# v141の軽い団子掃除を残したうえで、v148の一本道往復掃除を必ず通す。
_v141_original_safe_local_loop_cleanup = _safe_local_loop_cleanup_v141

def _safe_local_loop_cleanup_v141(points: Sequence[LatLon], max_passes: int = 18) -> List[LatLon]:
    cur = _v141_original_safe_local_loop_cleanup(points, max_passes=max_passes)
    cur2, _logs = _v148_remove_long_same_road_returns(cur, max_passes=30)
    return remove_near_duplicates(cur2, 0.45)


_v141_original_build_route_distance_coverage_balance = build_route_distance_coverage_balance_v141

def build_route_distance_coverage_balance_v141(
    boundary_polys: Sequence[Sequence[LatLon]],
    pins: Sequence[LatLon],
    density: float,
    pin_radius_m: float,
    seed: int,
    distance_mode: str,
    coverage_pct: int,
    target_distance_km: float,
    target_jitter_m: float,
    progress=None,
) -> Tuple[List[LatLon], List[str]]:
    """v148 wrapper.

    v141本体で配布率・距離・ピン・揺れを作ったあと、
    距離指定なしの場合も含めて一本道往復だけを最終検査する。
    """
    route, logs = _v141_original_build_route_distance_coverage_balance(
        boundary_polys, pins, density, pin_radius_m, seed, distance_mode,
        coverage_pct, target_distance_km, target_jitter_m, progress=progress,
    )
    if not route or len(route) < 2:
        return route, logs
    before_m = total_distance_m(route)
    before_rep = _v148_repeated_edge_report(route)
    cleaned, clean_logs = _v148_remove_long_same_road_returns(route, max_passes=36)
    cleaned = remove_near_duplicates(cleaned, 0.45)
    after_m = total_distance_m(cleaned) if cleaned else 0.0
    after_rep = _v148_repeated_edge_report(cleaned) if cleaned else (0, 0, 0.0)
    logs = list(logs)
    logs.append(
        f"v148検査: 粗い同一道路片の重複 keys {before_rep[0]}→{after_rep[0]} / heavy {before_rep[1]}→{after_rep[1]} / 距離 {before_m/1000:.2f}→{after_m/1000:.2f}km"
    )
    logs.extend(clean_logs)
    logs.append("v148方針: 配布率・GPS揺れ・ピン処理はv141を維持し、一本道往復の後処理だけ実行")
    return cleaned, logs


# GPX内表記もv148に固定して、古い版で生成したように見えないようにする。
def make_gpx_single_route_v118(points: Sequence[LatLon], start_time: _dt.datetime, speed_kmh: float, stop_total_min: float = 0.0, stop_count: int = 0) -> str:
    gpx = ET.Element("gpx", version="1.1", creator="ChatGPT v148 v141_base_corridor_return_guard", xmlns="http://www.topografix.com/GPX/1/1")
    trk = ET.SubElement(gpx, "trk")
    ET.SubElement(trk, "name").text = "posting_route_v148"
    trkseg = ET.SubElement(trk, "trkseg")
    current = start_time
    speed_mps = max(speed_kmh / 3.6, 0.3)
    rng = random.Random(int(start_time.timestamp()) ^ 148123)
    stop_count = int(max(0, stop_count))
    stop_total_sec = max(0.0, float(stop_total_min) * 60.0)
    stop_indices = set()
    if stop_count > 0 and len(points) > 20:
        candidates = list(range(10, len(points)-10))
        rng.shuffle(candidates)
        stop_indices = set(sorted(candidates[:min(stop_count, len(candidates))]))
    each_stop = stop_total_sec / max(stop_count, 1) if stop_count else 0.0
    prev = None
    for idx, p in enumerate(points):
        if prev is not None:
            current += _dt.timedelta(seconds=haversine_m(prev, p) / speed_mps)
        if idx in stop_indices:
            jitter = rng.uniform(-0.18, 0.18) * each_stop
            current += _dt.timedelta(seconds=max(10, each_stop + jitter))
        trkpt = ET.SubElement(trkseg, "trkpt", lat=f"{p[0]:.8f}", lon=f"{p[1]:.8f}")
        ET.SubElement(trkpt, "ele").text = "3.0"
        ET.SubElement(trkpt, "time").text = format_gpx_time(current)
        prev = p
    return ET.tostring(gpx, encoding="utf-8", xml_declaration=True).decode("utf-8")


def make_gpx(segments: Sequence[Sequence[LatLon]], start_time: _dt.datetime, speed_kmh: float, stop_total_min: float = 0.0) -> str:
    pts: List[LatLon] = []
    for seg in segments:
        pts.extend(list(seg))
    return make_gpx_single_route_v118(pts, start_time, speed_kmh, stop_total_min=stop_total_min, stop_count=0)


# Streamlitの既定ダウンロード名をv148にする。既存セッションの入力欄に古い名前が残る場合は画面上で変更してください。
try:
    DEFAULT_GPX_FILENAME_V148 = "posting_route_v148.gpx"
except Exception:
    pass


# ==================================================
# v150 ACTIVE OVERRIDE
# 目的:
# - v148の配布率・GPSブレ・ピン処理・一本道往復クリーナーは維持
# - 「家側へちょんと入る」配布入り込みだけを強化
# - 全部を深くせず、約半分は従来の浅いチョン、約半分は少し奥まで入るチョンにする
# ==================================================

def add_posting_spurs_v135(points: Sequence[LatLon], seed: int, density: float = 1.0, max_spur_m: float = 7.5) -> List[LatLon]:
    """v150: 配布中の短い建物寄り入り込みを、浅いもの/深いものの混在にする。

    重要:
    - v148の道路選択・配布率・一本道往復削除は触らない
    - GPSブレ本体 wiggle_polyline は触らない
    - ちょん入りの発生頻度は大きく増やさず、深さだけを約半数で伸ばす
    - 深い入り込みでも大ジャンプに見えないよう、中間点を増やして戻す
    """
    pts = [tuple(p) for p in points if p is not None]
    if len(pts) < 6:
        return pts

    rng = random.Random(seed * 9176 + 150)
    out: List[LatLon] = [pts[0]]
    dist_since = 0.0
    next_spur = rng.uniform(34.0, 78.0) / max(0.35, density)

    for i in range(1, len(pts) - 1):
        prev_p, p, next_p = pts[i - 1], pts[i], pts[i + 1]
        out.append(p)
        step_d = haversine_m(prev_p, p)
        dist_since += step_d

        # 発生間隔はv148相当。ここを増やしすぎると70%の見た目が濃くなりすぎる。
        if dist_since < next_spur:
            continue
        if rng.random() > 0.62:
            dist_since = 0.0
            next_spur = rng.uniform(30.0, 85.0) / max(0.35, density)
            continue

        origin = p
        x1, y1 = local_xy(origin, prev_p)
        x2, y2 = local_xy(origin, next_p)
        vx, vy = x2 - x1, y2 - y1
        norm = math.hypot(vx, vy)
        if norm < 1.5:
            continue
        ux, uy = vx / norm, vy / norm
        nxv, nyv = -uy, ux

        side = rng.choice([-1.0, 1.0])

        # 約半分は従来の浅いチョン、約半分は少し奥へ入るチョン。
        # max_spur_mは呼び出し元により5〜8m前後なので、深い側だけ上限を別に持たせる。
        deep = rng.random() < 0.50
        if deep:
            # 住宅の敷地側へ「もう一歩入った」ように見える深さ。
            # 深すぎると家の中へ飛び込む/不自然な三角になるので上限は抑える。
            depth = rng.uniform(max(6.8, max_spur_m * 0.95), max(9.5, max_spur_m * 1.85))
            if rng.random() < 0.22:
                depth *= rng.uniform(1.05, 1.22)
            depth = min(depth, 14.8)
            # 深いチョンは前後方向にも少し流して、単純な横突き刺しにしない。
            along = rng.uniform(-2.0, 3.4)
            shoulder = rng.uniform(0.38, 0.58)
            tip_back = rng.uniform(0.70, 0.86)
        else:
            depth = rng.uniform(2.8, max_spur_m)
            if rng.random() < 0.18:
                depth *= rng.uniform(1.15, 1.55)
            depth = min(depth, 11.5)
            along = rng.uniform(-1.4, 2.2)
            shoulder = rng.uniform(0.50, 0.64)
            tip_back = rng.uniform(0.62, 0.78)

        # p -> 肩 -> 奥 -> 戻り途中 -> 道路方向へ戻る
        # 深い場合だけ中間点を1つ増やし、点間の飛びを減らす。
        spur1 = local_ll(origin, (nxv * side * depth * shoulder + ux * along * 0.35,
                                  nyv * side * depth * shoulder + uy * along * 0.35))
        spur2 = local_ll(origin, (nxv * side * depth + ux * along,
                                  nyv * side * depth + uy * along))
        spur3 = local_ll(origin, (nxv * side * depth * tip_back + ux * (along + rng.uniform(0.8, 2.4)),
                                  nyv * side * depth * tip_back + uy * (along + rng.uniform(0.8, 2.4))))
        back = local_ll(origin, (ux * rng.uniform(1.2, 3.4),
                                 uy * rng.uniform(1.2, 3.4)))

        if deep:
            out.extend([spur1, spur2, spur3, back])
        else:
            out.extend([spur1, spur2, back])

        dist_since = 0.0
        next_spur = rng.uniform(36.0, 92.0) / max(0.35, density)

    out.append(pts[-1])
    return remove_near_duplicates(out, 0.45)


# GPX内表記だけv150に更新。ルート生成ベースはv148のまま。
def make_gpx_single_route_v118(points: Sequence[LatLon], start_time: _dt.datetime, speed_kmh: float, stop_total_min: float = 0.0, stop_count: int = 0) -> str:
    gpx = ET.Element("gpx", version="1.1", creator="ChatGPT v150 v148_base_deeper_posting_spurs", xmlns="http://www.topografix.com/GPX/1/1")
    trk = ET.SubElement(gpx, "trk")
    ET.SubElement(trk, "name").text = "posting_route_v150"
    trkseg = ET.SubElement(trk, "trkseg")
    current = start_time
    speed_mps = max(speed_kmh / 3.6, 0.3)
    rng = random.Random(int(start_time.timestamp()) ^ 150123)
    stop_count = int(max(0, stop_count))
    stop_total_sec = max(0.0, float(stop_total_min) * 60.0)
    stop_indices = set()
    if stop_count > 0 and len(points) > 20:
        candidates = list(range(10, len(points)-10))
        rng.shuffle(candidates)
        stop_indices = set(sorted(candidates[:min(stop_count, len(candidates))]))
    each_stop = stop_total_sec / max(stop_count, 1) if stop_count else 0.0
    prev = None
    for idx, p in enumerate(points):
        if prev is not None:
            current += _dt.timedelta(seconds=haversine_m(prev, p) / speed_mps)
        if idx in stop_indices:
            jitter = rng.uniform(-0.18, 0.18) * each_stop
            current += _dt.timedelta(seconds=max(10, each_stop + jitter))
        trkpt = ET.SubElement(trkseg, "trkpt", lat=f"{p[0]:.8f}", lon=f"{p[1]:.8f}")
        ET.SubElement(trkpt, "ele").text = "3.0"
        ET.SubElement(trkpt, "time").text = format_gpx_time(current)
        prev = p
    return ET.tostring(gpx, encoding="utf-8", xml_declaration=True).decode("utf-8")


def make_gpx(segments: Sequence[Sequence[LatLon]], start_time: _dt.datetime, speed_kmh: float, stop_total_min: float = 0.0) -> str:
    pts: List[LatLon] = []
    for seg in segments:
        pts.extend(list(seg))
    return make_gpx_single_route_v118(pts, start_time, speed_kmh, stop_total_min=stop_total_min, stop_count=0)

try:
    DEFAULT_GPX_FILENAME_V148 = "posting_route_v150.gpx"
except Exception:
    pass


# ==================================================
# v151 ACTIVE OVERRIDE
# 公園・学校など、配布しないと判定できる面にはチョン入りを出さない。
# ベースはv150。配布率/距離/ピン/一本道往復/GPSブレの既存処理は変えず、
# add_posting_spurs_v135 のチョン方向選択だけに no-spur-zone 判定を加える。
# ==================================================

NO_SPUR_CACHE_TTL_SEC_V151 = 60 * 60 * 12

@st.cache_data(show_spinner=False, ttl=NO_SPUR_CACHE_TTL_SEC_V151)
def overpass_no_spur_zones_v151(minlat: float, minlon: float, maxlat: float, maxlon: float) -> List[List[LatLon]]:
    """公園・学校など、ポスティングのチョン入りを出さない面をOSMから取得する。

    取得できない場合は空で返す。判定不能なら従来通りランダムにチョン入りする。
    """
    if requests is None:
        return []
    q = f"""
    [out:json][timeout:35];
    (
      way["leisure"~"^(park|playground|recreation_ground|sports_centre|pitch|garden)$"]({minlat},{minlon},{maxlat},{maxlon});
      way["amenity"~"^(school|kindergarten|university|college)$"]({minlat},{minlon},{maxlat},{maxlon});
      way["landuse"~"^(education|recreation_ground)$"]({minlat},{minlon},{maxlat},{maxlon});
    );
    out tags geom;
    """
    endpoints = [
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://overpass.openstreetmap.ru/api/interpreter",
    ]
    data = None
    for url in endpoints:
        try:
            r = requests.post(url, data={"data": q}, timeout=45, headers={"User-Agent": "posting-route-builder-v151/1.0"})
            r.raise_for_status()
            data = r.json()
            break
        except Exception:
            data = None
            continue
    if not data:
        return []
    zones: List[List[LatLon]] = []
    for el in data.get("elements", []):
        geom = el.get("geometry") or []
        pts = [(float(g["lat"]), float(g["lon"])) for g in geom if "lat" in g and "lon" in g]
        if len(pts) >= 4:
            # 閉じていないwayもpolygon扱いにできるよう閉じる
            if haversine_m(pts[0], pts[-1]) > 2.0:
                pts.append(pts[0])
            # あまり巨大な公園/学校面を誤取得しても、点内判定だけなので保持
            zones.append(pts)
    return zones


def _no_spur_zones_for_points_v151(points: Sequence[LatLon]) -> List[Any]:
    """ルート周辺の公園/学校ポリゴンをshapely化。失敗時は空。"""
    if not points or Polygon is None:
        return []
    try:
        minlat = min(p[0] for p in points); maxlat = max(p[0] for p in points)
        minlon = min(p[1] for p in points); maxlon = max(p[1] for p in points)
        minlat, minlon, maxlat, maxlon = _bbox_expand((minlat, minlon, maxlat, maxlon), 70.0)
        raw = overpass_no_spur_zones_v151(round(minlat, 6), round(minlon, 6), round(maxlat, 6), round(maxlon, 6))
        zones = []
        for z in raw:
            try:
                poly = Polygon([(lon, lat) for lat, lon in z]).buffer(0)
                if not poly.is_empty:
                    # 道路際の境界ブレ対策でほんの少しだけ膨らませる。緩くしすぎない。
                    zones.append(poly.buffer(0.000012))
            except Exception:
                continue
        return zones
    except Exception:
        return []


def _point_in_no_spur_zone_v151(p: LatLon, zones: Sequence[Any]) -> bool:
    if not zones or Point is None:
        return False
    try:
        pt = Point(p[1], p[0])
        for z in zones:
            try:
                if z.contains(pt) or z.touches(pt):
                    return True
            except Exception:
                continue
    except Exception:
        return False
    return False


def add_posting_spurs_v135(points: Sequence[LatLon], seed: int, density: float = 1.0, max_spur_m: float = 7.5) -> List[LatLon]:
    """v151: v150の深めチョン入りを維持しつつ、公園/学校側には出さない。

    - 公園/学校とOSMで判定できる側は避ける
    - 片側だけNGなら反対側へ出す
    - 両側NGならチョン自体をスキップ
    - 判定できない場所はv150同様ランダム
    """
    pts = list(points)
    if len(pts) < 4:
        return pts

    no_spur_zones = _no_spur_zones_for_points_v151(pts)

    rng = random.Random(seed + 150150)
    out: List[LatLon] = [pts[0]]
    dist_since = 0.0
    next_spur = rng.uniform(34.0, 78.0) / max(0.35, density)
    skipped_no_spur = 0

    for i in range(1, len(pts) - 1):
        prev_p, p, next_p = pts[i - 1], pts[i], pts[i + 1]
        out.append(p)
        step_d = haversine_m(prev_p, p)
        dist_since += step_d

        # 発生頻度はv150相当。ここは増やさない。
        if dist_since < next_spur:
            continue
        if rng.random() > 0.62:
            dist_since = 0.0
            next_spur = rng.uniform(30.0, 85.0) / max(0.35, density)
            continue

        origin = p
        x1, y1 = local_xy(origin, prev_p)
        x2, y2 = local_xy(origin, next_p)
        vx, vy = x2 - x1, y2 - y1
        norm = math.hypot(vx, vy)
        if norm < 1.5:
            continue
        ux, uy = vx / norm, vy / norm
        nxv, nyv = -uy, ux

        # 約半分は浅いチョン、約半分は少し奥へ入るチョン。
        deep = rng.random() < 0.50
        if deep:
            depth = rng.uniform(max(6.8, max_spur_m * 0.95), max(9.5, max_spur_m * 1.85))
            if rng.random() < 0.22:
                depth *= rng.uniform(1.05, 1.22)
            depth = min(depth, 14.8)
            along = rng.uniform(-2.0, 3.4)
            shoulder = rng.uniform(0.38, 0.58)
            tip_back = rng.uniform(0.70, 0.86)
        else:
            depth = rng.uniform(2.8, max_spur_m)
            if rng.random() < 0.18:
                depth *= rng.uniform(1.15, 1.55)
            depth = min(depth, 11.5)
            along = rng.uniform(-1.4, 2.2)
            shoulder = rng.uniform(0.50, 0.64)
            tip_back = rng.uniform(0.62, 0.78)

        def build_spur(side: float):
            spur1 = local_ll(origin, (nxv * side * depth * shoulder + ux * along * 0.35,
                                      nyv * side * depth * shoulder + uy * along * 0.35))
            spur2 = local_ll(origin, (nxv * side * depth + ux * along,
                                      nyv * side * depth + uy * along))
            spur3 = local_ll(origin, (nxv * side * depth * tip_back + ux * (along + rng.uniform(0.8, 2.4)),
                                      nyv * side * depth * tip_back + uy * (along + rng.uniform(0.8, 2.4))))
            back = local_ll(origin, (ux * rng.uniform(1.2, 3.4),
                                     uy * rng.uniform(1.2, 3.4)))
            return spur1, spur2, spur3, back

        # まず左右どちらの先端が公園/学校側に入るかを見る。
        # 先端だけでなく肩も見て、境界沿いの誤突入を減らす。
        candidate_sides = [-1.0, 1.0]
        rng.shuffle(candidate_sides)
        chosen = None
        for side in candidate_sides:
            spur1, spur2, spur3, back = build_spur(side)
            if _point_in_no_spur_zone_v151(spur2, no_spur_zones) or _point_in_no_spur_zone_v151(spur1, no_spur_zones):
                continue
            chosen = (spur1, spur2, spur3, back)
            break

        if chosen is None:
            # 両側が公園/学校判定、または境界内へ入る場合はチョンを作らない。
            skipped_no_spur += 1
            dist_since = 0.0
            next_spur = rng.uniform(36.0, 92.0) / max(0.35, density)
            continue

        spur1, spur2, spur3, back = chosen
        if deep:
            out.extend([spur1, spur2, spur3, back])
        else:
            out.extend([spur1, spur2, back])

        dist_since = 0.0
        next_spur = rng.uniform(36.0, 92.0) / max(0.35, density)

    out.append(pts[-1])
    return remove_near_duplicates(out, 0.45)


# GPX内表記だけv151に更新。ルート生成ベースはv150/v148のまま。
def make_gpx_single_route_v118(points: Sequence[LatLon], start_time: _dt.datetime, speed_kmh: float, stop_total_min: float = 0.0, stop_count: int = 0) -> str:
    gpx = ET.Element("gpx", version="1.1", creator="ChatGPT v153 v152_base_effective_average_speed", xmlns="http://www.topografix.com/GPX/1/1")
    trk = ET.SubElement(gpx, "trk")
    ET.SubElement(trk, "name").text = "posting_route_v153"
    trkseg = ET.SubElement(trk, "trkseg")
    current = start_time
    speed_mps = max(speed_kmh / 3.6, 0.3)
    rng = random.Random(int(start_time.timestamp()) ^ 151123)
    stop_count = int(max(0, stop_count))
    stop_total_sec = max(0.0, float(stop_total_min) * 60.0)
    stop_indices = set()
    if stop_count > 0 and len(points) > 20:
        candidates = list(range(10, len(points)-10))
        rng.shuffle(candidates)
        stop_indices = set(sorted(candidates[:min(stop_count, len(candidates))]))
    each_stop = stop_total_sec / max(stop_count, 1) if stop_count else 0.0
    prev = None
    for idx, p in enumerate(points):
        if prev is not None:
            current += _dt.timedelta(seconds=haversine_m(prev, p) / speed_mps)
        if idx in stop_indices:
            jitter = rng.uniform(-0.18, 0.18) * each_stop
            current += _dt.timedelta(seconds=max(10, each_stop + jitter))
        trkpt = ET.SubElement(trkseg, "trkpt", lat=f"{p[0]:.8f}", lon=f"{p[1]:.8f}")
        ET.SubElement(trkpt, "ele").text = "3.0"
        ET.SubElement(trkpt, "time").text = format_gpx_time(current)
        prev = p
    return ET.tostring(gpx, encoding="utf-8", xml_declaration=True).decode("utf-8")


def make_gpx(segments: Sequence[Sequence[LatLon]], start_time: _dt.datetime, speed_kmh: float, stop_total_min: float = 0.0) -> str:
    pts: List[LatLon] = []
    for seg in segments:
        pts.extend(list(seg))
    return make_gpx_single_route_v118(pts, start_time, speed_kmh, stop_total_min=stop_total_min, stop_count=0)

try:
    DEFAULT_GPX_FILENAME_V148 = "posting_route_v153.gpx"
except Exception:
    pass


# ==================================================
# v153 ACTIVE OVERRIDE（v152ベース + 停止込み平均速度表示）
# 町丁目の回る順番モード
# - v151の配布率/距離/GPSブレ/チョン/ピン/公園学校回避は変更しない
# - 複数町丁目を「選択した順」または「最初の町を固定した近い順」で生成に渡す
# ==================================================

def _boundary_items_for_order_v152(polys: Sequence[Sequence[LatLon]]) -> List[Dict[str, Any]]:
    """現在登録済みの配布範囲を、順番制御用に取り出す。"""
    items: List[Dict[str, Any]] = []
    raw_items = st.session_state.get("route_boundaries_v118", []) or []
    for i, item in enumerate(raw_items):
        coords = item.get("coords") if isinstance(item, dict) else item
        name = item.get("name", f"配布範囲{i+1}") if isinstance(item, dict) else f"配布範囲{i+1}"
        if coords and len(coords) >= 3:
            items.append({"name": str(name), "coords": list(coords), "original_index": i})
    # 登録済み境界がない場合は、従来通り渡されたpolysを使う。
    if not items:
        for i, poly in enumerate(polys):
            if poly and len(poly) >= 3:
                items.append({"name": f"配布範囲{i+1}", "coords": list(poly), "original_index": i})
    return items


def order_boundary_polys_v152(polys: Sequence[Sequence[LatLon]], route_order_mode: str) -> Tuple[List[List[LatLon]], List[str]]:
    """町丁目の生成順を決める。

    - 選択した順: v151までと同じ。
    - 近い順: 最初に登録した町丁目だけ固定し、2件目以降を重心距離の近い順に並べる。
    """
    mode = str(route_order_mode or "選択した順")
    items = _boundary_items_for_order_v152(polys)
    if len(items) <= 1:
        return [list(x.get("coords", [])) for x in items if x.get("coords")], ["v152町丁目順: 1件のみのため並べ替えなし"]

    if not mode.startswith("近い順"):
        names = " → ".join([str(x.get("name", f"配布範囲{i+1}")) for i, x in enumerate(items)])
        return [list(x["coords"]) for x in items], [f"v152町丁目順: 選択した順 / {names}"]

    ordered: List[Dict[str, Any]] = [items[0]]
    rest: List[Dict[str, Any]] = list(items[1:])
    cur_c = centroid(ordered[0]["coords"])
    while rest:
        nxt_i = min(range(len(rest)), key=lambda i: haversine_m(cur_c, centroid(rest[i]["coords"])))
        nxt = rest.pop(nxt_i)
        ordered.append(nxt)
        cur_c = centroid(nxt["coords"])

    names = " → ".join([str(x.get("name", f"配布範囲{i+1}")) for i, x in enumerate(ordered)])
    return [list(x["coords"]) for x in ordered], [f"v152町丁目順: 近い順（最初の町は固定） / {names}"]



# ==================================================
# v170: 選択済み町丁目連動 リバブルマンション名看板画像取得
# - v169で合格した「町名ページ→詳細ページ→マンション名画像」ロジックを本体へ追加
# - GPX/配布率/チョン/GPSブレは変更しない
# ==================================================

try:
    import csv as _csv_v170
    import io as _io_v170
    from dataclasses import asdict as _asdict_v170
    from urllib.parse import urljoin as _urljoin_v170, urlparse as _urlparse_v170, parse_qs as _parse_qs_v170, unquote as _unquote_v170
except Exception:
    pass

try:
    from bs4 import BeautifulSoup as _BeautifulSoup_v170
except Exception:
    _BeautifulSoup_v170 = None

try:
    import pandas as _pd_v170
except Exception:
    _pd_v170 = None

_V170_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0 Safari/537.36"
    ),
    "Accept-Language": "ja,en-US;q=0.9,en;q=0.8",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Connection": "close",
}

_V170_DETAIL_RE = re.compile(r"/mansion/library/(\d{6,})/?")
_V170_EXPECTED_RE = re.compile(r"該当\s*([0-9０-９,，]+)\s*件")
_V170_CHOME_RE = re.compile(r"([一二三四五六七八九十１２３４５６７８９０0-9]+丁目)")
_V170_PREFS = (
    "北海道", "青森県", "岩手県", "宮城県", "秋田県", "山形県", "福島県",
    "茨城県", "栃木県", "群馬県", "埼玉県", "千葉県", "東京都", "神奈川県",
    "新潟県", "富山県", "石川県", "福井県", "山梨県", "長野県", "岐阜県", "静岡県", "愛知県",
    "三重県", "滋賀県", "京都府", "大阪府", "兵庫県", "奈良県", "和歌山県",
    "鳥取県", "島根県", "岡山県", "広島県", "山口県", "徳島県", "香川県", "愛媛県", "高知県",
    "福岡県", "佐賀県", "長崎県", "熊本県", "大分県", "宮崎県", "鹿児島県", "沖縄県",
)
_V170_ADDRESS_START_RE = re.compile("|".join(map(re.escape, _V170_PREFS)))
_V170_STOP_WORDS_AFTER_ADDRESS = ("駅", "徒歩", "築", "戸", "詳細", "売出", "新しい物件", "このマンション", "円", "万円")
_V170_NG_TEXTS = (
    "買いたいTOP", "売りたいTOP", "借りたいTOP", "貸したいTOP",
    "このマンションを売りたい", "部屋の詳細", "売出されたら教えて欲しい",
    "AI査定", "スピードAI査定", "お問い合わせ", "無料相談",
)
_V170_LEAD_PHRASES = ("前のスライド 次のスライド", "1 / 0", "一覧")
_V170_BAD_CONTEXT_KEYWORDS = [
    "買いたいTOP", "売りたいTOP", "借りたいTOP", "貸したいTOP", "投資用TOP",
    "Tellus Talk", "スピードAI査定", "売却査定", "購入ガイド", "売却ガイド",
    "店舗検索TOP", "プレミアム賃貸", "お客様の声", "不動産AIアドバイザー",
    "リビング", "ダイニング", "キッチン", "洗面", "浴室", "トイレ", "眺望", "洋室", "寝室",
]

# まずユーザーが実際に試しているエリアを安定化。必要に応じてここへ町名URLを追加する。
_V170_LIVABLE_TOWN_URLS = {
    ("千葉県", "柏市", "あけぼの"): "https://www.livable.co.jp/mansion/library/chiba/t12217004/",
    ("千葉県", "柏市", "旭町"): "https://www.livable.co.jp/mansion/library/chiba/t12217005/",
    ("千葉県", "柏市", "明原"): "https://www.livable.co.jp/mansion/library/chiba/t12217006/",
    ("千葉県", "柏市", "大室"): "https://www.livable.co.jp/mansion/library/chiba/t12217027/",
    ("千葉県", "柏市", "豊住"): "https://www.livable.co.jp/mansion/library/chiba/t12217043/",
    ("千葉県", "柏市", "豊四季"): "https://www.livable.co.jp/mansion/library/chiba/t12217041/",
    ("千葉県", "柏市", "富里"): "https://www.livable.co.jp/mansion/library/chiba/t12217046/",
}
_V170_LIVABLE_CITY_URLS = {
    ("千葉県", "柏市"): "https://www.livable.co.jp/mansion/library/chiba/a12217/",
}

@dataclass
class MansionRowV170:
    no: int
    name: str
    address: str
    chome: str
    detail_url: str
    detail_id: str
    source_text: str
    town_key: str = ""

@dataclass
class LivableImageV170:
    label: str
    url: str
    raw_url: str
    source_tag: str
    context: str
    priority: int

@dataclass
class MansionSignResultV170:
    no: int
    name: str
    address: str
    chome: str
    detail_url: str
    sign_count: int
    sign_urls: str
    status: str
    warning: str
    town_key: str = ""


def _v170_normalize_text(s: str) -> str:
    if not s:
        return ""
    s = str(s).replace("\u3000", " ")
    return re.sub(r"\s+", " ", s).strip()


def _v170_zen_to_han(s: str) -> str:
    return str(s).translate(str.maketrans("０１２３４５６７８９", "0123456789"))


def _v170_fetch_html(url: str, timeout: int = 25) -> Tuple[str, str, int]:
    if requests is None:
        raise RuntimeError("requests がありません。PowerShellで `pip install requests` を実行してください。")
    resp = requests.get(url, headers=_V170_HEADERS, timeout=timeout)
    resp.raise_for_status()
    if not resp.encoding or resp.encoding.lower() in {"iso-8859-1", "ascii"}:
        resp.encoding = resp.apparent_encoding or "utf-8"
    return resp.text, resp.url, resp.status_code


def _v170_expected_count_from_text(text: str) -> Optional[int]:
    m = _V170_EXPECTED_RE.search(text or "")
    if not m:
        return None
    raw = _v170_zen_to_han(m.group(1)).replace(",", "").replace("，", "")
    try:
        return int(raw)
    except Exception:
        return None


def _v170_remove_lead_phrases(text: str) -> str:
    t = _v170_normalize_text(text)
    for phrase in _V170_LEAD_PHRASES:
        t = t.replace(phrase, " ")
    t = re.sub(r"^[0-9０-９]+\s*/\s*[0-9０-９]+\s*", "", t)
    return _v170_normalize_text(t)


def _v170_extract_address_from_text(text: str) -> str:
    t = _v170_normalize_text(text)
    m = _V170_ADDRESS_START_RE.search(t)
    if not m:
        return ""
    addr_part = t[m.start():]
    cuts = []
    for w in _V170_STOP_WORDS_AFTER_ADDRESS:
        idx = addr_part.find(w)
        if idx > 0:
            cuts.append(idx)
    if cuts:
        addr_part = addr_part[: min(cuts)]
    addr_part = _v170_normalize_text(addr_part)
    addr_part = re.sub(r"(常磐線|千代田|常磐緩行線|東武|JR|東京メトロ).*$", "", addr_part).strip()
    return addr_part


def _v170_extract_name_from_text(text: str, address: str) -> str:
    t = _v170_remove_lead_phrases(text)
    if address and address in t:
        name = t.split(address, 1)[0]
    else:
        m = _V170_ADDRESS_START_RE.search(t)
        name = t[: m.start()] if m else t
    name = _v170_remove_lead_phrases(name)
    name = re.sub(r"^[0-9０-９]+\s*枚\s*", "", name)
    name = re.sub(r"^詳細\s*", "", name)
    name = _v170_normalize_text(name)
    if len(name) > 80:
        name = name[:80].strip()
    return name


def _v170_extract_chome(address: str) -> str:
    m = _V170_CHOME_RE.search(address or "")
    return m.group(1) if m else ""


def _v170_clean_url(href: str, base_url: str) -> str:
    return _urljoin_v170(base_url, (href or "").split("#", 1)[0])


def _v170_is_bad_text(text: str) -> bool:
    t = _v170_normalize_text(text)
    return any(w in t for w in _V170_NG_TEXTS)


def _v170_detail_id_from_url(url: str) -> str:
    m = _V170_DETAIL_RE.search(url or "")
    return m.group(1) if m else ""


def _v170_find_parent_text(a) -> str:
    texts = []
    a_text = a.get_text(" ", strip=True)
    if a_text:
        texts.append(a_text)
    node = a
    for _ in range(5):
        node = getattr(node, "parent", None)
        if node is None:
            break
        tx = _v170_normalize_text(node.get_text(" ", strip=True))
        if tx and len(tx) < 1000:
            texts.append(tx)
            if _V170_ADDRESS_START_RE.search(tx) and "詳細" in tx:
                break
    with_addr = [_v170_normalize_text(x) for x in texts if _V170_ADDRESS_START_RE.search(_v170_normalize_text(x))]
    if with_addr:
        return min(with_addr, key=len)
    return _v170_normalize_text(" ".join(texts))


def _v170_parse_livable_town_page(html: str, final_url: str, town_key: str = "") -> Tuple[List[MansionRowV170], Dict[str, object]]:
    if _BeautifulSoup_v170 is None:
        raise RuntimeError("beautifulsoup4 が未インストールです。PowerShellで `pip install beautifulsoup4` を実行してください。")
    soup = _BeautifulSoup_v170(html, "html.parser")
    page_text = _v170_normalize_text(soup.get_text(" ", strip=True))
    expected = _v170_expected_count_from_text(page_text)
    rows: List[MansionRowV170] = []
    seen_urls = set()
    for a in soup.find_all("a", href=True):
        url = _v170_clean_url(a.get("href") or "", final_url)
        if not _V170_DETAIL_RE.search(url):
            continue
        if url in seen_urls:
            continue
        local_text = _v170_find_parent_text(a)
        if _v170_is_bad_text(local_text) and not _V170_ADDRESS_START_RE.search(local_text):
            continue
        address = _v170_extract_address_from_text(local_text)
        name = _v170_extract_name_from_text(local_text, address)
        if not name or not address or len(name) < 2:
            continue
        if any(x in name for x in ("詳細", "部屋", "このマンション", "売出", "新しい物件")):
            continue
        rows.append(MansionRowV170(
            no=len(rows) + 1,
            name=name,
            address=address,
            chome=_v170_extract_chome(address),
            detail_url=url,
            detail_id=_v170_detail_id_from_url(url),
            source_text=local_text,
            town_key=town_key,
        ))
        seen_urls.add(url)
    meta = {
        "expected_count": expected,
        "parsed_count": len(rows),
        "final_url": final_url,
        "unique_url_count": len({r.detail_url for r in rows}),
        "duplicate_url_count": len(rows) - len({r.detail_url for r in rows}),
        "has_century_kashiwa": any("センチュリー柏" in r.name for r in rows),
        "town_key": town_key,
    }
    return rows, meta


def _v170_decode_livable_img_proxy(url: str) -> str:
    try:
        parsed = _urlparse_v170(url)
        if parsed.netloc.endswith("img.livable.co.jp"):
            qs = _parse_qs_v170(parsed.query)
            inner = qs.get("url", [""])[0]
            if inner:
                return _unquote_v170(inner)
    except Exception:
        pass
    return url


def _v170_absolutize(base_url: str, candidate: str) -> Optional[str]:
    if not candidate:
        return None
    candidate = str(candidate).strip().strip('"\'')
    if not candidate or candidate.startswith("data:") or candidate.startswith("javascript:"):
        return None
    if candidate.startswith("//"):
        candidate = "https:" + candidate
    return _urljoin_v170(base_url, candidate)


def _v170_urls_from_srcset(base_url: str, srcset: str) -> List[str]:
    out = []
    if not srcset:
        return out
    for part in srcset.split(','):
        first = part.strip().split(' ')[0].strip()
        u = _v170_absolutize(base_url, first)
        if u:
            out.append(u)
    return out


def _v170_is_livable_image_url(u: str) -> bool:
    if not u:
        return False
    lu = u.lower()
    if any(x in lu for x in ["/assets/", "logo", "icon", "btn", "banner", "sprite", "loading", "noimage"]):
        return False
    if "img.livable.co.jp" in lu:
        return True
    if "project-image" in lu and any(ext in lu for ext in [".jpg", ".jpeg", ".png", ".webp"]):
        return True
    if "livable.co.jp" in lu and any(ext in lu for ext in [".jpg", ".jpeg", ".png", ".webp"]):
        return True
    return False


def _v170_context_text_for_tag(tag, max_len: int = 240) -> str:
    parts = []
    try:
        for attr in ["alt", "title", "aria-label", "data-alt", "data-title"]:
            v = tag.get(attr)
            if v:
                parts.append(str(v))
    except Exception:
        pass
    try:
        own_txt = _v170_normalize_text(tag.get_text(" ", strip=True))
        if own_txt and len(own_txt) <= 80:
            parts.append(own_txt)
    except Exception:
        pass
    try:
        a = tag.find_parent("a")
        if a is not None:
            for attr in ["title", "aria-label"]:
                v = a.get(attr)
                if v:
                    parts.append(str(v))
            txt = _v170_normalize_text(a.get_text(" ", strip=True))
            if txt and len(txt) <= 120:
                parts.append(txt)
    except Exception:
        pass
    try:
        fig = tag.find_parent("figure")
        if fig is not None:
            cap = fig.find("figcaption")
            if cap:
                txt = _v170_normalize_text(cap.get_text(" ", strip=True))
                if txt:
                    parts.append(txt)
    except Exception:
        pass
    return _v170_normalize_text(" / ".join(dict.fromkeys(parts)))[:max_len]


def _v170_has_bad_context(c: str) -> bool:
    return any(k in (c or "") for k in _V170_BAD_CONTEXT_KEYWORDS)


def _v170_classify_image(context: str, url: str, mansion_name: str = "") -> Tuple[str, int]:
    c = _v170_normalize_text(context or "")
    name = _v170_normalize_text(mansion_name or "")
    if _v170_has_bad_context(c) and not (name and name in c and any(k in c for k in ["マンション名", "館銘板", "銘板", "看板"] )):
        return "除外", 99
    if name and name in c:
        if any(k in c for k in ["マンション名", "館銘板", "銘板", "看板", "名称", "プレート", "表札"]):
            return "マンション名", 1
        if any(k in c for k in ["エントランス", "入口", "エントランスホール", "ロビー", "オートロック"]):
            return "エントランス", 2
        if any(k in c for k in ["アプローチ", "外構", "通路", "駐車場", "駐輪場", "共用部"]):
            return "アプローチ", 3
        if any(k in c for k in ["外観", "建物", "現地外観", "外観写真"]):
            return "外観", 4
    if any(k in c for k in ["マンション名", "館銘板", "銘板", "看板"]):
        return "マンション名", 5
    if "エントランス" in c:
        return "エントランス", 6
    if "アプローチ" in c:
        return "アプローチ", 7
    if "外観" in c:
        return "外観", 8
    return "その他", 9


def _v170_extract_livable_images(base_url: str, soup, mansion_name: str = "") -> List[LivableImageV170]:
    images: List[LivableImageV170] = []
    seen = set()
    def add_url(u: str, tag, source_tag: str):
        au = _v170_absolutize(base_url, u)
        if not au or not _v170_is_livable_image_url(au):
            return
        canonical = _v170_decode_livable_img_proxy(au)
        key = re.sub(r"[?&](w|h)=\d+", "", canonical)
        if key in seen:
            return
        seen.add(key)
        ctx = _v170_context_text_for_tag(tag)
        label, pri = _v170_classify_image(ctx, au, mansion_name=mansion_name)
        if label == "除外":
            return
        images.append(LivableImageV170(label=label, url=au, raw_url=canonical, source_tag=source_tag, context=ctx, priority=pri))
    for tag in soup.find_all("img"):
        for attr in ["src", "data-src", "data-original", "data-lazy", "data-url"]:
            v = tag.get(attr)
            if v:
                add_url(v, tag, f"img[{attr}]")
        for attr in ["srcset", "data-srcset"]:
            for u in _v170_urls_from_srcset(base_url, tag.get(attr) or ""):
                add_url(u, tag, f"img[{attr}]")
    for tag in soup.find_all("source"):
        for attr in ["srcset", "data-srcset", "src"]:
            v = tag.get(attr)
            if attr.endswith("srcset"):
                for u in _v170_urls_from_srcset(base_url, v or ""):
                    add_url(u, tag, f"source[{attr}]")
            elif v:
                add_url(v, tag, f"source[{attr}]")
    for tag in soup.find_all("a", href=True):
        href = tag.get("href") or ""
        if any(ext in href.lower() for ext in [".jpg", ".jpeg", ".png", ".webp"]) or "img.livable.co.jp" in href.lower():
            add_url(href, tag, "a[href]")
    html = str(soup)
    for m in re.finditer(r"https?:\\/\\/[^\"']+?\.(?:jpg|jpeg|png|webp)(?:\?[^\"']*)?", html, flags=re.I):
        u = m.group(0).replace("\\/", "/")
        add_url(u, soup, "html-url")
    images.sort(key=lambda x: (x.priority, x.label, x.url))
    return images


def _v170_read_detail_for_signs(row: MansionRowV170, timeout: int = 25) -> Tuple[List[LivableImageV170], str]:
    try:
        html, final_url, status = _v170_fetch_html(row.detail_url, timeout=timeout)
        soup = _BeautifulSoup_v170(html, "html.parser")
        images = _v170_extract_livable_images(final_url, soup, mansion_name=row.name)
        signs = [img for img in images if img.label == "マンション名"]
        signs = [img for img in signs if (row.name in img.context or any(k in img.context for k in ["マンション名", "館銘板", "銘板", "看板"]))]
        return signs, ""
    except Exception as e:
        return [], str(e)


def _v170_results_to_csv_bytes(results: List[MansionSignResultV170]) -> bytes:
    out = _io_v170.StringIO()
    writer = _csv_v170.DictWriter(out, fieldnames=["no", "town_key", "name", "address", "chome", "detail_url", "sign_count", "sign_urls", "status", "warning"])
    writer.writeheader()
    for r in results:
        writer.writerow(_asdict_v170(r))
    return out.getvalue().encode("utf-8-sig")


def _v171_split_town_chome_from_rest(rest: str) -> Tuple[str, str]:
    """市区町村名が取れない場合でも、旭町一丁目 -> 旭町 / 一丁目 に分ける。"""
    rest = str(rest or "").replace(" ", "")
    m = re.search(r"(.+?)([一二三四五六七八九十１２３４５６７８９０0-9]+丁目)$", rest)
    if m:
        return m.group(1), m.group(2)
    return rest, ""


def _v171_infer_pref_city_town(pref: str, town: str) -> Optional[Tuple[str, str, str]]:
    """
    選択名が「千葉県 旭町一丁目」のように市名なしで保存された場合に、
    既知のリバブル町名URL辞書から市名を補完する。
    例: 千葉県 + 旭町 -> 千葉県 柏市 旭町
    """
    pref = pref or "千葉県"
    town = str(town or "").replace(" ", "")
    if not town:
        return None
    candidates = []
    for (p, city, mapped_town), url in _V170_LIVABLE_TOWN_URLS.items():
        if p != pref:
            continue
        if town == mapped_town or town.startswith(mapped_town) or mapped_town.startswith(town):
            candidates.append((p, city, mapped_town))
    # 完全一致を優先
    exact = [c for c in candidates if c[2] == town]
    if len(exact) == 1:
        return exact[0]
    if len(candidates) == 1:
        return candidates[0]
    return None


def _v175_parse_slash_or_comma_area_name(name: str) -> Optional[Dict[str, str]]:
    """
    v175追加:
    Nominatim/候補表示では "旭町一丁目 / 柏市 / 千葉県" のように
    町名→市名→県名の逆順で保存されることがある。
    これを通常の 千葉県/柏市/旭町/一丁目 に戻す。
    """
    raw_name = str(name or "").strip()
    if not raw_name:
        return None

    # / 区切り・カンマ区切りを優先して読む
    parts = [x.strip() for x in re.split(r"[/,，]", raw_name) if x and x.strip()]
    if len(parts) < 2:
        return None

    pref = ""
    city = ""
    town_part = ""

    for part in parts:
        compact = _v170_normalize_text(part).replace(" ", "")
        if compact in _V170_PREFS:
            pref = compact
            continue
        if re.fullmatch(r".+?[市区]", compact):
            city = compact
            continue

    # 町名候補は、市区町村・都道府県・国名以外の先頭要素を優先
    for part in parts:
        compact = _v170_normalize_text(part).replace(" ", "")
        if not compact:
            continue
        if compact in _V170_PREFS or compact in {"日本", "Japan"}:
            continue
        if city and compact == city:
            continue
        # 旭町一丁目 / あけぼの四丁目 / 豊四季 など
        town_part = compact
        break

    pref = pref or "千葉県"
    if not city:
        # 市名が無い場合は既知町名から補完
        town_tmp, chome_tmp = _v171_split_town_chome_from_rest(town_part)
        inferred = _v171_infer_pref_city_town(pref, town_tmp)
        if inferred:
            ipref, icity, mapped_town = inferred
            return {"pref": ipref, "city": icity, "town": mapped_town, "chome": chome_tmp, "raw": name}
        return None

    if not town_part:
        return None

    town, chome = _v171_split_town_chome_from_rest(town_part)
    if not town:
        return None

    # 町名が既知URL辞書にある場合は、表記ゆれを辞書側へ寄せる
    inferred = _v171_infer_pref_city_town(pref, town)
    if inferred and inferred[1] == city:
        ipref, icity, mapped_town = inferred
        return {"pref": ipref, "city": icity, "town": mapped_town, "chome": chome, "raw": name}

    return {"pref": pref, "city": city, "town": town, "chome": chome, "raw": name}


def _v170_parse_area_name(name: str) -> Optional[Dict[str, str]]:
    # v175: まず "旭町一丁目 / 柏市 / 千葉県" 形式を正しく読む
    slash_info = _v175_parse_slash_or_comma_area_name(name)
    if slash_info:
        return slash_info

    raw = _v170_normalize_text(name).replace(" ", "")
    pref = ""
    for p in _V170_PREFS:
        if raw.startswith(p):
            pref = p
            raw2 = raw[len(p):]
            break
    else:
        raw2 = raw
        # 現状よく使う千葉県側は県名が省略されることがあるため保険
        if "柏市" in raw2:
            pref = "千葉県"
    pref = pref or "千葉県"

    # v175: "旭町一丁目柏市千葉県" のような逆順に近い文字列を救済
    m_rev = re.match(r"(.+?丁目)?(.+?)(柏市|我孫子市|松戸市|流山市|市川市|船橋市|鎌ケ谷市|野田市|印西市|白井市|取手市|守谷市).*$", raw2)
    if m_rev and not raw2.startswith(m_rev.group(3)):
        town_part = (m_rev.group(1) or "") + (m_rev.group(2) or "")
        city = m_rev.group(3)
        town, chome = _v171_split_town_chome_from_rest(town_part)
        inferred = _v171_infer_pref_city_town(pref, town)
        if inferred and inferred[1] == city:
            ipref, icity, mapped_town = inferred
            return {"pref": ipref, "city": icity, "town": mapped_town, "chome": chome, "raw": name}
        if town:
            return {"pref": pref, "city": city, "town": town, "chome": chome, "raw": name}

    # v174修正: 「千葉県 旭町一丁目」を「市区町村」の町として誤読しない
    m_city = re.match(r"(.+?[市区])(.+)$", raw2)
    if m_city:
        city = m_city.group(1)
        rest = m_city.group(2)
        town, chome = _v171_split_town_chome_from_rest(rest)
        if not town:
            return None
        inferred = _v171_infer_pref_city_town(pref, town)
        if inferred and inferred[1] == city:
            ipref, icity, mapped_town = inferred
            return {"pref": ipref, "city": icity, "town": mapped_town, "chome": chome, "raw": name}
        return {"pref": pref, "city": city, "town": town, "chome": chome, "raw": name}

    # 市名なしで「千葉県 旭町一丁目」のように入ってきた場合の救済
    town, chome = _v171_split_town_chome_from_rest(raw2)
    inferred = _v171_infer_pref_city_town(pref, town)
    if inferred:
        ipref, city, mapped_town = inferred
        return {"pref": ipref, "city": city, "town": mapped_town, "chome": chome, "raw": name}

    return None


def _v176_add_name_with_source(raw_names: List[str], debug: List[Dict[str, str]], name: str, source: str) -> None:
    nm = str(name or "").strip()
    if not nm:
        return
    raw_names.append(nm)
    try:
        debug.append({"source": source, "name": nm})
    except Exception:
        pass


def _v176_candidate_display_name(p: Any) -> str:
    if not isinstance(p, dict):
        return ""
    vals = []
    for k in ("display_name", "name", "label"):
        v = p.get(k)
        if v:
            vals.append(str(v))
    try:
        vals.append(short_place_name(p))
    except Exception:
        pass
    return " / ".join([v for v in vals if v])


def _v176_collect_known_town_strings_from_session(max_items: int = 80) -> List[str]:
    """
    v176最後の保険。Streamlitの状態の中に残っている候補文字列から、
    柏市/あけぼの/旭町など既知リバブル町名に関係する文字列だけ拾う。
    画面上の赤いチップや候補検索結果が別キーに残っていても救済するため。
    """
    known_towns = {t for (_, _, t) in _V170_LIVABLE_TOWN_URLS.keys()}
    known_cities = {c for (_, c, _) in _V170_LIVABLE_TOWN_URLS.keys()}
    out: List[str] = []
    seen = set()

    def walk(obj: Any, depth: int = 0):
        if len(out) >= max_items or depth > 4:
            return
        if isinstance(obj, str):
            txt = _v170_normalize_text(obj)
            compact = txt.replace(" ", "")
            if len(compact) < 2 or len(compact) > 180:
                return
            if any(t in compact for t in known_towns) or any(c in compact for c in known_cities):
                if compact not in seen:
                    seen.add(compact)
                    out.append(txt)
            return
        if isinstance(obj, dict):
            for k, v in list(obj.items()):
                if str(k).startswith("_"):
                    continue
                walk(v, depth + 1)
        elif isinstance(obj, (list, tuple, set)):
            for v in list(obj)[:120]:
                walk(v, depth + 1)

    try:
        for k, v in list(st.session_state.items()):
            # 大きすぎる生成ルート座標は文字列探索には不要
            if k in {"last_generated_route_v118", "required_pins_v118", "boundary_lines"}:
                continue
            walk(v, 0)
    except Exception:
        pass
    return out


def _v176_sample_points_from_current_geometry(max_points: int = 6) -> List[Tuple[float, float]]:
    pts: List[Tuple[float, float]] = []

    def add_point(pt: Any):
        try:
            lat, lon = float(pt[0]), float(pt[1])
            if -90 <= lat <= 90 and -180 <= lon <= 180:
                pts.append((lat, lon))
        except Exception:
            pass

    # 境界ポリゴンの代表点
    for item in (st.session_state.get("route_boundaries_v118", []) or []):
        poly = item.get("coords") if isinstance(item, dict) else item
        if poly:
            try:
                c = centroid(poly)
                add_point(c)
            except Exception:
                pass
    for line in (st.session_state.get("boundary_lines", []) or []):
        if line:
            try:
                c = centroid(line)
                add_point(c)
            except Exception:
                pass

    # 生成ルートのサンプル点
    route = st.session_state.get("last_generated_route_v118", []) or []
    if route:
        n = len(route)
        for idx in [0, n//5, 2*n//5, 3*n//5, 4*n//5, n-1]:
            if 0 <= idx < n:
                add_point(route[idx])

    # 近すぎる重複を削る
    unique: List[Tuple[float, float]] = []
    for p in pts:
        if not any(haversine_m(p, q) < 80 for q in unique):
            unique.append(p)
        if len(unique) >= max_points:
            break
    return unique


def _v176_reverse_geocode_area_names_from_geometry() -> List[str]:
    """名前が全滅した時だけ使う保険。生成済みルート/境界の座標から町名を復元する。"""
    if requests is None:
        return []
    known_towns = {t for (_, _, t) in _V170_LIVABLE_TOWN_URLS.keys()}
    names: List[str] = []
    seen = set()
    pts = _v176_sample_points_from_current_geometry()
    for lat, lon in pts:
        try:
            url = "https://nominatim.openstreetmap.org/reverse"
            params = {
                "format": "jsonv2",
                "lat": f"{lat:.7f}",
                "lon": f"{lon:.7f}",
                "zoom": "18",
                "addressdetails": "1",
                "accept-language": "ja",
            }
            r = requests.get(url, params=params, headers={"User-Agent": _V170_HEADERS.get("User-Agent", "Mozilla/5.0")}, timeout=12)
            if r.status_code != 200:
                continue
            data = r.json() if hasattr(r, "json") else {}
            addr = data.get("address", {}) if isinstance(data, dict) else {}
            display = str(data.get("display_name", "") if isinstance(data, dict) else "")
            pref = addr.get("province") or addr.get("state") or "千葉県"
            city = addr.get("city") or addr.get("town") or addr.get("municipality") or addr.get("county") or ""
            all_text = " ".join([display] + [str(v) for v in addr.values()])
            for town in known_towns:
                if town and town in all_text:
                    if not city:
                        inf = _v171_infer_pref_city_town(pref, town)
                        if inf:
                            pref, city, town = inf
                    nm = f"{pref} {city} {town}".strip()
                    if nm not in seen:
                        seen.add(nm)
                        names.append(nm)
            time.sleep(0.25)
        except Exception:
            continue
    return names


def _v173_collect_area_names_for_image() -> List[str]:
    """
    v176: 画像取得に使う町丁目名を、現在の画面状態からできるだけ確実に集める。

    優先順:
    1) 配布範囲に追加済み
    2) 現在プレビュー中の境界名
    3) 左側で選択中の候補
    4) 直近候補検索結果の中で、既知リバブル町名として解釈できるもの
    5) セッション内に残った候補文字列
    6) それでも空なら、生成済みルート/境界座標から逆ジオコーディングで町名復元
    """
    raw_names: List[str] = []
    debug: List[Dict[str, str]] = []

    # 1) 登録済み配布範囲
    items = st.session_state.get("route_boundaries_v118", []) or []
    for item in items:
        if isinstance(item, dict):
            _v176_add_name_with_source(raw_names, debug, item.get("name", ""), "route_boundaries_v118")

    # 2) 現在プレビュー中の境界名
    for nm in (st.session_state.get("boundary_line_names_v174", []) or []):
        _v176_add_name_with_source(raw_names, debug, nm, "boundary_line_names_v174")

    # 3) 左側で選択中の候補
    candidates = st.session_state.get("search_candidates_v126", []) or []
    selected_idxs = st.session_state.get("selected_candidate_idxs_v126", []) or []
    try:
        selected_idxs = [int(i) for i in selected_idxs]
    except Exception:
        selected_idxs = []
    for idx in selected_idxs:
        if 0 <= idx < len(candidates):
            p = candidates[idx]
            try:
                nm = short_place_name(p)
            except Exception:
                nm = _v176_candidate_display_name(p)
            _v176_add_name_with_source(raw_names, debug, nm, "selected_candidate_idxs_v126")

    # 4) ここまで空なら、候補検索結果そのものから拾う
    if not raw_names and candidates:
        for p in candidates[:80]:
            nm = _v176_candidate_display_name(p)
            if nm and _v170_parse_area_name(nm):
                _v176_add_name_with_source(raw_names, debug, nm, "search_candidates_v126_all_fallback")

    # 5) セッション内の文字列探索
    if not raw_names:
        for nm in _v176_collect_known_town_strings_from_session():
            if _v170_parse_area_name(nm):
                _v176_add_name_with_source(raw_names, debug, nm, "session_text_fallback")

    # 6) 生成済みルート/境界座標から町名復元
    if not raw_names and (st.session_state.get("last_generated_route_v118") or st.session_state.get("boundary_lines") or st.session_state.get("route_boundaries_v118")):
        for nm in _v176_reverse_geocode_area_names_from_geometry():
            if _v170_parse_area_name(nm):
                _v176_add_name_with_source(raw_names, debug, nm, "reverse_geocode_fallback")

    out = list(dict.fromkeys(raw_names))
    try:
        st.session_state["v176_area_name_debug_sources"] = debug
        st.session_state["v176_area_name_debug_final"] = out
    except Exception:
        pass
    return out


def _v170_selected_area_groups() -> List[Dict[str, Any]]:
    """
    v173修正:
    画像取得対象は以下の順で拾う。
    1) 配布範囲に追加済みの町丁目
    2) 「この条件で軌跡を生成」した時に実際に使った町丁目名
    3) 左側で赤いチップとして選択中の候補

    これにより、配布範囲に追加ボタンを押さずにプレビュー境界から軌跡生成した場合でも、
    生成後の画像取得で町丁目名を失わない。
    """
    raw_names: List[str] = []

    # 1) 現在の登録済み/選択中
    raw_names.extend(_v173_collect_area_names_for_image())

    # 2) 最後に軌跡生成した時に保存した町丁目名
    last_names = st.session_state.get("last_generated_area_names_v173", []) or []
    for nm in last_names:
        nm = str(nm or "").strip()
        if nm:
            raw_names.append(nm)

    raw_names = list(dict.fromkeys(raw_names))

    groups: Dict[Tuple[str, str, str], Dict[str, Any]] = {}
    for name in raw_names:
        info = _v170_parse_area_name(name)
        if not info:
            continue
        key = (info["pref"], info["city"], info["town"])
        g = groups.setdefault(key, {
            "pref": info["pref"],
            "city": info["city"],
            "town": info["town"],
            "chomes": set(),
            "areas": [],
            "town_key": f"{info['pref']} {info['city']} {info['town']}"
        })
        if info.get("chome"):
            g["chomes"].add(info["chome"])
        g["areas"].append(info["raw"])

    # 同一町名・丁目の重複整理
    out = list(groups.values())
    for g in out:
        g["areas"] = list(dict.fromkeys(g.get("areas", [])))
    return out


def _v170_town_page_url_for_group(g: Dict[str, Any]) -> Optional[str]:
    pref, city, town = g.get("pref", ""), g.get("city", ""), g.get("town", "")
    key = (pref, city, town)
    if key in _V170_LIVABLE_TOWN_URLS:
        return _V170_LIVABLE_TOWN_URLS[key]
    # 保険: 市区町村ページから町名リンクを探す
    city_url = _V170_LIVABLE_CITY_URLS.get((pref, city))
    if not city_url:
        return None
    try:
        html, final_url, _ = _v170_fetch_html(city_url)
        soup = _BeautifulSoup_v170(html, "html.parser")
        for a in soup.find_all("a", href=True):
            tx = _v170_normalize_text(a.get_text(" ", strip=True))
            href = a.get("href") or ""
            if town and town in tx and "mansion/library" in href:
                return _v170_clean_url(href, final_url)
    except Exception:
        return None
    return None


# v178: 丁目表記ゆれ対策。
# リバブル住所は「旭町1丁目」「旭町１丁目」になりやすく、
# 選択町丁目側は「旭町一丁目」で来るため、v177では丁目フィルタで全件落ちていた。
_V178_KANJI_NUM = {
    "一": "1", "二": "2", "三": "3", "四": "4", "五": "5",
    "六": "6", "七": "7", "八": "8", "九": "9", "十": "10",
}

def _v178_normalize_chome_token(s: str) -> str:
    txt = _v170_zen_to_han(str(s or "")).replace(" ", "").replace("　", "")
    # 「一丁目」「1丁目」「１丁目」を全部「1丁目」へ寄せる
    for k, v in sorted(_V178_KANJI_NUM.items(), key=lambda kv: -len(kv[0])):
        txt = txt.replace(k + "丁目", v + "丁目")
    return txt

def _v178_extract_chome_numbers_from_text(s: str) -> set:
    txt = _v178_normalize_chome_token(s)
    return set(re.findall(r"(\d+)丁目", txt))

def _v170_addr_matches_group(address: str, g: Dict[str, Any]) -> bool:
    addr_raw = str(address or "")
    addr = _v178_normalize_chome_token(addr_raw)
    if g.get("city") and str(g["city"]).replace(" ", "") not in addr:
        return False
    if g.get("town") and str(g["town"]).replace(" ", "") not in addr:
        return False
    chomes = g.get("chomes") or set()
    if chomes:
        wanted_nums = set()
        for ch in chomes:
            wanted_nums |= _v178_extract_chome_numbers_from_text(ch)
        addr_nums = _v178_extract_chome_numbers_from_text(addr)
        # 丁目番号が取れる場合は番号で比較。これで 一丁目 vs 1丁目 を一致させる。
        if wanted_nums and addr_nums:
            if wanted_nums.isdisjoint(addr_nums):
                return False
        else:
            # 番号抽出できない特殊ケースだけ従来の文字包含へフォールバック
            normalized_chomes = [_v178_normalize_chome_token(ch) for ch in chomes]
            if not any(ch and ch in addr for ch in normalized_chomes):
                return False
    return True


def _v170_render_sign_cards(results: List[MansionSignResultV170], sign_map: Dict[int, List[LivableImageV170]], max_show: int):
    st.markdown("#### マンション名画像 取得結果")
    for r in results[:max_show]:
        with st.container(border=True):
            st.markdown(f"### {r.no}. {r.name}")
            st.write(f"住所：{r.address}")
            st.write(f"町丁目：{r.chome or '不明'}")
            signs = sign_map.get(r.no, [])
            if not signs:
                st.warning("マンション名画像：未取得")
                if r.warning:
                    st.caption(f"理由：{r.warning}")
            else:
                cols = st.columns(min(3, max(1, len(signs))))
                for i, img in enumerate(signs[:3]):
                    with cols[i % len(cols)]:
                        st.image(img.url, caption=img.context or "マンション名", use_container_width=True)
                        st.link_button("画像を開く", img.url, key=f"v170_img_{r.no}_{i}_{abs(hash(img.url))}")
            st.link_button("元ページを開く", r.detail_url, key=f"v170_page_{r.no}_{abs(hash(r.detail_url))}")


def render_selected_area_livable_sign_images_v170() -> None:
    st.divider()
    st.subheader("マンション名看板画像 v176（生成済みルート座標からの復元付き）")
    st.caption("v169で合格した画像取得ロジックを本体に接続します。v176では、登録済み/選択中/生成時保存名が空でも、生成済みルートや境界座標から町名復元を試します。")

    with st.expander("選択済み町丁目 → マンション名看板画像を自動取得", expanded=False):
        groups = _v170_selected_area_groups()
        if not groups:
            st.error("画像取得対象の町名を復元できませんでした。生成済みルート・選択候補・検索候補・座標復元まで確認しましたが、町名が取れていません。")
            dbg = st.session_state.get("v176_area_name_debug_sources", []) or []
            final_dbg = st.session_state.get("v176_area_name_debug_final", []) or []
            with st.expander("v176 町名取得診断", expanded=True):
                st.write("最終候補:", final_dbg)
                st.write("取得元ログ:", dbg)
                st.write("last_generated_area_names_v173:", st.session_state.get("last_generated_area_names_v173", []))
                st.write("boundary_line_names_v174:", st.session_state.get("boundary_line_names_v174", []))
                st.write("selected_candidate_idxs_v126:", st.session_state.get("selected_candidate_idxs_v126", []))
                st.write("search_candidates_v126件数:", len(st.session_state.get("search_candidates_v126", []) or []))
                st.write("route_boundaries_v118件数:", len(st.session_state.get("route_boundaries_v118", []) or []))
                st.write("last_generated_route_v118点数:", len(st.session_state.get("last_generated_route_v118", []) or []))
            return
        st.write("検索対象:")
        for g in groups:
            ch = "・".join(sorted(g.get("chomes") or [])) or "全域"
            st.write(f"- {g.get('pref')} {g.get('city')} {g.get('town')}（{ch}）")
        c1, c2, c3 = st.columns(3)
        max_details_per_town = int(c1.number_input("町名ごとの詳細取得上限", 1, 80, 30, 1, key="v170_max_details_per_town"))
        max_show = int(c2.number_input("表示上限", 1, 120, 60, 1, key="v170_max_show"))
        delay = float(c3.number_input("詳細ページ間隔 秒", 0.0, 3.0, 0.15, 0.05, key="v170_delay"))
        run = st.button("生成済み/選択中/追加済み町丁目からマンション名看板画像を取得（v176）", type="primary", use_container_width=True, key="v170_run")

        if run:
            # v178: 前回の結果を一度クリア。空結果の時に古い/無表示で混乱しないようにする。
            st.session_state["v170_livable_results"] = []
            st.session_state["v170_livable_sign_map"] = {}
            st.session_state["v170_livable_rows"] = []
            st.session_state["v170_livable_metas"] = []
            st.session_state["v170_livable_errors"] = []
            st.session_state["v178_last_attempt_summary"] = {}
            all_rows: List[MansionRowV170] = []
            metas = []
            town_errors = []
            with st.spinner("リバブル町名ページから詳細ページ一覧を取得中..."):
                for g in groups:
                    town_url = _v170_town_page_url_for_group(g)
                    town_key = f"{g.get('pref')} {g.get('city')} {g.get('town')}"
                    if not town_url:
                        town_errors.append(f"{town_key}: リバブル町名ページURLを見つけられませんでした")
                        continue
                    try:
                        html, final_url, status = _v170_fetch_html(town_url)
                        rows, meta = _v170_parse_livable_town_page(html, final_url, town_key=town_key)
                        rows = [r for r in rows if _v170_addr_matches_group(r.address, g)]
                        # 町名内で選択した丁目だけに絞った後、noを一旦通し番号化する
                        metas.append({**meta, "town_url": final_url, "after_chome_filter": len(rows)})
                        all_rows.extend(rows[:max_details_per_town])
                    except Exception as e:
                        town_errors.append(f"{town_key}: {e}")

            # URL重複除去、通し番号振り直し
            unique_rows = []
            seen = set()
            for r in all_rows:
                if r.detail_url in seen:
                    continue
                seen.add(r.detail_url)
                r.no = len(unique_rows) + 1
                unique_rows.append(r)

            st.session_state["v178_last_attempt_summary"] = {
                "town_groups": [f"{g.get('pref')} {g.get('city')} {g.get('town')}（{'・'.join(sorted(g.get('chomes') or [])) or '全域'}）" for g in groups],
                "town_page_errors": list(town_errors),
                "town_page_logs": metas,
                "detail_rows_after_filter": len(unique_rows),
            }

            sign_map: Dict[int, List[LivableImageV170]] = {}
            results: List[MansionSignResultV170] = []
            progress = st.progress(0.0, text="詳細ページからマンション名画像を取得中...")
            for idx, row in enumerate(unique_rows, start=1):
                progress.progress((idx - 1) / max(1, len(unique_rows)), text=f"{idx}/{len(unique_rows)} {row.name} を確認中...")
                signs, warning = _v170_read_detail_for_signs(row)
                sign_map[row.no] = signs
                results.append(MansionSignResultV170(
                    no=row.no,
                    name=row.name,
                    address=row.address,
                    chome=row.chome,
                    detail_url=row.detail_url,
                    sign_count=len(signs),
                    sign_urls=" | ".join(img.url for img in signs),
                    status="OK" if signs else "NO_SIGN_IMAGE",
                    warning=warning,
                    town_key=row.town_key,
                ))
                if delay:
                    time.sleep(float(delay))
            progress.progress(1.0, text="取得完了")

            st.session_state["v170_livable_results"] = results
            st.session_state["v170_livable_sign_map"] = sign_map
            st.session_state["v170_livable_rows"] = unique_rows
            st.session_state["v170_livable_metas"] = metas
            st.session_state["v170_livable_errors"] = town_errors

        results: List[MansionSignResultV170] = st.session_state.get("v170_livable_results", []) or []
        sign_map: Dict[int, List[LivableImageV170]] = st.session_state.get("v170_livable_sign_map", {}) or {}
        metas = st.session_state.get("v170_livable_metas", []) or []
        errors = st.session_state.get("v170_livable_errors", []) or []
        if errors:
            for e in errors:
                st.warning(e)
        if results:
            sign_ok = sum(1 for r in results if r.sign_count > 0)
            st.success(f"取得完了：詳細ページ {len(results)}件 / マンション名画像あり {sign_ok}件")
            if metas:
                with st.expander("町名ページ取得ログ", expanded=False):
                    if _pd_v170 is not None:
                        st.dataframe(_pd_v170.DataFrame(metas), use_container_width=True, hide_index=True)
                    else:
                        st.write(metas)
            st.download_button(
                "マンション名看板画像CSVをダウンロード",
                data=_v170_results_to_csv_bytes(results),
                file_name="livable_selected_area_sign_images_v170.csv",
                mime="text/csv",
                use_container_width=True,
                key="v170_csv",
            )
            _v170_render_sign_cards(results, sign_map, int(st.session_state.get("v170_max_show", 60)))
        else:
            st.info("まだ取得していません。ボタンを押すと、生成済み/選択中/追加済み町丁目からマンション名看板画像を取得（v176）します。")



# ==================================================
# v177 OVERRIDE: 画像取得対象町名の受け渡しを可視化・強制安定化
# 目的:
# - v169で合格したリバブル画像取得ロジックは触らない
# - 本体統合時の「町名が空」だけを潰す
# - 取得対象をボタン前に必ず画面表示し、空のまま進ませない
# - hidden session_state が欠けても、生成済みルート/境界座標から逆引きする
# - 最後の保険として手入力欄も用意するが、通常は自動検出を優先する
# ==================================================


def _v177_split_manual_area_text(text: str) -> List[str]:
    out: List[str] = []
    for part in re.split(r"[\n;；]+", str(text or "")):
        nm = part.strip()
        if nm:
            out.append(nm)
    return out


def _v177_collect_raw_area_names_for_image() -> List[str]:
    raw: List[str] = []
    debug: List[Dict[str, str]] = []

    def add_many(names: Iterable[str], source: str):
        for nm in names:
            nm = str(nm or "").strip()
            if not nm:
                continue
            raw.append(nm)
            debug.append({"source": source, "name": nm})

    # 1) v176の強化コレクタ。登録済み・選択中・候補・session文字列・座標逆引きまで見る。
    try:
        names = _v173_collect_area_names_for_image()
        add_many(names, "v176_collect_area_names")
    except Exception as e:
        debug.append({"source": "v176_collect_area_names_error", "name": str(e)})

    # 2) 生成ボタン時に保存できていた名前
    try:
        add_many(st.session_state.get("last_generated_area_names_v173", []) or [], "last_generated_area_names_v173")
    except Exception as e:
        debug.append({"source": "last_generated_area_names_error", "name": str(e)})

    # 3) v176コレクタがまだ空の場合だけ、明示的にもう一度座標逆引き
    #    ここは「ルートは出ているのに町名が空」を潰す最後の自動手段。
    if not [x for x in raw if _v170_parse_area_name(x)]:
        try:
            add_many(_v176_reverse_geocode_area_names_from_geometry(), "reverse_geocode_direct_v177")
        except Exception as e:
            debug.append({"source": "reverse_geocode_error", "name": str(e)})

    # 4) 画面の保険入力欄。通常は使わないが、hidden stateが完全に消えた時の最後の救済。
    try:
        manual = st.session_state.get("v177_manual_area_text", "")
        add_many(_v177_split_manual_area_text(manual), "manual_text_v177")
    except Exception as e:
        debug.append({"source": "manual_text_error", "name": str(e)})

    # 重複削除。ただし順番は維持。
    deduped = []
    seen = set()
    for nm in raw:
        key = str(nm).strip()
        if key and key not in seen:
            seen.add(key)
            deduped.append(key)

    st.session_state["v177_area_name_debug_sources"] = debug
    st.session_state["v177_area_name_debug_final"] = deduped
    return deduped


def _v170_selected_area_groups() -> List[Dict[str, Any]]:  # type: ignore[override]
    """v177: 画像取得対象の町名グループを、必ず可視化できる形で作る。"""
    raw_names = _v177_collect_raw_area_names_for_image()

    groups: Dict[Tuple[str, str, str], Dict[str, Any]] = {}
    parse_debug: List[Dict[str, str]] = []
    for name in raw_names:
        info = _v170_parse_area_name(name)
        if not info:
            parse_debug.append({"raw": str(name), "parse": "NG"})
            continue
        parse_debug.append({"raw": str(name), "parse": f"OK: {info['pref']} {info['city']} {info['town']} {info.get('chome','')}"})
        key = (info["pref"], info["city"], info["town"])
        g = groups.setdefault(key, {
            "pref": info["pref"],
            "city": info["city"],
            "town": info["town"],
            "chomes": set(),
            "areas": [],
            "town_key": f"{info['pref']} {info['city']} {info['town']}",
        })
        if info.get("chome"):
            g["chomes"].add(info["chome"])
        g["areas"].append(info["raw"])

    out = list(groups.values())
    for g in out:
        g["areas"] = list(dict.fromkeys(g.get("areas", [])))
    st.session_state["v177_area_parse_debug"] = parse_debug
    st.session_state["v177_area_groups_debug"] = [
        {
            "pref": g.get("pref"),
            "city": g.get("city"),
            "town": g.get("town"),
            "chomes": "・".join(sorted(g.get("chomes") or [])) or "全域",
            "areas": " / ".join(g.get("areas") or []),
        }
        for g in out
    ]
    return out


def render_selected_area_livable_sign_images_v170() -> None:  # type: ignore[override]
    st.divider()
    st.subheader("マンション名看板画像 v178（丁目表記ゆれ修正版）")
    st.caption("v169で合格した画像取得ロジックは維持し、失敗していた『軌跡生成→町名受け渡し』だけを可視化して潰します。")

    with st.expander("選択済み/生成済み町丁目 → マンション名看板画像を自動取得", expanded=True):
        groups = _v170_selected_area_groups()

        if groups:
            st.success("画像取得対象の町名を検出しました。下の対象でリバブル町名ページへ進みます。")
            for g in groups:
                ch = "・".join(sorted(g.get("chomes") or [])) or "全域"
                st.write(f"- {g.get('pref')} {g.get('city')} {g.get('town')}（{ch}）")
        else:
            st.error("画像取得対象の町名を自動検出できませんでした。ここで止めます。空のまま処理には進ませません。")
            st.info("生成済みルート・選択候補・登録済み範囲・session文字列・座標逆引きまで確認しました。必要なら下の保険欄に 例: 千葉県 柏市 旭町一丁目 を1行ずつ入れてください。")

        with st.expander("取得対象の診断 / 保険入力", expanded=not bool(groups)):
            default_manual = st.session_state.get("v177_manual_area_text", "")
            st.text_area(
                "保険用：町丁目を1行ずつ直接指定（通常は空でOK）",
                value=default_manual,
                key="v177_manual_area_text",
                height=90,
                placeholder="例:\n千葉県 柏市 旭町一丁目\n千葉県 柏市 旭町二丁目",
            )
            st.write("検出された生町名:", st.session_state.get("v177_area_name_debug_final", []))
            st.write("解析結果:", st.session_state.get("v177_area_parse_debug", []))
            st.write("取得元ログ:", st.session_state.get("v177_area_name_debug_sources", []))
            st.write("生成済みルート点数:", len(st.session_state.get("last_generated_route_v118", []) or []))
            st.write("登録済み配布範囲件数:", len(st.session_state.get("route_boundaries_v118", []) or []))
            st.write("選択中境界名:", st.session_state.get("boundary_line_names_v174", []))
            st.write("生成時保存名:", st.session_state.get("last_generated_area_names_v173", []))

        # 保険欄を入力した直後はgroupsが古いので、再計算ボタンを兼ねる
        if not groups:
            st.warning("対象町名が空なので、ここでは取得ボタンを出しません。保険欄を入れた場合は画面が再読込された後に取得ボタンが出ます。")
            return

        c1, c2, c3 = st.columns(3)
        max_details_per_town = int(c1.number_input("町名ごとの詳細取得上限", 1, 80, 30, 1, key="v170_max_details_per_town"))
        max_show = int(c2.number_input("表示上限", 1, 120, 60, 1, key="v170_max_show"))
        delay = float(c3.number_input("詳細ページ間隔 秒", 0.0, 3.0, 0.15, 0.05, key="v170_delay"))
        run = st.button("この対象でマンション名看板画像を取得（v178）", type="primary", use_container_width=True, key="v178_run")

        if run:
            # v178: 前回の結果を一度クリア。空結果の時に古い/無表示で混乱しないようにする。
            st.session_state["v170_livable_results"] = []
            st.session_state["v170_livable_sign_map"] = {}
            st.session_state["v170_livable_rows"] = []
            st.session_state["v170_livable_metas"] = []
            st.session_state["v170_livable_errors"] = []
            st.session_state["v178_last_attempt_summary"] = {}
            all_rows: List[MansionRowV170] = []
            metas = []
            town_errors = []
            with st.spinner("リバブル町名ページから詳細ページ一覧を取得中..."):
                for g in groups:
                    town_url = _v170_town_page_url_for_group(g)
                    town_key = f"{g.get('pref')} {g.get('city')} {g.get('town')}"
                    if not town_url:
                        town_errors.append(f"{town_key}: リバブル町名ページURLを見つけられませんでした")
                        continue
                    try:
                        html, final_url, status = _v170_fetch_html(town_url)
                        rows, meta = _v170_parse_livable_town_page(html, final_url, town_key=town_key)
                        rows = [r for r in rows if _v170_addr_matches_group(r.address, g)]
                        metas.append({**meta, "town_url": final_url, "after_chome_filter": len(rows)})
                        all_rows.extend(rows[:max_details_per_town])
                    except Exception as e:
                        town_errors.append(f"{town_key}: {e}")

            unique_rows = []
            seen = set()
            for r in all_rows:
                if r.detail_url in seen:
                    continue
                seen.add(r.detail_url)
                r.no = len(unique_rows) + 1
                unique_rows.append(r)

            st.session_state["v178_last_attempt_summary"] = {
                "town_groups": [f"{g.get('pref')} {g.get('city')} {g.get('town')}（{'・'.join(sorted(g.get('chomes') or [])) or '全域'}）" for g in groups],
                "town_page_errors": list(town_errors),
                "town_page_logs": metas,
                "detail_rows_after_filter": len(unique_rows),
            }

            sign_map: Dict[int, List[LivableImageV170]] = {}
            results: List[MansionSignResultV170] = []
            progress = st.progress(0.0, text="詳細ページからマンション名画像を取得中...")
            for idx, row in enumerate(unique_rows, start=1):
                progress.progress((idx - 1) / max(1, len(unique_rows)), text=f"{idx}/{len(unique_rows)} {row.name} を確認中...")
                signs, warning = _v170_read_detail_for_signs(row)
                sign_map[row.no] = signs
                results.append(MansionSignResultV170(
                    no=row.no,
                    name=row.name,
                    address=row.address,
                    chome=row.chome,
                    detail_url=row.detail_url,
                    sign_count=len(signs),
                    sign_urls=" | ".join(img.url for img in signs),
                    status="OK" if signs else "NO_SIGN_IMAGE",
                    warning=warning,
                    town_key=row.town_key,
                ))
                if delay:
                    time.sleep(float(delay))
            progress.progress(1.0, text="取得完了")

            st.session_state["v170_livable_results"] = results
            st.session_state["v170_livable_sign_map"] = sign_map
            st.session_state["v170_livable_rows"] = unique_rows
            st.session_state["v170_livable_metas"] = metas
            st.session_state["v170_livable_errors"] = town_errors

        results: List[MansionSignResultV170] = st.session_state.get("v170_livable_results", []) or []
        sign_map: Dict[int, List[LivableImageV170]] = st.session_state.get("v170_livable_sign_map", {}) or {}
        metas = st.session_state.get("v170_livable_metas", []) or []
        errors = st.session_state.get("v170_livable_errors", []) or []
        if errors:
            for e in errors:
                st.warning(e)
        if results:
            sign_ok = sum(1 for r in results if r.sign_count > 0)
            st.success(f"取得完了：詳細ページ {len(results)}件 / マンション名画像あり {sign_ok}件")
            if metas:
                with st.expander("町名ページ取得ログ", expanded=False):
                    if _pd_v170 is not None:
                        st.dataframe(_pd_v170.DataFrame(metas), use_container_width=True, hide_index=True)
                    else:
                        st.write(metas)
            st.download_button(
                "マンション名看板画像CSVをダウンロード",
                data=_v170_results_to_csv_bytes(results),
                file_name="livable_selected_area_sign_images_v178.csv",
                mime="text/csv",
                use_container_width=True,
                key="v178_csv",
            )
            _v170_render_sign_cards(results, sign_map, int(st.session_state.get("v170_max_show", 60)))
        else:
            summary = st.session_state.get("v178_last_attempt_summary", {}) or {}
            if summary:
                st.warning("取得結果が0件でした。下に原因確認用のログを表示します。")
                with st.expander("v178 取得ログ", expanded=True):
                    st.write("対象町名:", summary.get("town_groups", []))
                    st.write("町名ページエラー:", summary.get("town_page_errors", []))
                    st.write("町名ページ取得ログ:", summary.get("town_page_logs", []))
                    st.write("丁目フィルタ後の詳細ページ件数:", summary.get("detail_rows_after_filter", 0))
            else:
                st.info("対象町名が表示されている場合は、上の取得ボタンでマンション名看板画像を取得します。")



# ==================================================
# v179 OVERRIDE: 表示整理・丁目順/町名順ソート
# 目的:
# - v178で成功した看板画像取得ロジックは触らない
# - 結果カードから重複する「町丁目」表示を削除
# - 取得結果を 町名あいうえお順 → 丁目順 → 住所 → マンション名 で並べる
# - 左側の検索候補も、可能な範囲で町名あいうえお順・丁目順へ寄せる
# ==================================================

_V179_TOWN_YOMI = {
    "あけぼの": "あけぼの",
    "明原": "あけはら",
    "旭町": "あさひちょう",
    "大室": "おおむろ",
    "柏": "かしわ",
    "柏の葉": "かしわのは",
    "篠籠田": "しこだ",
    "高田": "たかた",
    "中央": "ちゅうおう",
    "中央町": "ちゅうおうちょう",
    "千代田": "ちよだ",
    "豊四季": "とよしき",
    "豊住": "とよすみ",
    "富里": "とみさと",
    "根戸": "ねど",
    "東": "ひがし",
    "東上町": "ひがしかみちょう",
    "松葉町": "まつばちょう",
    "南柏": "みなみかしわ",
}


def _v179_town_yomi(town: str) -> str:
    t = _v170_normalize_text(town or "").replace(" ", "")
    return _V179_TOWN_YOMI.get(t, t)


def _v179_chome_num(chome_or_address: str) -> int:
    nums = _v178_extract_chome_numbers_from_text(chome_or_address or "")
    if not nums:
        return 999
    try:
        return min(int(x) for x in nums)
    except Exception:
        return 999


def _v179_candidate_sort_key(p: Dict[str, Any]) -> Tuple[str, str, str, int, str]:
    try:
        label = short_place_name(p)
    except Exception:
        label = str(p.get("display_name", "") or p.get("name", "") or "") if isinstance(p, dict) else str(p)
    info = _v170_parse_area_name(label) or {}
    pref = info.get("pref", "")
    city = info.get("city", "")
    town = info.get("town", "")
    chome = info.get("chome", "")
    # 解析できない候補は従来の自然順へ逃がす
    return (pref, city, _v179_town_yomi(town), _v179_chome_num(chome or label), _natural_town_key(label))


def _v179_sort_candidates(candidates: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    try:
        return sorted(list(candidates or []), key=_v179_candidate_sort_key)
    except Exception:
        return candidates or []


def _v179_group_sort_key(g: Dict[str, Any]) -> Tuple[str, str, str]:
    return (str(g.get("pref", "")), str(g.get("city", "")), _v179_town_yomi(str(g.get("town", ""))))


def _v179_row_sort_key(r: MansionRowV170) -> Tuple[str, int, str, str]:
    return (_v179_town_yomi((r.town_key or "").split()[-1] if r.town_key else ""), _v179_chome_num(r.chome or r.address), r.address or "", r.name or "")


def _v179_result_sort_key(r: MansionSignResultV170) -> Tuple[str, int, str, str]:
    return (_v179_town_yomi((r.town_key or "").split()[-1] if r.town_key else ""), _v179_chome_num(r.chome or r.address), r.address or "", r.name or "")


def _v179_sort_rows_and_renumber(rows: List[MansionRowV170]) -> List[MansionRowV170]:
    out = sorted(list(rows or []), key=_v179_row_sort_key)
    for i, r in enumerate(out, start=1):
        r.no = i
    return out


def _v179_sort_results_and_signmap(results: List[MansionSignResultV170], sign_map: Dict[int, List[LivableImageV170]]) -> Tuple[List[MansionSignResultV170], Dict[int, List[LivableImageV170]]]:
    old_by_key = {r.no: r for r in results or []}
    sorted_results = sorted(list(results or []), key=_v179_result_sort_key)
    new_map: Dict[int, List[LivableImageV170]] = {}
    for new_no, r in enumerate(sorted_results, start=1):
        old_no = r.no
        r.no = new_no
        new_map[new_no] = sign_map.get(old_no, [])
    return sorted_results, new_map


def _v179_area_display(g: Dict[str, Any]) -> str:
    chomes = sorted(list(g.get("chomes") or []), key=_v179_chome_num)
    ch = "・".join(chomes) if chomes else "全域"
    return f"{g.get('pref')} {g.get('city')} {g.get('town')}（{ch}）"


def _v170_render_sign_cards(results: List[MansionSignResultV170], sign_map: Dict[int, List[LivableImageV170]], max_show: int):  # type: ignore[override]
    st.markdown("#### マンション名画像 取得結果")
    for r in results[:max_show]:
        with st.container(border=True):
            st.markdown(f"### {r.no}. {r.name}")
            st.write(f"住所：{r.address}")
            # v179: 住所に丁目が入っているので、重複する「町丁目：○丁目」は表示しない。
            signs = sign_map.get(r.no, [])
            if not signs:
                st.warning("マンション名画像：未取得")
                if r.warning:
                    st.caption(f"理由：{r.warning}")
            else:
                cols = st.columns(min(3, max(1, len(signs))))
                for i, img in enumerate(signs[:3]):
                    with cols[i % len(cols)]:
                        st.image(img.url, caption=img.context or "マンション名", use_container_width=True)
                        st.link_button("画像を開く", img.url, key=f"v179_img_{r.no}_{i}_{abs(hash(img.url))}")
            st.link_button("元ページを開く", r.detail_url, key=f"v179_page_{r.no}_{abs(hash(r.detail_url))}")


def render_selected_area_livable_sign_images_v170() -> None:  # type: ignore[override]
    st.divider()
    st.subheader("マンション名看板画像 v179（表示整理・丁目順ソート版）")
    st.caption("v178で通った看板画像取得は維持し、表示を整理しました。結果は町名順・丁目順に並べます。")

    with st.expander("選択済み/生成済み町丁目 → マンション名看板画像を自動取得", expanded=True):
        groups = _v170_selected_area_groups()
        groups = sorted(groups, key=_v179_group_sort_key)

        if groups:
            st.success("画像取得対象の町名を検出しました。下の対象でリバブル町名ページへ進みます。")
            for g in groups:
                st.write(f"- {_v179_area_display(g)}")
        else:
            st.error("画像取得対象の町名を自動検出できませんでした。ここで止めます。空のまま処理には進ませません。")
            st.info("必要なら下の保険欄に 例: 千葉県 柏市 旭町一丁目 を1行ずつ入れてください。")

        with st.expander("取得対象の診断 / 保険入力", expanded=not bool(groups)):
            default_manual = st.session_state.get("v177_manual_area_text", "")
            st.text_area(
                "保険用：町丁目を1行ずつ直接指定（通常は空でOK）",
                value=default_manual,
                key="v177_manual_area_text",
                height=90,
                placeholder="例:\n千葉県 柏市 旭町一丁目\n千葉県 柏市 旭町二丁目",
            )
            st.write("検出された生町名:", st.session_state.get("v177_area_name_debug_final", []))
            st.write("解析結果:", st.session_state.get("v177_area_parse_debug", []))
            st.write("取得元ログ:", st.session_state.get("v177_area_name_debug_sources", []))

        if not groups:
            st.warning("対象町名が空なので、ここでは取得ボタンを出しません。")
            return

        c1, c2, c3 = st.columns(3)
        max_details_per_town = int(c1.number_input("町名ごとの詳細取得上限", 1, 80, 30, 1, key="v170_max_details_per_town"))
        max_show = int(c2.number_input("表示上限", 1, 120, 60, 1, key="v170_max_show"))
        delay = float(c3.number_input("詳細ページ間隔 秒", 0.0, 3.0, 0.15, 0.05, key="v170_delay"))
        run = st.button("この対象でマンション名看板画像を取得（v179）", type="primary", use_container_width=True, key="v179_run")

        if run:
            st.session_state["v170_livable_results"] = []
            st.session_state["v170_livable_sign_map"] = {}
            st.session_state["v170_livable_rows"] = []
            st.session_state["v170_livable_metas"] = []
            st.session_state["v170_livable_errors"] = []
            st.session_state["v178_last_attempt_summary"] = {}
            all_rows: List[MansionRowV170] = []
            metas = []
            town_errors = []
            with st.spinner("リバブル町名ページから詳細ページ一覧を取得中..."):
                for g in groups:
                    town_url = _v170_town_page_url_for_group(g)
                    town_key = f"{g.get('pref')} {g.get('city')} {g.get('town')}"
                    if not town_url:
                        town_errors.append(f"{town_key}: リバブル町名ページURLを見つけられませんでした")
                        continue
                    try:
                        html, final_url, status = _v170_fetch_html(town_url)
                        rows, meta = _v170_parse_livable_town_page(html, final_url, town_key=town_key)
                        rows = [r for r in rows if _v170_addr_matches_group(r.address, g)]
                        rows = _v179_sort_rows_and_renumber(rows)
                        metas.append({**meta, "town_url": final_url, "after_chome_filter": len(rows)})
                        all_rows.extend(rows[:max_details_per_town])
                    except Exception as e:
                        town_errors.append(f"{town_key}: {e}")

            unique_rows = []
            seen = set()
            for r in _v179_sort_rows_and_renumber(all_rows):
                if r.detail_url in seen:
                    continue
                seen.add(r.detail_url)
                unique_rows.append(r)
            unique_rows = _v179_sort_rows_and_renumber(unique_rows)

            st.session_state["v178_last_attempt_summary"] = {
                "town_groups": [_v179_area_display(g) for g in groups],
                "town_page_errors": list(town_errors),
                "town_page_logs": metas,
                "detail_rows_after_filter": len(unique_rows),
            }

            sign_map: Dict[int, List[LivableImageV170]] = {}
            results: List[MansionSignResultV170] = []
            progress = st.progress(0.0, text="詳細ページからマンション名画像を取得中...")
            for idx, row in enumerate(unique_rows, start=1):
                progress.progress((idx - 1) / max(1, len(unique_rows)), text=f"{idx}/{len(unique_rows)} {row.name} を確認中...")
                signs, warning = _v170_read_detail_for_signs(row)
                sign_map[row.no] = signs
                results.append(MansionSignResultV170(
                    no=row.no,
                    name=row.name,
                    address=row.address,
                    chome=row.chome,
                    detail_url=row.detail_url,
                    sign_count=len(signs),
                    sign_urls=" | ".join(img.url for img in signs),
                    status="OK" if signs else "NO_SIGN_IMAGE",
                    warning=warning,
                    town_key=row.town_key,
                ))
                if delay:
                    time.sleep(float(delay))
            progress.progress(1.0, text="取得完了")

            results, sign_map = _v179_sort_results_and_signmap(results, sign_map)
            st.session_state["v170_livable_results"] = results
            st.session_state["v170_livable_sign_map"] = sign_map
            st.session_state["v170_livable_rows"] = unique_rows
            st.session_state["v170_livable_metas"] = metas
            st.session_state["v170_livable_errors"] = town_errors

        results: List[MansionSignResultV170] = st.session_state.get("v170_livable_results", []) or []
        sign_map: Dict[int, List[LivableImageV170]] = st.session_state.get("v170_livable_sign_map", {}) or {}
        metas = st.session_state.get("v170_livable_metas", []) or []
        errors = st.session_state.get("v170_livable_errors", []) or []
        if errors:
            for e in errors:
                st.warning(e)
        if results:
            sign_ok = sum(1 for r in results if r.sign_count > 0)
            st.success(f"取得完了：詳細ページ {len(results)}件 / マンション名画像あり {sign_ok}件")
            if metas:
                with st.expander("町名ページ取得ログ", expanded=False):
                    if _pd_v170 is not None:
                        st.dataframe(_pd_v170.DataFrame(metas), use_container_width=True, hide_index=True)
                    else:
                        st.write(metas)
            st.download_button(
                "マンション名看板画像CSVをダウンロード",
                data=_v170_results_to_csv_bytes(results),
                file_name="livable_selected_area_sign_images_v179.csv",
                mime="text/csv",
                use_container_width=True,
                key="v179_csv",
            )
            _v170_render_sign_cards(results, sign_map, int(st.session_state.get("v170_max_show", 60)))
        else:
            summary = st.session_state.get("v178_last_attempt_summary", {}) or {}
            if summary:
                st.warning("取得結果が0件でした。下に原因確認用のログを表示します。")
                with st.expander("v179 取得ログ", expanded=True):
                    st.write("対象町名:", summary.get("town_groups", []))
                    st.write("町名ページエラー:", summary.get("town_page_errors", []))
                    st.write("町名ページ取得ログ:", summary.get("town_page_logs", []))
                    st.write("丁目フィルタ後の詳細ページ件数:", summary.get("detail_rows_after_filter", 0))
            else:
                st.info("対象町名が表示されている場合は、上の取得ボタンでマンション名看板画像を取得します。")



# ==================================================
# v180 OVERRIDE: 候補検索の厳密化・町名あいうえお順/丁目順の安定化
# 目的:
# - 「戸塚」と打った時に、横浜市戸塚区内というだけの「原宿」「南舞岡」等を出さない
# - 入力文字が町名に入っている候補だけを優先表示する
# - 「市名だけ検索」は従来通り市内一覧を出す
# - 候補リストを 町名あいうえお順 → 丁目順 に並べる
# ==================================================

_V180_TOWN_YOMI_EXTRA = {
    # 川口・戸塚系。候補検索でよく使う町名を先に読み順へ寄せる。
    "戸塚": "とつか",
    "戸塚東": "とつかひがし",
    "戸塚南": "とつかみなみ",
    "戸塚境町": "とつかさかいちょう",
    "東川口": "ひがしかわぐち",
    "長蔵": "ちょうぞう",
    "差間": "さしま",
    "北原台": "きたはらだい",
    "久左衛門新田": "きゅうざえもんしんでん",
    # 既存柏系もここで明示しておく
    "旭町": "あさひちょう",
    "あけぼの": "あけぼの",
    "明原": "あけはら",
    "大室": "おおむろ",
    "豊四季": "とよしき",
    "豊住": "とよすみ",
}
try:
    _V179_TOWN_YOMI.update(_V180_TOWN_YOMI_EXTRA)
except Exception:
    pass

_V180_KANA_TO_KANJI_HINTS = {
    "とつか": "戸塚",
    "トツカ": "戸塚",
    "あさひ": "旭町",
    "あさひちょう": "旭町",
    "あけぼの": "あけぼの",
}


def _v180_query_variants(q: str) -> List[str]:
    q0 = str(q or "").strip()
    vars_: List[str] = []
    for x in [q0, _V180_KANA_TO_KANJI_HINTS.get(q0, "")]:
        x = str(x or "").strip()
        if x and x not in vars_:
            vars_.append(x)
    # 正規化文字列も重複なしで保持
    out: List[str] = []
    for x in vars_:
        nx = _normalize_jp(x)
        if nx and nx not in out:
            out.append(nx)
    return out


def _v180_find_pref_city_for_query(query: str, records: Sequence[Dict[str, Any]]) -> Tuple[str, str, str, bool]:
    """queryを pref/city/town_q に分ける。

    重要: 「戸塚」は横浜市戸塚区の市区名の一部だが、市区名検索として扱わない。
    「横浜市戸塚区」「柏市」のように市区名を明示した時だけ city_only を許す。
    """
    qnorm = _normalize_jp(query)
    pref = ""
    city = ""

    prefs = sorted({r.get("pref", "") for r in records if r.get("pref")}, key=len, reverse=True)
    for p in prefs:
        pn = _normalize_jp(p)
        if pn and qnorm.startswith(pn):
            pref = p
            qnorm_no_pref = qnorm[len(pn):]
            break
    else:
        qnorm_no_pref = qnorm

    cities = sorted({r.get("city", "") for r in records if r.get("city")}, key=len, reverse=True)

    # 1) 市区町村名を明示している場合だけ exact city 扱い
    explicit_city = False
    for c in cities:
        cn = _normalize_jp(c)
        if not cn:
            continue
        if qnorm_no_pref == cn or qnorm == _normalize_jp((pref or "") + c):
            city = c
            qnorm_no_pref = ""
            explicit_city = True
            break
        # 「戸塚区」のように区まで入れている場合は市区検索として許可
        if qnorm_no_pref.endswith(("市", "区", "町", "村")) and cn.endswith(qnorm_no_pref):
            city = c
            qnorm_no_pref = ""
            explicit_city = True
            break

    # 2) 「川口市戸塚」のように市名＋町名が入っている場合
    if not city:
        for c in cities:
            cn = _normalize_jp(c)
            if cn and cn in qnorm_no_pref:
                city = c
                qnorm_no_pref = qnorm_no_pref.replace(cn, "", 1)
                explicit_city = False
                break

    town_q = qnorm_no_pref
    return pref, city, town_q, explicit_city


def _v180_town_matches_query(town: str, town_query_norms: Sequence[str]) -> bool:
    tn = _normalize_jp(town)
    if not town_query_norms:
        return True
    return any(q and q in tn for q in town_query_norms)


def local_boundary_search_candidates_v126(query: str, limit: int = 250) -> List[Dict[str, Any]]:  # type: ignore[override]
    """v180: 町名検索を厳密化。

    旧版では「戸塚」と入力すると、横浜市戸塚区の市区名に反応して
    原宿・南舞岡・平戸など、町名に戸塚を含まない候補まで出ていた。
    v180では、町名入力らしい検索は town_r の中身だけで判定する。
    """
    records = load_local_boundary_candidates_v126()
    if not records:
        return []

    q_raw = str(query or "").strip()
    if not q_raw:
        return []

    pref, city, town_q, explicit_city = _v180_find_pref_city_for_query(q_raw, records)
    town_query_norms = _v180_query_variants(town_q or q_raw)

    out: List[Dict[str, Any]] = []
    for r in records:
        pref_r = r.get("pref", "")
        city_r = r.get("city", "")
        town_r = r.get("short_name", "")

        if pref and pref != pref_r:
            continue
        if city and city != city_r:
            continue

        if explicit_city and not town_q:
            # 「柏市」「横浜市戸塚区」のような市区町村名だけの検索は市区内全部。
            pass
        else:
            # 「戸塚」「川口市戸塚」「旭町」などは必ず町名本体に検索語が入るものだけ。
            if not _v180_town_matches_query(town_r, town_query_norms):
                continue

        out.append(r)

    out = _v180_sort_local_candidates(out)
    return out[:limit]


def _v180_sort_local_candidates(items: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    def key(r: Dict[str, Any]):
        town = str(r.get("short_name", ""))
        base_key = _natural_town_key(town)
        base = str(base_key[0]) if isinstance(base_key, tuple) else town
        ch = base_key[1] if isinstance(base_key, tuple) and len(base_key) > 1 else 999
        return (str(r.get("pref", "")), str(r.get("city", "")), _v179_town_yomi(base), int(ch or 999), town)
    return sorted(list(items or []), key=key)


def _v180_candidate_sort_key(p: Dict[str, Any]) -> Tuple[str, str, str, int, str]:
    try:
        label = short_place_name(p)
    except Exception:
        label = str(p.get("display_name", "") or p.get("name", "") or "") if isinstance(p, dict) else str(p)

    town_name = str(p.get("short_name", "") or label) if isinstance(p, dict) else label
    nk = _natural_town_key(town_name)
    base = str(nk[0]) if isinstance(nk, tuple) else town_name
    ch = nk[1] if isinstance(nk, tuple) and len(nk) > 1 else _v179_chome_num(town_name)
    pref = str(p.get("pref", "")) if isinstance(p, dict) else ""
    city = str(p.get("city", "")) if isinstance(p, dict) else ""
    return (pref, city, _v179_town_yomi(base), int(ch or 999), town_name)


def _v179_sort_candidates(candidates: List[Dict[str, Any]]) -> List[Dict[str, Any]]:  # type: ignore[override]
    try:
        return sorted(list(candidates or []), key=_v180_candidate_sort_key)
    except Exception:
        return candidates or []


def smart_search_place_candidates(query: str) -> List[Dict[str, Any]]:  # type: ignore[override]
    """v180: ローカル町丁目候補を厳密検索。無い場合だけNominatimへフォールバック。"""
    q = (query or "").strip()
    if not q:
        raise ValueError("検索語が空です")

    local_items = local_boundary_search_candidates_v126(q, limit=300)
    if local_items:
        return local_items

    # ここから下は従来フォールバック。ただし候補が広がりすぎるため最後に並び替える。
    all_items: List[Dict[str, Any]] = []
    all_items.extend(_nominatim_get(q, limit=12))

    chome_words = ["一", "二", "三", "四", "五", "六", "七", "八", "九", "十", "十一", "十二"]
    if "丁目" not in q and not re.search(r"\d+\s*丁目", q):
        for i, k in enumerate(chome_words, start=1):
            variants = [f"{q}{i}丁目", f"{q}{k}丁目"]
            for v in variants:
                try:
                    all_items.extend(_nominatim_get(v, limit=2))
                    time.sleep(0.05)
                except Exception:
                    pass

    items = _dedupe_places(all_items)
    qnorms = _v180_query_variants(q)
    # Nominatimでも、町名入力らしい場合は候補名に検索語が入るものを優先。全部消える場合だけ元に戻す。
    filtered = []
    for x in items:
        label = short_place_name(x)
        if any(qn and qn in _normalize_jp(label) for qn in qnorms):
            filtered.append(x)
    if filtered:
        items = filtered

    def score(x: Dict[str, Any]) -> Tuple[int, int, int, str]:
        disp = x.get("display_name", "")
        cls = x.get("class", "")
        typ = x.get("type", "")
        has_poly = 1 if _has_polygon_geojson(x) else 0
        has_chome = 1 if "丁目" in disp else 0
        residentialish = 1 if cls in ("boundary", "place") or typ in ("administrative", "quarter", "neighbourhood", "suburb") else 0
        return (-has_poly, -has_chome, -residentialish, short_place_name(x))
    items.sort(key=score)
    return items[:30]


# ==================================================
# v181 OVERRIDE: 他地域対応のためのリバブル市区町村ページ自動解決 + 町名解析強化
# 目的:
# - v178で成功した「詳細ページ→マンション名画像取得」は触らない
# - v179/v180で詰まった「他地域の町名ページURLが見つからない」を潰す
# - 柏市だけの固定URL辞書に依存せず、都県slug + 市区町村コードから
#   リバブル市区町村ページ aXXXXX を作り、そこから町名リンクを探す
# - 横浜市戸塚区のような「市＋区」を、横浜市ではなく横浜市戸塚区として読む
# ==================================================

_V181_PREF_SLUGS = {
    "東京都": "tokyo",
    "神奈川県": "kanagawa",
    "埼玉県": "saitama",
    "千葉県": "chiba",
    "茨城県": "ibaraki",
    "栃木県": "tochigi",
    "群馬県": "gunma",
    "山梨県": "yamanashi",
}

# GeoJSONに市区町村コードが無い/読めない場合の実用保険。
# よく使う関東圏だけ先に入れる。コードが取れる場合はそちらを優先。
_V181_KNOWN_CITY_CODES = {
    ("千葉県", "柏市"): "12217",
    ("千葉県", "我孫子市"): "12222",
    ("千葉県", "松戸市"): "12207",
    ("千葉県", "流山市"): "12220",
    ("千葉県", "市川市"): "12203",
    ("千葉県", "船橋市"): "12204",
    ("埼玉県", "川口市"): "11203",
    ("埼玉県", "三郷市"): "11237",
    ("埼玉県", "越谷市"): "11222",
    ("埼玉県", "八潮市"): "11234",
    ("埼玉県", "草加市"): "11221",
    ("神奈川県", "横浜市戸塚区"): "14110",
    ("神奈川県", "横浜市港南区"): "14111",
    ("神奈川県", "横浜市旭区"): "14112",
    ("東京都", "葛飾区"): "13122",
    ("東京都", "足立区"): "13121",
    ("東京都", "江戸川区"): "13123",
    ("茨城県", "つくば市"): "08220",
    ("茨城県", "取手市"): "08217",
    ("茨城県", "守谷市"): "08224",
}

_V181_CODE_CACHE: Dict[Tuple[str, str], Optional[str]] = {}
_V181_TOWN_URL_CACHE: Dict[Tuple[str, str, str], Optional[str]] = {}


def _v181_compact(s: str) -> str:
    return _v170_normalize_text(str(s or "")).replace(" ", "").replace("　", "")


def _v181_pref_slug(pref: str) -> str:
    return _V181_PREF_SLUGS.get(_v181_compact(pref), "")


def _v181_boundary_city_names() -> List[str]:
    names = set()
    try:
        for r in load_local_boundary_candidates_v126() or []:
            c = _v181_compact(r.get("city", ""))
            if c:
                names.add(c)
    except Exception:
        pass
    try:
        for _p, c in list(_V181_KNOWN_CITY_CODES.keys()) + list(_V170_LIVABLE_CITY_URLS.keys()):
            c2 = _v181_compact(c)
            if c2:
                names.add(c2)
    except Exception:
        pass
    return sorted(names, key=len, reverse=True)


def _v181_city_code_from_geojson(pref: str, city: str) -> Optional[str]:
    pref_c = _v181_compact(pref)
    city_c = _v181_compact(city)
    key = (pref_c, city_c)
    if key in _V181_CODE_CACHE:
        return _V181_CODE_CACHE[key]

    code_keys = [
        "CITY_CODE", "city_code", "市区町村コード", "全国地方公共団体コード",
        "N03_007", "JISCODE", "JIS_CODE", "jiscode", "KEY_CODE", "行政区域コード",
    ]
    pref_keys = ["PREF_NAME", "pref_name", "都道府県名", "PREF", "N03_001", "都道府県"]
    city_keys = ["CITY_NAME", "city_name", "市区町村名", "CITY", "city", "N03_004", "行政区名", "市区町村"]

    found: Optional[str] = None
    try:
        for cand in _local_boundary_paths():
            if not cand.exists():
                continue
            data = json.loads(cand.read_text(encoding="utf-8"))
            for f in data.get("features", []) or []:
                props = f.get("properties", {}) or {}
                p = _v181_compact(_get_prop_any(props, pref_keys, ""))
                c = _v181_compact(_get_prop_any(props, city_keys, ""))
                if p != pref_c or c != city_c:
                    continue
                raw_code = _get_prop_any(props, code_keys, "")
                m = re.search(r"(\d{5})", str(raw_code or ""))
                if m:
                    found = m.group(1)
                    break
            if found:
                break
    except Exception:
        found = None

    if not found:
        found = _V181_KNOWN_CITY_CODES.get((pref_c, city_c))
    _V181_CODE_CACHE[key] = found
    return found


def _v181_city_page_url(pref: str, city: str) -> Optional[str]:
    pref_c, city_c = _v181_compact(pref), _v181_compact(city)
    if (pref_c, city_c) in _V170_LIVABLE_CITY_URLS:
        return _V170_LIVABLE_CITY_URLS[(pref_c, city_c)]
    slug = _v181_pref_slug(pref_c)
    code = _v181_city_code_from_geojson(pref_c, city_c)
    if not slug or not code:
        return None
    return f"https://www.livable.co.jp/mansion/library/{slug}/a{code}/"


def _v181_town_link_matches(text: str, href: str, town: str) -> bool:
    tx = _v181_compact(text)
    tn = _v181_compact(town)
    if not tn:
        return False
    # 町名リンクは基本的に「あけぼの」「旭町」「戸塚町」のように町名そのもの。
    # 部分一致も許すが、短すぎる町名は完全一致寄りにする。
    if tx == tn:
        return True
    if len(tn) >= 2 and tn in tx:
        return True
    return False


def _v170_town_page_url_for_group(g: Dict[str, Any]) -> Optional[str]:  # type: ignore[override]
    pref = _v181_compact(g.get("pref", ""))
    city = _v181_compact(g.get("city", ""))
    town = _v181_compact(g.get("town", ""))
    key = (pref, city, town)
    if key in _V181_TOWN_URL_CACHE:
        return _V181_TOWN_URL_CACHE[key]
    if key in _V170_LIVABLE_TOWN_URLS:
        _V181_TOWN_URL_CACHE[key] = _V170_LIVABLE_TOWN_URLS[key]
        return _V181_TOWN_URL_CACHE[key]

    city_url = _v181_city_page_url(pref, city)
    if not city_url:
        _V181_TOWN_URL_CACHE[key] = None
        return None

    try:
        html, final_url, status = _v170_fetch_html(city_url)
        soup = _BeautifulSoup_v170(html, "html.parser")
        best: Optional[str] = None
        for a in soup.find_all("a", href=True):
            href = a.get("href") or ""
            if "mansion/library" not in href:
                continue
            tx = _v170_normalize_text(a.get_text(" ", strip=True))
            if _v181_town_link_matches(tx, href, town):
                best = _v170_clean_url(href, final_url)
                break
        _V181_TOWN_URL_CACHE[key] = best
        return best
    except Exception:
        _V181_TOWN_URL_CACHE[key] = None
        return None


def _v181_split_town_chome(rest: str) -> Tuple[str, str]:
    rest = _v181_compact(rest)
    m = re.search(r"(.+?)([一二三四五六七八九十１２３４５６７８９０0-9]+丁目)$", rest)
    if m:
        return m.group(1), m.group(2)
    return rest, ""


def _v181_infer_pref_city_from_town(pref: str, town: str) -> Optional[Tuple[str, str, str]]:
    pref_c = _v181_compact(pref) or "千葉県"
    town_c = _v181_compact(town)
    if not town_c:
        return None
    try:
        old = _v171_infer_pref_city_town(pref_c, town_c)
        if old:
            return old
    except Exception:
        pass

    matches = []
    try:
        for r in load_local_boundary_candidates_v126() or []:
            if _v181_compact(r.get("pref", "")) != pref_c:
                continue
            short = _v181_compact(r.get("short_name", ""))
            base, _ch = _v181_split_town_chome(short)
            if town_c == base or town_c == short or short.startswith(town_c):
                city = _v181_compact(r.get("city", ""))
                if city:
                    matches.append((pref_c, city, base or town_c))
    except Exception:
        pass
    uniq = list(dict.fromkeys(matches))
    if len(uniq) == 1:
        return uniq[0]
    return None


def _v181_parse_area_name_core(name: str) -> Optional[Dict[str, str]]:
    raw_name = str(name or "").strip()
    if not raw_name:
        return None

    # 1) 「旭町一丁目 / 柏市 / 千葉県」「戸塚町 / 横浜市戸塚区 / 神奈川県」形式
    parts = [x.strip() for x in re.split(r"[/,，]", raw_name) if x and x.strip()]
    if len(parts) >= 2:
        pref = ""
        city = ""
        town_part = ""
        city_names = _v181_boundary_city_names()
        for part in parts:
            c = _v181_compact(part)
            if c in _V170_PREFS:
                pref = c
            elif c in city_names or re.fullmatch(r".+?市.+?区", c) or re.fullmatch(r".+?[市区町村]", c):
                # 市区町村っぽいもの。ただし町名候補としてもあり得るので、町名は後で拾う。
                if not city or len(c) > len(city):
                    city = c
        for part in parts:
            c = _v181_compact(part)
            if not c or c == pref or c == city or c in {"日本", "Japan"}:
                continue
            if c in city_names:
                continue
            town_part = c
            break
        pref = pref or "千葉県"
        if town_part:
            town, chome = _v181_split_town_chome(town_part)
            if city:
                return {"pref": pref, "city": city, "town": town, "chome": chome, "raw": raw_name}
            inferred = _v181_infer_pref_city_from_town(pref, town)
            if inferred:
                ip, ic, it = inferred
                return {"pref": ip, "city": ic, "town": it, "chome": chome, "raw": raw_name}

    # 2) 通常の連結文字列「神奈川県横浜市戸塚区戸塚町」「千葉県柏市旭町一丁目」形式
    compact = _v181_compact(raw_name)
    pref = ""
    rest = compact
    for p in sorted(_V170_PREFS, key=len, reverse=True):
        if rest.startswith(p):
            pref = p
            rest = rest[len(p):]
            break
    pref = pref or "千葉県"

    city = ""
    for c in _v181_boundary_city_names():
        if rest.startswith(c):
            city = c
            rest = rest[len(c):]
            break
    if not city:
        # 横浜市戸塚区のような市+区を、市だけで切らないように先に見る。
        m_ward = re.match(r"(.+?市.+?区)(.+)$", rest)
        if m_ward:
            city = m_ward.group(1)
            rest = m_ward.group(2)
        else:
            m_city = re.match(r"(.+?[市区町村])(.+)$", rest)
            if m_city:
                city = m_city.group(1)
                rest = m_city.group(2)

    if city and rest:
        town, chome = _v181_split_town_chome(rest)
        return {"pref": pref, "city": city, "town": town, "chome": chome, "raw": raw_name}

    # 3) 市名なし「千葉県旭町一丁目」など
    town, chome = _v181_split_town_chome(rest)
    inferred = _v181_infer_pref_city_from_town(pref, town)
    if inferred:
        ip, ic, it = inferred
        return {"pref": ip, "city": ic, "town": it, "chome": chome, "raw": raw_name}
    return None


def _v170_parse_area_name(name: str) -> Optional[Dict[str, str]]:  # type: ignore[override]
    return _v181_parse_area_name_core(name)


# v181: 取得結果の無い時に「リバブル市区町村ページが未解決」なのか
# 「町名ページは取れたが丁目/看板画像で落ちた」のか見えるよう、既存表示に補足を足す。
# 本体のrenderはv179を維持し、内部関数の差し替えだけで他地域対応する。



# ==================================================
# v182 OVERRIDE: 他地域で町名が消える問題を根本修正
# 目的:
# - v178で通ったマンション名看板画像取得ロジックは触らない
# - v181で失敗した「戸塚一丁目」のような市区町村が落ちた文字列を、
#   search_candidates_v126 の structured data(pref/city/short_name) から復元する
# - 画像取得前に、対象町名と町名ページURL解決結果を画面に出し、
#   旭町以外の地域でも“町名ページに到達できているか”を先に確認できるようにする
# ==================================================


def _v182_candidate_to_area_info(p: Dict[str, Any]) -> Optional[Dict[str, str]]:
    """local_boundary候補の構造化情報から、pref/city/town/chomeを直接作る。"""
    if not isinstance(p, dict):
        return None
    pref = _v181_compact(p.get("pref", ""))
    city = _v181_compact(p.get("city", ""))
    short = _v181_compact(p.get("short_name", "") or p.get("name", "") or p.get("display_name", ""))
    if p.get("source") == "local_boundary" and pref and city and short:
        town, chome = _v181_split_town_chome(short)
        if town:
            return {"pref": pref, "city": city, "town": town, "chome": chome, "raw": f"{short} / {city} / {pref}"}

    # Nominatim候補の場合はdisplay_nameから拾える範囲で解析
    label = ""
    try:
        label = short_place_name(p)
    except Exception:
        label = str(p.get("display_name", "") or p.get("name", "") or "")
    return _v170_parse_area_name(label)


def _v182_group_add(groups: Dict[Tuple[str, str, str], Dict[str, Any]], info: Optional[Dict[str, str]], source: str, debug: List[Dict[str, str]]) -> None:
    if not info:
        debug.append({"source": source, "raw": "", "parse": "NG"})
        return
    pref = _v181_compact(info.get("pref", ""))
    city = _v181_compact(info.get("city", ""))
    town = _v181_compact(info.get("town", ""))
    chome = _v181_compact(info.get("chome", ""))
    raw = str(info.get("raw", "") or f"{pref} {city} {town}{chome}")
    if not (pref and city and town):
        debug.append({"source": source, "raw": raw, "parse": "NG: pref/city/town missing"})
        return
    key = (pref, city, town)
    g = groups.setdefault(key, {
        "pref": pref,
        "city": city,
        "town": town,
        "chomes": set(),
        "areas": [],
        "town_key": f"{pref} {city} {town}",
        "sources": set(),
    })
    if chome:
        g["chomes"].add(chome)
    g["areas"].append(raw)
    g["sources"].add(source)
    debug.append({"source": source, "raw": raw, "parse": f"OK: {pref} {city} {town} {chome}"})


def _v182_match_candidate_for_raw(raw: str, candidates: Sequence[Dict[str, Any]], selected_only: bool = False) -> List[Dict[str, Any]]:
    """市区町村が落ちた raw名（例: 戸塚一丁目）を候補リストから復元する。"""
    raw_c = _v181_compact(raw)
    if not raw_c:
        return []
    out: List[Dict[str, Any]] = []
    for p in candidates or []:
        if not isinstance(p, dict):
            continue
        short = _v181_compact(p.get("short_name", "") or "")
        label = ""
        try:
            label = _v181_compact(short_place_name(p))
        except Exception:
            label = _v181_compact(p.get("display_name", "") or "")
        if raw_c == short or raw_c == label:
            out.append(p)
    return out


def _v182_selected_candidate_records() -> List[Dict[str, Any]]:
    candidates = st.session_state.get("search_candidates_v126", []) or []
    selected_idxs = st.session_state.get("selected_candidate_idxs_v126", []) or []
    try:
        selected_idxs = [int(i) for i in selected_idxs]
    except Exception:
        selected_idxs = []
    out: List[Dict[str, Any]] = []
    for idx in selected_idxs:
        if 0 <= idx < len(candidates):
            p = candidates[idx]
            if isinstance(p, dict):
                out.append(p)
    return out


def _v170_selected_area_groups() -> List[Dict[str, Any]]:  # type: ignore[override]
    """v182: 画像取得対象を、文字列ではなく候補データ本体から組み立てる。"""
    groups: Dict[Tuple[str, str, str], Dict[str, Any]] = {}
    debug: List[Dict[str, str]] = []

    candidates = st.session_state.get("search_candidates_v126", []) or []
    selected_records = _v182_selected_candidate_records()

    # 1) 最優先: 左側で選択中の候補データそのもの。ここにはpref/city/short_nameがある。
    for p in selected_records:
        _v182_group_add(groups, _v182_candidate_to_area_info(p), "selected_candidate_record_v182", debug)

    # 2) 登録済み配布範囲・プレビュー境界・生成時保存名などの旧文字列。
    #    ただし市名が落ちた raw は、まず選択候補/候補一覧から復元する。
    raw_names: List[str] = []
    try:
        raw_names.extend(_v177_collect_raw_area_names_for_image())
    except Exception:
        try:
            raw_names.extend(_v173_collect_area_names_for_image())
        except Exception:
            pass
    for nm in (st.session_state.get("last_generated_area_names_v173", []) or []):
        if str(nm or "").strip():
            raw_names.append(str(nm).strip())

    seen_raw = set()
    for raw in raw_names:
        raw_s = str(raw or "").strip()
        if not raw_s or raw_s in seen_raw:
            continue
        seen_raw.add(raw_s)

        # 2-a) 選択候補から一致するものを探す
        matched = _v182_match_candidate_for_raw(raw_s, selected_records)
        # 2-b) 選択候補で見つからなければ候補一覧全体から探す
        if not matched:
            matched = _v182_match_candidate_for_raw(raw_s, candidates)
        if matched:
            for p in matched:
                _v182_group_add(groups, _v182_candidate_to_area_info(p), f"raw_name_matched_candidate_v182:{raw_s}", debug)
            continue

        # 2-c) それでも無理なら従来パーサーへ。ただし曖昧な市名なし町名は無理に柏市扱いしない。
        info = _v170_parse_area_name(raw_s)
        _v182_group_add(groups, info, f"raw_name_parser_v182:{raw_s}", debug)

    # 3) 手入力保険欄。これは明示情報として最後に追加。
    manual = st.session_state.get("v177_manual_area_text", "")
    try:
        for line in _v177_split_manual_area_text(manual):
            _v182_group_add(groups, _v170_parse_area_name(line), "manual_text_v182", debug)
    except Exception:
        pass

    out = list(groups.values())
    for g in out:
        g["areas"] = list(dict.fromkeys(g.get("areas", [])))
        g["sources"] = sorted(list(g.get("sources", [])))
    out = sorted(out, key=_v179_group_sort_key)

    try:
        st.session_state["v182_area_parse_debug"] = debug
        st.session_state["v182_area_groups_debug"] = [
            {
                "pref": g.get("pref"),
                "city": g.get("city"),
                "town": g.get("town"),
                "chomes": "・".join(sorted(g.get("chomes") or [])) or "全域",
                "areas": " / ".join(g.get("areas") or []),
                "sources": " / ".join(g.get("sources") or []),
            }
            for g in out
        ]
    except Exception:
        pass
    return out


def _v182_safe_town_page_url(g: Dict[str, Any]) -> Tuple[Optional[str], str]:
    """町名ページURL解決。理由を返して画面に出せるようにする。"""
    try:
        url = _v170_town_page_url_for_group(g)
        if url:
            return url, "OK"
        city_url = _v181_city_page_url(g.get("pref", ""), g.get("city", "")) if "_v181_city_page_url" in globals() else None
        if not city_url:
            return None, "市区町村ページURLを作れませんでした"
        return None, f"市区町村ページは作成OKだが、町名リンクが見つかりませんでした: {city_url}"
    except Exception as e:
        return None, f"URL解決エラー: {e}"


def _v182_render_url_resolution_table(groups: List[Dict[str, Any]]) -> None:
    logs = []
    for g in groups:
        url, reason = _v182_safe_town_page_url(g)
        logs.append({
            "対象": _v179_area_display(g),
            "町名ページURL": url or "未取得",
            "状態": reason,
        })
    st.session_state["v182_town_url_check_logs"] = logs
    if logs:
        with st.expander("v182 町名ページURL接続チェック", expanded=False):
            if _pd_v170 is not None:
                st.dataframe(_pd_v170.DataFrame(logs), use_container_width=True, hide_index=True)
            else:
                st.write(logs)


def render_selected_area_livable_sign_images_v170() -> None:  # type: ignore[override]
    st.divider()
    st.subheader("マンション名看板画像 v182（他地域接続・候補データ受け渡し修正版）")
    st.caption("旭町で通った看板画像取得は維持し、戸塚など他地域で市区町村名が落ちる問題を候補データ本体から復元します。")

    with st.expander("選択済み/生成済み町丁目 → マンション名看板画像を自動取得", expanded=True):
        groups = _v170_selected_area_groups()
        groups = sorted(groups, key=_v179_group_sort_key)

        if groups:
            st.success("画像取得対象の町名を検出しました。下の対象でリバブル町名ページへ進みます。")
            for g in groups:
                st.write(f"- {_v179_area_display(g)}")
            _v182_render_url_resolution_table(groups)
        else:
            st.error("画像取得対象の町名を自動検出できませんでした。ここで止めます。空のまま処理には進ませません。")
            st.info("候補を選択した状態で軌跡生成した場合でも、本来はここに対象町名が出る必要があります。必要なら下の保険欄に1行ずつ入れてください。")

        with st.expander("取得対象の診断 / 保険入力", expanded=not bool(groups)):
            default_manual = st.session_state.get("v177_manual_area_text", "")
            st.text_area(
                "保険用：町丁目を1行ずつ直接指定（通常は空でOK）",
                value=default_manual,
                key="v177_manual_area_text",
                height=90,
                placeholder="例:\n神奈川県 横浜市戸塚区 戸塚一丁目\n埼玉県 川口市 戸塚東一丁目\n千葉県 柏市 旭町一丁目",
            )
            st.write("v182解析結果:", st.session_state.get("v182_area_parse_debug", []))
            st.write("v182取得対象:", st.session_state.get("v182_area_groups_debug", []))
            st.write("選択中候補idx:", st.session_state.get("selected_candidate_idxs_v126", []))
            st.write("検索候補件数:", len(st.session_state.get("search_candidates_v126", []) or []))
            st.write("旧検出生町名:", st.session_state.get("v177_area_name_debug_final", []))
            st.write("生成時保存名:", st.session_state.get("last_generated_area_names_v173", []))

        if not groups:
            st.warning("対象町名が空なので、ここでは取得ボタンを出しません。")
            return

        c1, c2, c3 = st.columns(3)
        max_details_per_town = int(c1.number_input("町名ごとの詳細取得上限", 1, 80, 30, 1, key="v170_max_details_per_town"))
        max_show = int(c2.number_input("表示上限", 1, 120, 60, 1, key="v170_max_show"))
        delay = float(c3.number_input("詳細ページ間隔 秒", 0.0, 3.0, 0.15, 0.05, key="v170_delay"))
        run = st.button("この対象でマンション名看板画像を取得（v182）", type="primary", use_container_width=True, key="v182_run")

        if run:
            st.session_state["v170_livable_results"] = []
            st.session_state["v170_livable_sign_map"] = {}
            st.session_state["v170_livable_rows"] = []
            st.session_state["v170_livable_metas"] = []
            st.session_state["v170_livable_errors"] = []
            st.session_state["v178_last_attempt_summary"] = {}
            all_rows: List[MansionRowV170] = []
            metas = []
            town_errors = []
            with st.spinner("リバブル町名ページから詳細ページ一覧を取得中..."):
                for g in groups:
                    town_url, reason = _v182_safe_town_page_url(g)
                    town_key = f"{g.get('pref')} {g.get('city')} {g.get('town')}"
                    if not town_url:
                        town_errors.append(f"{town_key}: {reason}")
                        continue
                    try:
                        html, final_url, status = _v170_fetch_html(town_url)
                        rows, meta = _v170_parse_livable_town_page(html, final_url, town_key=town_key)
                        rows = [r for r in rows if _v170_addr_matches_group(r.address, g)]
                        rows = _v179_sort_rows_and_renumber(rows)
                        metas.append({**meta, "town_url": final_url, "after_chome_filter": len(rows), "target": _v179_area_display(g)})
                        all_rows.extend(rows[:max_details_per_town])
                    except Exception as e:
                        town_errors.append(f"{town_key}: {e}")

            unique_rows = []
            seen = set()
            for r in _v179_sort_rows_and_renumber(all_rows):
                if r.detail_url in seen:
                    continue
                seen.add(r.detail_url)
                unique_rows.append(r)
            unique_rows = _v179_sort_rows_and_renumber(unique_rows)

            st.session_state["v178_last_attempt_summary"] = {
                "town_groups": [_v179_area_display(g) for g in groups],
                "town_page_errors": list(town_errors),
                "town_page_logs": metas,
                "detail_rows_after_filter": len(unique_rows),
            }

            sign_map: Dict[int, List[LivableImageV170]] = {}
            results: List[MansionSignResultV170] = []
            progress = st.progress(0.0, text="詳細ページからマンション名画像を取得中...")
            for idx, row in enumerate(unique_rows, start=1):
                progress.progress((idx - 1) / max(1, len(unique_rows)), text=f"{idx}/{len(unique_rows)} {row.name} を確認中...")
                signs, warning = _v170_read_detail_for_signs(row)
                sign_map[row.no] = signs
                results.append(MansionSignResultV170(
                    no=row.no,
                    name=row.name,
                    address=row.address,
                    chome=row.chome,
                    detail_url=row.detail_url,
                    sign_count=len(signs),
                    sign_urls=" | ".join(img.url for img in signs),
                    status="OK" if signs else "NO_SIGN_IMAGE",
                    warning=warning,
                    town_key=row.town_key,
                ))
                if delay:
                    time.sleep(float(delay))
            progress.progress(1.0, text="取得完了")

            results, sign_map = _v179_sort_results_and_signmap(results, sign_map)
            st.session_state["v170_livable_results"] = results
            st.session_state["v170_livable_sign_map"] = sign_map
            st.session_state["v170_livable_rows"] = unique_rows
            st.session_state["v170_livable_metas"] = metas
            st.session_state["v170_livable_errors"] = town_errors

        results: List[MansionSignResultV170] = st.session_state.get("v170_livable_results", []) or []
        sign_map: Dict[int, List[LivableImageV170]] = st.session_state.get("v170_livable_sign_map", {}) or {}
        metas = st.session_state.get("v170_livable_metas", []) or []
        errors = st.session_state.get("v170_livable_errors", []) or []
        if errors:
            for e in errors:
                st.warning(e)
        if results:
            sign_ok = sum(1 for r in results if r.sign_count > 0)
            st.success(f"取得完了：詳細ページ {len(results)}件 / マンション名画像あり {sign_ok}件")
            if metas:
                with st.expander("町名ページ取得ログ", expanded=False):
                    if _pd_v170 is not None:
                        st.dataframe(_pd_v170.DataFrame(metas), use_container_width=True, hide_index=True)
                    else:
                        st.write(metas)
            st.download_button(
                "マンション名看板画像CSVをダウンロード",
                data=_v170_results_to_csv_bytes(results),
                file_name="livable_selected_area_sign_images_v182.csv",
                mime="text/csv",
                use_container_width=True,
                key="v182_csv",
            )
            _v170_render_sign_cards(results, sign_map, int(st.session_state.get("v170_max_show", 60)))
        else:
            summary = st.session_state.get("v178_last_attempt_summary", {}) or {}
            if summary:
                st.warning("取得結果が0件でした。下に原因確認用のログを表示します。")
                with st.expander("v182 取得ログ", expanded=True):
                    st.write("対象町名:", summary.get("town_groups", []))
                    st.write("町名ページエラー:", summary.get("town_page_errors", []))
                    st.write("町名ページ取得ログ:", summary.get("town_page_logs", []))
                    st.write("丁目フィルタ後の詳細ページ件数:", summary.get("detail_rows_after_filter", 0))
            else:
                st.info("対象町名が表示されている場合は、上の取得ボタンでマンション名看板画像を取得します。")



# ==================================================
# v183 OVERRIDE: リバブル町名ページ取得の汎用化 + 詳細ページフォールバック
# 目的:
# - 旭町で成功した「町名ページ→詳細ページ→看板画像」の流れを他地域でも同じ形で通す
# - 町名ページURLが取れても一覧パース/丁目フィルタで0件になる問題を、詳細ページ側の住所確認で救済する
# - 例: 東京都世田谷区 船橋5丁目/経堂 など、柏市以外でも町名ページへ確実に到達しやすくする
# ==================================================

# よく使う市区町村コードを追加。既存辞書へ後入れで反映する。
try:
    _V181_KNOWN_CITY_CODES.update({
        ("東京都", "世田谷区"): "13112",
        ("東京都", "杉並区"): "13115",
        ("東京都", "大田区"): "13111",
        ("東京都", "板橋区"): "13119",
        ("東京都", "練馬区"): "13120",
        ("東京都", "江東区"): "13108",
        ("東京都", "品川区"): "13109",
        ("東京都", "目黒区"): "13110",
    })
except Exception:
    pass

# 実際にユーザーが使った・検査対象にした町名URLは、まず直行できるようにする。
# 町名ページのURLはリバブル側の公開ページ。ここにあるものは市区ページ探索より優先する。
try:
    _V170_LIVABLE_TOWN_URLS.update({
        ("東京都", "世田谷区", "船橋"): "https://www.livable.co.jp/mansion/library/tokyo/t13112056/",
        ("東京都", "世田谷区", "経堂"): "https://www.livable.co.jp/mansion/library/tokyo/t13112023/",
    })
    _V170_LIVABLE_CITY_URLS.update({
        ("東京都", "世田谷区"): "https://www.livable.co.jp/mansion/library/tokyo/a13112/",
    })
except Exception:
    pass


def _v183_detail_canonical_url(url: str, base_url: str = "") -> str:
    """detail/around等に寄っても /mansion/library/<id>/ に戻す。"""
    u = _v170_clean_url(url, base_url or "https://www.livable.co.jp/")
    m = _V170_DETAIL_RE.search(u or "")
    if not m:
        return u
    parsed = _urlparse_v170(u)
    return f"{parsed.scheme or 'https'}://{parsed.netloc or 'www.livable.co.jp'}/mansion/library/{m.group(1)}/"


def _v183_extract_detail_urls_from_town_html(html: str, final_url: str, limit: int = 120) -> List[str]:
    if _BeautifulSoup_v170 is None:
        return []
    soup = _BeautifulSoup_v170(html or "", "html.parser")
    out: List[str] = []
    seen = set()
    for a in soup.find_all("a", href=True):
        href = a.get("href") or ""
        if not _V170_DETAIL_RE.search(href):
            continue
        u = _v183_detail_canonical_url(href, final_url)
        if u in seen:
            continue
        # 部屋詳細など別URLは基本的に _V170_DETAIL_RE に入らないが、念のため library 直下だけを残す
        if not re.search(r"/mansion/library/\d{6,}/$", u):
            continue
        seen.add(u)
        out.append(u)
        if len(out) >= int(limit):
            break
    return out


def _v183_page_text(html: str) -> str:
    if _BeautifulSoup_v170 is None:
        return _v170_normalize_text(re.sub(r"<[^>]+>", " ", html or ""))
    soup = _BeautifulSoup_v170(html or "", "html.parser")
    return _v170_normalize_text(soup.get_text(" ", strip=True))


def _v183_extract_address_for_group_from_text(text: str, g: Dict[str, Any]) -> str:
    """詳細ページ本文から対象市区町村+町名+丁目の住所をできるだけ短く取る。"""
    txt = _v178_normalize_chome_token(_v170_normalize_text(text))
    pref = _v181_compact(g.get("pref", ""))
    city = _v181_compact(g.get("city", ""))
    town = _v181_compact(g.get("town", ""))
    if not (pref and city and town):
        return _v170_extract_address_from_text(txt)

    # 東京都世田谷区船橋5丁目 / 千葉県柏市旭町1丁目 などを最優先で抽出
    pat = re.compile(re.escape(pref) + r"\s*" + re.escape(city) + r"\s*" + re.escape(town) + r"\s*[0-9０-９一二三四五六七八九十]+丁目")
    m = pat.search(txt)
    if m:
        return _v170_normalize_text(m.group(0))

    # 旧関数の抽出も試す
    addr = _v170_extract_address_from_text(txt)
    if addr:
        return addr
    return ""


def _v183_extract_detail_name(html: str, final_url: str) -> str:
    if _BeautifulSoup_v170 is None:
        return ""
    soup = _BeautifulSoup_v170(html or "", "html.parser")
    candidates: List[str] = []
    for sel in ["h1", "h2"]:
        for tag in soup.select(sel):
            tx = _v170_normalize_text(tag.get_text(" ", strip=True))
            if tx:
                candidates.append(tx)
    for attr in [("meta", {"property": "og:title"}), ("meta", {"name": "twitter:title"})]:
        tag = soup.find(attr[0], attr[1])
        if tag and tag.get("content"):
            candidates.append(_v170_normalize_text(tag.get("content")))
    if soup.title and soup.title.get_text(strip=True):
        candidates.append(_v170_normalize_text(soup.title.get_text(" ", strip=True)))

    for tx in candidates:
        name = re.split(r"の購入|の売却|｜|\|", tx)[0].strip()
        name = re.sub(r"^(マンション名|物件名)[:：]?", "", name).strip()
        if name and len(name) >= 2 and not any(x in name for x in ("東急リバブル", "マンションライブラリー", "中古マンション")):
            return name[:80]
    # URLだけでは名前が分からない場合
    return f"リバブル詳細 { _v170_detail_id_from_url(final_url) }".strip()


def _v183_rows_from_detail_pages(town_html: str, town_final_url: str, g: Dict[str, Any], max_fetch: int = 80) -> Tuple[List[MansionRowV170], Dict[str, Any]]:
    """町名ページ一覧パースが失敗した時の本命保険。
    町名ページから詳細URLだけ取り、各詳細ページで住所・物件名を確認して行を作る。
    """
    urls = _v183_extract_detail_urls_from_town_html(town_html, town_final_url, limit=max_fetch)
    rows: List[MansionRowV170] = []
    checked = 0
    errors = 0
    for u in urls:
        checked += 1
        try:
            html, final_url, status = _v170_fetch_html(u, timeout=18)
            text = _v183_page_text(html)
            name = _v183_extract_detail_name(html, final_url)
            addr = _v183_extract_address_for_group_from_text(text, g)
            if not addr or not _v170_addr_matches_group(addr, g):
                continue
            rows.append(MansionRowV170(
                no=len(rows) + 1,
                name=name,
                address=addr,
                chome=_v170_extract_chome(addr),
                detail_url=_v183_detail_canonical_url(final_url),
                detail_id=_v170_detail_id_from_url(final_url),
                source_text="detail_fallback_v183",
                town_key=f"{g.get('pref')} {g.get('city')} {g.get('town')}",
            ))
        except Exception:
            errors += 1
            continue
    meta = {
        "fallback": "detail_pages_v183",
        "detail_url_candidates": len(urls),
        "detail_pages_checked": checked,
        "detail_page_errors": errors,
        "fallback_rows": len(rows),
    }
    return rows, meta


def _v183_town_page_seems_correct(html: str, g: Dict[str, Any]) -> bool:
    txt = _v181_compact(_v183_page_text(html))
    city = _v181_compact(g.get("city", ""))
    town = _v181_compact(g.get("town", ""))
    if not town:
        return False
    # 「世田谷区 船橋のマンション」などが本文にあれば正しい町名ページ扱い
    return bool((not city or city in txt) and town in txt and "マンション" in txt)


def _v170_town_page_url_for_group(g: Dict[str, Any]) -> Optional[str]:  # type: ignore[override]
    """v183: 町名URL解決を厳密化。
    既知URL→市区町村ページの町名リンク探索→URL検証、の順。
    """
    pref = _v181_compact(g.get("pref", ""))
    city = _v181_compact(g.get("city", ""))
    town = _v181_compact(g.get("town", ""))
    key = (pref, city, town)
    if key in _V181_TOWN_URL_CACHE:
        return _V181_TOWN_URL_CACHE[key]
    if key in _V170_LIVABLE_TOWN_URLS:
        _V181_TOWN_URL_CACHE[key] = _V170_LIVABLE_TOWN_URLS[key]
        return _V181_TOWN_URL_CACHE[key]

    city_url = _v181_city_page_url(pref, city)
    if not city_url:
        _V181_TOWN_URL_CACHE[key] = None
        return None

    try:
        html, final_url, status = _v170_fetch_html(city_url)
        soup = _BeautifulSoup_v170(html, "html.parser")
        candidates: List[Tuple[int, str, str]] = []
        for a in soup.find_all("a", href=True):
            href = a.get("href") or ""
            if "mansion/library" not in href or "/t" not in href:
                continue
            tx = _v181_compact(a.get_text(" ", strip=True))
            if not tx:
                continue
            url = _v170_clean_url(href, final_url)
            if tx == town:
                candidates.append((0, tx, url))
            elif tx.startswith(town) or town in tx:
                candidates.append((10 + abs(len(tx) - len(town)), tx, url))
        candidates.sort(key=lambda x: (x[0], len(x[1]), x[1]))
        for _score, _tx, url in candidates[:6]:
            try:
                thtml, tfinal, _ = _v170_fetch_html(url, timeout=18)
                if _v183_town_page_seems_correct(thtml, g):
                    _V181_TOWN_URL_CACHE[key] = tfinal
                    return tfinal
            except Exception:
                continue
        _V181_TOWN_URL_CACHE[key] = candidates[0][2] if candidates else None
        return _V181_TOWN_URL_CACHE[key]
    except Exception:
        _V181_TOWN_URL_CACHE[key] = None
        return None


def render_selected_area_livable_sign_images_v170() -> None:  # type: ignore[override]
    st.divider()
    st.subheader("マンション名看板画像 v183（他地域詳細ページ保険付き）")
    st.caption("旭町で通った流れを、町名ページ一覧で失敗した地域でも詳細ページ住所確認で救済します。")

    with st.expander("選択済み/生成済み町丁目 → マンション名看板画像を自動取得", expanded=True):
        groups = _v170_selected_area_groups()
        groups = sorted(groups, key=_v179_group_sort_key)

        if groups:
            st.success("画像取得対象の町名を検出しました。下の対象でリバブル町名ページへ進みます。")
            for g in groups:
                st.write(f"- {_v179_area_display(g)}")
            _v182_render_url_resolution_table(groups)
        else:
            st.error("画像取得対象の町名を自動検出できませんでした。ここで止めます。空のまま処理には進ませません。")
            st.info("必要なら下の保険欄に 例: 東京都 世田谷区 船橋五丁目 を1行ずつ入れてください。")

        with st.expander("取得対象の診断 / 保険入力", expanded=not bool(groups)):
            default_manual = st.session_state.get("v177_manual_area_text", "")
            st.text_area(
                "保険用：町丁目を1行ずつ直接指定（通常は空でOK）",
                value=default_manual,
                key="v177_manual_area_text",
                height=90,
                placeholder="例:\n東京都 世田谷区 船橋五丁目\n東京都 世田谷区 経堂二丁目\n千葉県 柏市 旭町一丁目",
            )
            st.write("v183解析結果:", st.session_state.get("v182_area_parse_debug", []))
            st.write("v183取得対象:", st.session_state.get("v182_area_groups_debug", []))
            st.write("選択中候補idx:", st.session_state.get("selected_candidate_idxs_v126", []))
            st.write("検索候補件数:", len(st.session_state.get("search_candidates_v126", []) or []))
            st.write("生成時保存名:", st.session_state.get("last_generated_area_names_v173", []))

        if not groups:
            st.warning("対象町名が空なので、ここでは取得ボタンを出しません。")
            return

        c1, c2, c3 = st.columns(3)
        max_details_per_town = int(c1.number_input("町名ごとの詳細取得上限", 1, 120, 50, 1, key="v170_max_details_per_town"))
        max_show = int(c2.number_input("表示上限", 1, 160, 80, 1, key="v170_max_show"))
        delay = float(c3.number_input("詳細ページ間隔 秒", 0.0, 3.0, 0.12, 0.05, key="v170_delay"))
        run = st.button("この対象でマンション名看板画像を取得（v183）", type="primary", use_container_width=True, key="v183_run")

        if run:
            st.session_state["v170_livable_results"] = []
            st.session_state["v170_livable_sign_map"] = {}
            st.session_state["v170_livable_rows"] = []
            st.session_state["v170_livable_metas"] = []
            st.session_state["v170_livable_errors"] = []
            st.session_state["v178_last_attempt_summary"] = {}
            all_rows: List[MansionRowV170] = []
            metas = []
            town_errors = []
            with st.spinner("リバブル町名ページから詳細ページ一覧を取得中..."):
                for g in groups:
                    town_url, reason = _v182_safe_town_page_url(g)
                    town_key = f"{g.get('pref')} {g.get('city')} {g.get('town')}"
                    if not town_url:
                        town_errors.append(f"{town_key}: {reason}")
                        continue
                    try:
                        html, final_url, status = _v170_fetch_html(town_url)
                        rows, meta = _v170_parse_livable_town_page(html, final_url, town_key=town_key)
                        parsed_before_filter = len(rows)
                        rows = [r for r in rows if _v170_addr_matches_group(r.address, g)]
                        rows = _v179_sort_rows_and_renumber(rows)

                        fb_meta = {}
                        # v183: 通常パースで0件なら、詳細URL→詳細ページ住所で救済する。
                        if not rows:
                            fb_rows, fb_meta = _v183_rows_from_detail_pages(
                                html, final_url, g, max_fetch=max(60, int(max_details_per_town) * 4)
                            )
                            rows = _v179_sort_rows_and_renumber(fb_rows)

                        metas.append({
                            **meta,
                            "town_url": final_url,
                            "target": _v179_area_display(g),
                            "parsed_before_filter": parsed_before_filter,
                            "after_chome_filter": len(rows),
                            **fb_meta,
                        })
                        all_rows.extend(rows[:max_details_per_town])
                    except Exception as e:
                        town_errors.append(f"{town_key}: {e}")

            unique_rows = []
            seen = set()
            for r in _v179_sort_rows_and_renumber(all_rows):
                if r.detail_url in seen:
                    continue
                seen.add(r.detail_url)
                unique_rows.append(r)
            unique_rows = _v179_sort_rows_and_renumber(unique_rows)

            st.session_state["v178_last_attempt_summary"] = {
                "town_groups": [_v179_area_display(g) for g in groups],
                "town_page_errors": list(town_errors),
                "town_page_logs": metas,
                "detail_rows_after_filter": len(unique_rows),
            }

            sign_map: Dict[int, List[LivableImageV170]] = {}
            results: List[MansionSignResultV170] = []
            progress = st.progress(0.0, text="詳細ページからマンション名画像を取得中...")
            for idx, row in enumerate(unique_rows, start=1):
                progress.progress((idx - 1) / max(1, len(unique_rows)), text=f"{idx}/{len(unique_rows)} {row.name} を確認中...")
                signs, warning = _v170_read_detail_for_signs(row)
                sign_map[row.no] = signs
                results.append(MansionSignResultV170(
                    no=row.no,
                    name=row.name,
                    address=row.address,
                    chome=row.chome,
                    detail_url=row.detail_url,
                    sign_count=len(signs),
                    sign_urls=" | ".join(img.url for img in signs),
                    status="OK" if signs else "NO_SIGN_IMAGE",
                    warning=warning,
                    town_key=row.town_key,
                ))
                if delay:
                    time.sleep(float(delay))
            progress.progress(1.0, text="取得完了")

            results, sign_map = _v179_sort_results_and_signmap(results, sign_map)
            st.session_state["v170_livable_results"] = results
            st.session_state["v170_livable_sign_map"] = sign_map
            st.session_state["v170_livable_rows"] = unique_rows
            st.session_state["v170_livable_metas"] = metas
            st.session_state["v170_livable_errors"] = town_errors

        results: List[MansionSignResultV170] = st.session_state.get("v170_livable_results", []) or []
        sign_map: Dict[int, List[LivableImageV170]] = st.session_state.get("v170_livable_sign_map", {}) or {}
        metas = st.session_state.get("v170_livable_metas", []) or []
        errors = st.session_state.get("v170_livable_errors", []) or []
        if errors:
            for e in errors:
                st.warning(e)
        if results:
            sign_ok = sum(1 for r in results if r.sign_count > 0)
            st.success(f"取得完了：詳細ページ {len(results)}件 / マンション名画像あり {sign_ok}件")
            if metas:
                with st.expander("町名ページ取得ログ", expanded=False):
                    if _pd_v170 is not None:
                        st.dataframe(_pd_v170.DataFrame(metas), use_container_width=True, hide_index=True)
                    else:
                        st.write(metas)
            st.download_button(
                "マンション名看板画像CSVをダウンロード",
                data=_v170_results_to_csv_bytes(results),
                file_name="livable_selected_area_sign_images_v183.csv",
                mime="text/csv",
                use_container_width=True,
                key="v183_csv",
            )
            _v170_render_sign_cards(results, sign_map, int(st.session_state.get("v170_max_show", 80)))
        else:
            summary = st.session_state.get("v178_last_attempt_summary", {}) or {}
            if summary:
                st.warning("取得結果が0件でした。下に原因確認用のログを表示します。")
                with st.expander("v183 取得ログ", expanded=True):
                    st.write("対象町名:", summary.get("town_groups", []))
                    st.write("町名ページエラー:", summary.get("town_page_errors", []))
                    st.write("町名ページ取得ログ:", summary.get("town_page_logs", []))
                    st.write("丁目フィルタ後の詳細ページ件数:", summary.get("detail_rows_after_filter", 0))
            else:
                st.info("対象町名が表示されている場合は、上の取得ボタンでマンション名看板画像を取得します。")


# ==================================================
# v184 OVERRIDE: 地域直行登録依存をやめる汎用リバブル解決版
# 目的:
# - 世田谷区だけの直行URL登録ではなく、選択した都県/市区町村/町名から
#   1) 市区町村ページを作る/探す
#   2) 市区町村ページ内の町名リンクを探す
#   3) 町名ページ内の詳細URLを拾う
#   4) 詳細ページ側住所で選択丁目と一致確認
#   5) 看板画像取得
#   という旭町成功パターンを汎用化する。
# - 選択候補の文字列が欠けても、配布範囲/プレビュー境界の座標から
#   local_boundary候補を逆引きして pref/city/town/chome を復元する。
# - 0件の場合も黙って終わらず、町名ページ/詳細URL/住所一致/看板数をログ表示する。
# ==================================================

_V184_URL_CACHE: Dict[Tuple[str, ...], Any] = {}
_V184_BOUNDARY_MATCH_CACHE: Dict[str, Optional[Dict[str, str]]] = {}


def _v184_compact(s: str) -> str:
    return _v181_compact(str(s or ""))


def _v184_pref_root_url(pref: str) -> Optional[str]:
    slug = _v181_pref_slug(pref)
    if not slug:
        return None
    return f"https://www.livable.co.jp/mansion/library/{slug}/"


def _v184_city_page_url(pref: str, city: str) -> Optional[str]:
    """都県/市区町村からリバブルの市区町村ページURLを解決する。
    既知辞書・GeoJSONコード・都県ページ探索の順で汎用化。
    """
    pref_c = _v184_compact(pref)
    city_c = _v184_compact(city)
    if not (pref_c and city_c):
        return None
    key = ("city", pref_c, city_c)
    if key in _V184_URL_CACHE:
        return _V184_URL_CACHE[key]

    # 1) 既存ロジック。GeoJSONコードが取れる場合はこれが一番速い。
    try:
        url = _v181_city_page_url(pref_c, city_c)
        if url:
            _V184_URL_CACHE[key] = url
            return url
    except Exception:
        pass

    # 2) 都県トップページから市区町村リンクを直接探す。
    root = _v184_pref_root_url(pref_c)
    if not root:
        _V184_URL_CACHE[key] = None
        return None

    try:
        html, final_url, _ = _v170_fetch_html(root, timeout=20)
        soup = _BeautifulSoup_v170(html, "html.parser")
        candidates: List[Tuple[int, str, str]] = []
        for a in soup.find_all("a", href=True):
            href = a.get("href") or ""
            if "/mansion/library/" not in href or "/a" not in href:
                continue
            tx = _v184_compact(a.get_text(" ", strip=True))
            if not tx:
                continue
            url = _v170_clean_url(href, final_url)
            if tx == city_c:
                candidates.append((0, tx, url))
            elif city_c in tx or tx in city_c:
                candidates.append((10 + abs(len(tx) - len(city_c)), tx, url))
        candidates.sort(key=lambda x: (x[0], len(x[1]), x[1]))
        if candidates:
            _V184_URL_CACHE[key] = candidates[0][2]
            return candidates[0][2]
    except Exception:
        pass

    _V184_URL_CACHE[key] = None
    return None


def _v184_extract_town_links_from_city_html(html: str, final_url: str, town: str) -> List[Tuple[int, str, str]]:
    """市区町村ページHTMLから町名ページ候補を抽出する。"""
    if _BeautifulSoup_v170 is None:
        return []
    town_c = _v184_compact(town)
    soup = _BeautifulSoup_v170(html or "", "html.parser")
    out: List[Tuple[int, str, str]] = []
    seen = set()
    for a in soup.find_all("a", href=True):
        href = a.get("href") or ""
        if "/mansion/library/" not in href or "/t" not in href:
            continue
        tx = _v184_compact(a.get_text(" ", strip=True))
        if not tx:
            continue
        url = _v170_clean_url(href, final_url)
        if url in seen:
            continue
        seen.add(url)
        if tx == town_c:
            out.append((0, tx, url))
        elif tx.startswith(town_c) or town_c in tx:
            out.append((20 + abs(len(tx) - len(town_c)), tx, url))
    out.sort(key=lambda x: (x[0], len(x[1]), x[1]))
    return out


def _v170_town_page_url_for_group(g: Dict[str, Any]) -> Optional[str]:  # type: ignore[override]
    """v184: 直行登録に頼らず、基本は市区町村ページ内の町名リンクから解決する。"""
    pref = _v184_compact(g.get("pref", ""))
    city = _v184_compact(g.get("city", ""))
    town = _v184_compact(g.get("town", ""))
    key = (pref, city, town)
    if key in _V181_TOWN_URL_CACHE:
        return _V181_TOWN_URL_CACHE[key]

    city_url = _v184_city_page_url(pref, city)
    if city_url:
        try:
            html, final_url, _ = _v170_fetch_html(city_url, timeout=25)
            candidates = _v184_extract_town_links_from_city_html(html, final_url, town)
            for _score, _tx, url in candidates[:8]:
                try:
                    thtml, tfinal, _ = _v170_fetch_html(url, timeout=18)
                    if _v183_town_page_seems_correct(thtml, g):
                        _V181_TOWN_URL_CACHE[key] = tfinal
                        return tfinal
                except Exception:
                    continue
            if candidates:
                # 検証に失敗しても、候補があるなら後段の住所一致フィルタで救済する。
                _V181_TOWN_URL_CACHE[key] = candidates[0][2]
                return candidates[0][2]
        except Exception:
            pass

    # 最後の保険として既知直行URLを使う。これは補助であって主経路ではない。
    if key in _V170_LIVABLE_TOWN_URLS:
        _V181_TOWN_URL_CACHE[key] = _V170_LIVABLE_TOWN_URLS[key]
        return _V181_TOWN_URL_CACHE[key]

    _V181_TOWN_URL_CACHE[key] = None
    return None


def _v184_boundary_info_from_coords(coords: Sequence[Tuple[float, float]], source: str = "geometry") -> Optional[Dict[str, str]]:
    """配布範囲/プレビュー境界の座標から、local_boundary候補を逆引きする。"""
    if not coords:
        return None
    try:
        key = source + ":" + str(round(sum(float(x[0]) for x in coords) / len(coords), 6)) + "," + str(round(sum(float(x[1]) for x in coords) / len(coords), 6))
        if key in _V184_BOUNDARY_MATCH_CACHE:
            return _V184_BOUNDARY_MATCH_CACHE[key]
    except Exception:
        key = ""

    try:
        if Point is None or Polygon is None:
            return None
        # coords は (lat, lon)。shapely は (lon, lat)。
        pts = [(float(lon), float(lat)) for lat, lon in coords if lat is not None and lon is not None]
        if len(pts) < 3:
            return None
        try:
            poly = Polygon(pts)
            c = poly.centroid
        except Exception:
            lat = sum(float(p[0]) for p in coords) / len(coords)
            lon = sum(float(p[1]) for p in coords) / len(coords)
            c = Point(float(lon), float(lat))

        best: Optional[Tuple[float, Dict[str, Any]]] = None
        for rec in load_local_boundary_candidates_v126() or []:
            lines = rec.get("latlon_lines") or []
            if not lines:
                continue
            line = lines[0]
            if len(line) < 3:
                continue
            try:
                rp = Polygon([(float(lon), float(lat)) for lat, lon in line])
                if not rp.is_valid:
                    rp = rp.buffer(0)
                dist = rp.distance(c)
                contains = rp.contains(c) or rp.touches(c)
                # 含むものを最優先。無ければ近いもの。
                score = 0.0 if contains else float(dist)
                if best is None or score < best[0]:
                    best = (score, rec)
                    if contains:
                        break
            except Exception:
                continue

        if best is None:
            return None
        rec = best[1]
        pref = _v184_compact(rec.get("pref", ""))
        city = _v184_compact(rec.get("city", ""))
        short = _v184_compact(rec.get("short_name", ""))
        if not (pref and city and short):
            return None
        town, chome = _v181_split_town_chome(short)
        info = {"pref": pref, "city": city, "town": town, "chome": chome, "raw": f"{short} / {city} / {pref}"}
        if key:
            _V184_BOUNDARY_MATCH_CACHE[key] = info
        return info
    except Exception:
        return None


def _v184_add_groups_from_geometry(groups: Dict[Tuple[str, str, str], Dict[str, Any]], debug: List[Dict[str, str]]) -> None:
    """登録済み配布範囲・プレビュー境界から、座標逆引きで町名を補完する。"""
    # 登録済み配布範囲
    for i, item in enumerate(st.session_state.get("route_boundaries_v118", []) or []):
        coords = item.get("coords") if isinstance(item, dict) else item
        info = _v184_boundary_info_from_coords(coords or [], source=f"route_boundaries_v118:{i}")
        _v182_group_add(groups, info, f"geometry_route_boundaries_v184:{i}", debug)

    # 現在プレビュー中境界
    for i, coords in enumerate(st.session_state.get("boundary_lines", []) or []):
        info = _v184_boundary_info_from_coords(coords or [], source=f"boundary_lines:{i}")
        _v182_group_add(groups, info, f"geometry_boundary_lines_v184:{i}", debug)


def _v170_selected_area_groups() -> List[Dict[str, Any]]:  # type: ignore[override]
    """v184: 候補データ本体 + 座標逆引き + 文字列復元を全部使って、選択地域を落とさない。"""
    groups: Dict[Tuple[str, str, str], Dict[str, Any]] = {}
    debug: List[Dict[str, str]] = []

    candidates = st.session_state.get("search_candidates_v126", []) or []
    selected_records = _v182_selected_candidate_records()

    # 1) 最優先: 現在選択中の候補データ本体
    for p in selected_records:
        _v182_group_add(groups, _v182_candidate_to_area_info(p), "selected_candidate_record_v184", debug)

    # 2) 配布範囲/プレビュー境界の座標から逆引き。検索候補が消えていても復元する。
    _v184_add_groups_from_geometry(groups, debug)

    # 3) 旧文字列も候補一覧から復元
    raw_names: List[str] = []
    try:
        raw_names.extend(_v177_collect_raw_area_names_for_image())
    except Exception:
        try:
            raw_names.extend(_v173_collect_area_names_for_image())
        except Exception:
            pass
    for nm in (st.session_state.get("last_generated_area_names_v173", []) or []):
        if str(nm or "").strip():
            raw_names.append(str(nm).strip())

    seen_raw = set()
    for raw in raw_names:
        raw_s = str(raw or "").strip()
        if not raw_s or raw_s in seen_raw:
            continue
        seen_raw.add(raw_s)

        matched = _v182_match_candidate_for_raw(raw_s, selected_records)
        if not matched:
            matched = _v182_match_candidate_for_raw(raw_s, candidates)
        if matched:
            for p in matched:
                _v182_group_add(groups, _v182_candidate_to_area_info(p), f"raw_matched_candidate_v184:{raw_s}", debug)
            continue

        info = _v170_parse_area_name(raw_s)
        _v182_group_add(groups, info, f"raw_parser_v184:{raw_s}", debug)

    # 4) 手入力保険欄
    manual = st.session_state.get("v177_manual_area_text", "")
    try:
        for line in _v177_split_manual_area_text(manual):
            _v182_group_add(groups, _v170_parse_area_name(line), "manual_text_v184", debug)
    except Exception:
        pass

    out = list(groups.values())
    for g in out:
        g["areas"] = list(dict.fromkeys(g.get("areas", [])))
        g["sources"] = sorted(list(g.get("sources", [])))
    out = sorted(out, key=_v179_group_sort_key)

    try:
        st.session_state["v184_area_parse_debug"] = debug
        st.session_state["v184_area_groups_debug"] = [
            {
                "pref": g.get("pref"),
                "city": g.get("city"),
                "town": g.get("town"),
                "chomes": "・".join(sorted(g.get("chomes") or [], key=_v179_chome_num)) or "全域",
                "areas": " / ".join(g.get("areas") or []),
                "sources": " / ".join(g.get("sources") or []),
            }
            for g in out
        ]
    except Exception:
        pass
    return out


def _v184_collect_related_page_urls(html: str, final_url: str, limit_pages: int = 6) -> List[str]:
    """町名ページのページネーション/同一町名ページURLを拾う。"""
    urls = [_v170_clean_url(final_url, final_url)]
    if _BeautifulSoup_v170 is None:
        return urls
    try:
        base_path = _urlparse_v170(final_url).path.rstrip("/")
        soup = _BeautifulSoup_v170(html or "", "html.parser")
        for a in soup.find_all("a", href=True):
            u = _v170_clean_url(a.get("href") or "", final_url)
            p = _urlparse_v170(u)
            if p.path.rstrip("/") != base_path:
                continue
            if u not in urls:
                urls.append(u)
                if len(urls) >= int(limit_pages):
                    break
    except Exception:
        pass
    return urls


def _v184_detail_rows_from_urls(detail_urls: Sequence[str], g: Dict[str, Any], max_fetch: int = 120) -> Tuple[List[MansionRowV170], Dict[str, Any]]:
    rows: List[MansionRowV170] = []
    checked = 0
    errors = 0
    address_mismatch = 0
    for u in list(dict.fromkeys(detail_urls))[:int(max_fetch)]:
        checked += 1
        try:
            html, final_url, status = _v170_fetch_html(u, timeout=18)
            text = _v183_page_text(html)
            name = _v183_extract_detail_name(html, final_url)
            addr = _v183_extract_address_for_group_from_text(text, g)
            if not addr or not _v170_addr_matches_group(addr, g):
                address_mismatch += 1
                continue
            rows.append(MansionRowV170(
                no=len(rows) + 1,
                name=name,
                address=addr,
                chome=_v170_extract_chome(addr),
                detail_url=_v183_detail_canonical_url(final_url),
                detail_id=_v170_detail_id_from_url(final_url),
                source_text="detail_address_verified_v184",
                town_key=f"{g.get('pref')} {g.get('city')} {g.get('town')}",
            ))
        except Exception:
            errors += 1
            continue
    return rows, {
        "detail_candidates": len(list(dict.fromkeys(detail_urls))),
        "detail_pages_checked": checked,
        "detail_page_errors": errors,
        "detail_address_mismatch": address_mismatch,
        "detail_rows_by_address": len(rows),
    }


def _v184_rows_for_group(g: Dict[str, Any], max_details_per_town: int = 60, max_pages: int = 6) -> Tuple[List[MansionRowV170], Dict[str, Any], List[str]]:
    """1町名グループについて、町名ページ→詳細URL→住所一致まで実行する。"""
    warnings: List[str] = []
    target = _v179_area_display(g)
    town_url = _v170_town_page_url_for_group(g)
    city_url = _v184_city_page_url(g.get("pref", ""), g.get("city", ""))

    meta: Dict[str, Any] = {
        "target": target,
        "city_url": city_url or "",
        "town_url": town_url or "",
        "town_pages_checked": 0,
        "town_parse_rows_before_filter": 0,
        "town_parse_rows_after_filter": 0,
        "detail_candidates": 0,
        "detail_pages_checked": 0,
        "detail_rows_by_address": 0,
    }

    if not town_url:
        warnings.append(f"{target}: リバブル町名ページURLを解決できませんでした")
        return [], meta, warnings

    all_rows: List[MansionRowV170] = []
    detail_urls: List[str] = []
    try:
        first_html, first_final, _ = _v170_fetch_html(town_url, timeout=25)
        page_urls = _v184_collect_related_page_urls(first_html, first_final, limit_pages=max_pages)
        seen_page = set()
        for page_i, page_url in enumerate(page_urls):
            if page_url in seen_page:
                continue
            seen_page.add(page_url)
            if page_i == 0:
                html, final_url = first_html, first_final
            else:
                html, final_url, _ = _v170_fetch_html(page_url, timeout=25)
            meta["town_pages_checked"] = int(meta.get("town_pages_checked", 0)) + 1

            rows, pmeta = _v170_parse_livable_town_page(html, final_url, town_key=f"{g.get('pref')} {g.get('city')} {g.get('town')}")
            meta["town_expected_count"] = pmeta.get("expected_count")
            meta["town_parse_rows_before_filter"] = int(meta.get("town_parse_rows_before_filter", 0)) + len(rows)
            filtered = [r for r in rows if _v170_addr_matches_group(r.address, g)]
            meta["town_parse_rows_after_filter"] = int(meta.get("town_parse_rows_after_filter", 0)) + len(filtered)
            all_rows.extend(filtered)

            detail_urls.extend(_v183_extract_detail_urls_from_town_html(html, final_url, limit=max(120, int(max_details_per_town) * 4)))
    except Exception as e:
        warnings.append(f"{target}: 町名ページ取得/解析エラー: {e}")

    # 町名ページのテキスト解析で取れた行だけに頼らず、詳細ページ住所でも必ず再確認する。
    fb_rows, fb_meta = _v184_detail_rows_from_urls(
        detail_urls,
        g,
        max_fetch=max(120, int(max_details_per_town) * 4),
    )
    meta.update(fb_meta)
    all_rows.extend(fb_rows)

    # 重複排除・並び替え
    unique: List[MansionRowV170] = []
    seen = set()
    for r in _v179_sort_rows_and_renumber(all_rows):
        key = r.detail_url or (r.name, r.address)
        if key in seen:
            continue
        seen.add(key)
        r.no = len(unique) + 1
        unique.append(r)
        if len(unique) >= int(max_details_per_town):
            break

    meta["final_rows"] = len(unique)
    if not unique:
        warnings.append(
            f"{target}: 町名ページは取得しましたが、選択丁目に一致する詳細ページが0件でした"
        )
    return unique, meta, warnings


def _v184_render_url_resolution_table(groups: List[Dict[str, Any]]) -> None:
    rows = []
    for g in groups:
        city_url = _v184_city_page_url(g.get("pref", ""), g.get("city", ""))
        town_url = _v170_town_page_url_for_group(g)
        rows.append({
            "対象": _v179_area_display(g),
            "市区町村ページ": "OK" if city_url else "NG",
            "町名ページ": "OK" if town_url else "NG",
            "town_url": town_url or "",
        })
    with st.expander("v184 URL解決チェック", expanded=True):
        if _pd_v170 is not None:
            st.dataframe(_pd_v170.DataFrame(rows), use_container_width=True, hide_index=True)
        else:
            st.write(rows)


def render_selected_area_livable_sign_images_v170() -> None:  # type: ignore[override]
    st.divider()
    st.subheader("マンション名看板画像 v184（汎用リバブル解決・詳細住所確認版）")
    st.caption("旭町で成功した流れを、地域直行登録ではなく、市区町村ページ→町名リンク→詳細ページ住所確認で汎用化しました。")

    with st.expander("選択済み/生成済み町丁目 → マンション名看板画像を自動取得", expanded=True):
        groups = _v170_selected_area_groups()
        groups = sorted(groups, key=_v179_group_sort_key)

        if groups:
            st.success("画像取得対象の町名を検出しました。下の対象ごとに市区町村ページ→町名ページ→詳細ページへ進みます。")
            for g in groups:
                st.write(f"- {_v179_area_display(g)}")
            _v184_render_url_resolution_table(groups)
        else:
            st.error("画像取得対象の町名を自動検出できませんでした。空のまま処理には進ませません。")
            st.info("必要なら下の保険欄に 例: 東京都 世田谷区 船橋五丁目 を1行ずつ入れてください。")

        with st.expander("取得対象の診断 / 保険入力", expanded=not bool(groups)):
            default_manual = st.session_state.get("v177_manual_area_text", "")
            st.text_area(
                "保険用：町丁目を1行ずつ直接指定（通常は空でOK）",
                value=default_manual,
                key="v177_manual_area_text",
                height=90,
                placeholder="例:\n東京都 世田谷区 船橋五丁目\n東京都 世田谷区 経堂二丁目\n千葉県 柏市 旭町一丁目",
            )
            st.write("v184解析結果:", st.session_state.get("v184_area_parse_debug", []))
            st.write("v184取得対象:", st.session_state.get("v184_area_groups_debug", []))
            st.write("選択中候補idx:", st.session_state.get("selected_candidate_idxs_v126", []))
            st.write("検索候補件数:", len(st.session_state.get("search_candidates_v126", []) or []))
            st.write("生成時保存名:", st.session_state.get("last_generated_area_names_v173", []))

        if not groups:
            st.warning("対象町名が空なので、ここでは取得ボタンを出しません。")
            return

        c1, c2, c3, c4 = st.columns(4)
        max_details_per_town = int(c1.number_input("町名ごとの詳細取得上限", 1, 160, 80, 1, key="v170_max_details_per_town"))
        max_show = int(c2.number_input("表示上限", 1, 200, 120, 1, key="v170_max_show"))
        delay = float(c3.number_input("詳細ページ間隔 秒", 0.0, 3.0, 0.10, 0.05, key="v170_delay"))
        max_pages = int(c4.number_input("町名ページ確認上限", 1, 10, 6, 1, key="v184_max_pages"))

        run = st.button("この対象でマンション名看板画像を取得（v184）", type="primary", use_container_width=True, key="v184_run")

        if run:
            st.session_state["v170_livable_results"] = []
            st.session_state["v170_livable_sign_map"] = {}
            st.session_state["v170_livable_rows"] = []
            st.session_state["v170_livable_metas"] = []
            st.session_state["v170_livable_errors"] = []
            st.session_state["v178_last_attempt_summary"] = {}

            all_rows: List[MansionRowV170] = []
            metas: List[Dict[str, Any]] = []
            town_errors: List[str] = []

            with st.spinner("リバブル町名ページ・詳細ページ住所を確認中..."):
                for g in groups:
                    rows, meta, warnings = _v184_rows_for_group(g, max_details_per_town=max_details_per_town, max_pages=max_pages)
                    metas.append(meta)
                    town_errors.extend(warnings)
                    all_rows.extend(rows)

            unique_rows: List[MansionRowV170] = []
            seen = set()
            for r in _v179_sort_rows_and_renumber(all_rows):
                key = r.detail_url or (r.name, r.address)
                if key in seen:
                    continue
                seen.add(key)
                r.no = len(unique_rows) + 1
                unique_rows.append(r)

            st.session_state["v178_last_attempt_summary"] = {
                "town_groups": [ _v179_area_display(g) for g in groups ],
                "town_page_errors": list(town_errors),
                "town_page_logs": metas,
                "detail_rows_after_filter": len(unique_rows),
            }

            sign_map: Dict[int, List[LivableImageV170]] = {}
            results: List[MansionSignResultV170] = []
            progress = st.progress(0.0, text="詳細ページからマンション名画像を取得中...")
            for idx, row in enumerate(unique_rows, start=1):
                progress.progress((idx - 1) / max(1, len(unique_rows)), text=f"{idx}/{len(unique_rows)} {row.name} を確認中...")
                signs, warning = _v170_read_detail_for_signs(row)
                sign_map[row.no] = signs
                results.append(MansionSignResultV170(
                    no=row.no,
                    name=row.name,
                    address=row.address,
                    chome=row.chome,
                    detail_url=row.detail_url,
                    sign_count=len(signs),
                    sign_urls=" | ".join(img.url for img in signs),
                    status="OK" if signs else "NO_SIGN_IMAGE",
                    warning=warning,
                    town_key=row.town_key,
                ))
                if delay:
                    time.sleep(float(delay))
            progress.progress(1.0, text="取得完了")

            results, sign_map = _v179_sort_results_and_signmap(results, sign_map)

            st.session_state["v170_livable_results"] = results
            st.session_state["v170_livable_sign_map"] = sign_map
            st.session_state["v170_livable_rows"] = unique_rows
            st.session_state["v170_livable_metas"] = metas
            st.session_state["v170_livable_errors"] = town_errors

        results: List[MansionSignResultV170] = st.session_state.get("v170_livable_results", []) or []
        sign_map: Dict[int, List[LivableImageV170]] = st.session_state.get("v170_livable_sign_map", {}) or {}
        metas = st.session_state.get("v170_livable_metas", []) or []
        errors = st.session_state.get("v170_livable_errors", []) or []

        if errors:
            with st.expander("v184 注意/原因ログ", expanded=True):
                for e in errors:
                    st.warning(e)

        if metas:
            with st.expander("v184 詳細取得ログ", expanded=True):
                if _pd_v170 is not None:
                    st.dataframe(_pd_v170.DataFrame(metas), use_container_width=True, hide_index=True)
                else:
                    st.write(metas)

        if results:
            sign_ok = sum(1 for r in results if r.sign_count > 0)
            st.success(f"取得完了：詳細ページ {len(results)}件 / マンション名画像あり {sign_ok}件")
            st.download_button(
                "マンション名看板画像CSVをダウンロード",
                data=_v170_results_to_csv_bytes(results),
                file_name="livable_selected_area_sign_images_v184.csv",
                mime="text/csv",
                use_container_width=True,
                key="v184_csv",
            )
            _v170_render_sign_cards(results, sign_map, int(st.session_state.get("v170_max_show", 120)))
        else:
            summary = st.session_state.get("v178_last_attempt_summary", {}) or {}
            if summary:
                st.warning("取得結果が0件でした。下に、どこで0件になったかを表示します。")
                with st.expander("v184 取得ログ", expanded=True):
                    st.write("対象町名:", summary.get("town_groups", []))
                    st.write("注意/エラー:", summary.get("town_page_errors", []))
                    st.write("取得ログ:", summary.get("town_page_logs", []))
                    st.write("住所一致後の詳細ページ件数:", summary.get("detail_rows_after_filter", 0))
            else:
                st.info("対象町名が表示されている場合は、上の取得ボタンでマンション名看板画像を取得します。")



# ==================================================
# v185 OVERRIDE: 3:4整形 + チラシランダム合成
# 目的:
# - v184で取得できたマンション名看板画像を、横3:縦4の最終画像へ整える
# - ユーザーがアップロードしたチラシ画像をランダム選択・ランダム配置で自然合成する
# - v184のリバブル取得ロジック・軌跡生成ロジックは壊さない
# 注意:
# - ローカルPillow処理では本物の生成AIアウトペイントはできないため、ここでは
#   「自然トリミング」または「簡易背景拡張」を実装する。
# - 本格的なAI外周補完は、別途画像生成/補完API接続が必要。
# ==================================================

try:
    import io as _io_v185
    import zipfile as _zipfile_v185
    import hashlib as _hashlib_v185
    from PIL import Image as _Image_v185, ImageOps as _ImageOps_v185, ImageFilter as _ImageFilter_v185, ImageEnhance as _ImageEnhance_v185, ImageChops as _ImageChops_v185
except Exception:
    _io_v185 = None
    _zipfile_v185 = None
    _hashlib_v185 = None
    _Image_v185 = None
    _ImageOps_v185 = None
    _ImageFilter_v185 = None
    _ImageEnhance_v185 = None
    _ImageChops_v185 = None

_V185_PREV_RENDER_SELECTED_AREA = render_selected_area_livable_sign_images_v170


def _v185_safe_filename(s: str, max_len: int = 70) -> str:
    s = str(s or "image")
    s = re.sub(r"[\\/:*?\"<>|\s　]+", "_", s).strip("_")
    s = re.sub(r"_+", "_", s)
    return (s[:max_len] or "image")


def _v185_open_uploaded_image(uploaded) -> Optional[Any]:
    if _Image_v185 is None or uploaded is None:
        return None
    try:
        uploaded.seek(0)
    except Exception:
        pass
    try:
        img = _Image_v185.open(uploaded).convert("RGBA")
        return img
    except Exception:
        return None


def _v185_fetch_image(url: str, timeout: int = 25) -> Optional[Any]:
    if _Image_v185 is None or requests is None or not url:
        return None
    try:
        resp = requests.get(url, headers=_V170_HEADERS, timeout=timeout)
        resp.raise_for_status()
        img = _Image_v185.open(_io_v185.BytesIO(resp.content)).convert("RGBA")
        return img
    except Exception:
        return None


def _v185_image_to_png_bytes(img) -> bytes:
    bio = _io_v185.BytesIO()
    img.convert("RGB").save(bio, format="PNG", optimize=True)
    return bio.getvalue()


def _v185_crop_or_expand_to_3x4(img, out_w: int = 900, mode: str = "簡易背景拡張"):
    """最終3:4キャンバスを作る。
    - 自然トリミング: cover crop。白フチなし、ただし端が切れる可能性あり。
    - 簡易背景拡張: 背景を拡大ぼかしで敷き、元画像をfit配置。AI補完ではないが情報保持寄り。
    """
    if _Image_v185 is None:
        return img
    img = img.convert("RGBA")
    out_w = int(out_w or 900)
    out_h = int(round(out_w * 4 / 3))
    if out_w < 360:
        out_w, out_h = 360, 480

    if mode == "自然トリミング":
        # 3:4でcover crop。縁は作らない。
        return _ImageOps_v185.fit(img, (out_w, out_h), method=_Image_v185.Resampling.LANCZOS, centering=(0.5, 0.5)).convert("RGBA")

    # 簡易背景拡張: 重要情報保持優先。背景は元画像をcoverしてぼかす。
    bg = _ImageOps_v185.fit(img, (out_w, out_h), method=_Image_v185.Resampling.LANCZOS, centering=(0.5, 0.5)).convert("RGBA")
    try:
        bg = bg.filter(_ImageFilter_v185.GaussianBlur(radius=max(10, out_w // 45)))
        bg = _ImageEnhance_v185.Contrast(bg).enhance(0.92)
        bg = _ImageEnhance_v185.Brightness(bg).enhance(0.96)
    except Exception:
        pass

    # 元画像をできるだけ大きくfit配置。余白ではなく背景拡張に見えるようにする。
    iw, ih = img.size
    scale = min(out_w / max(1, iw), out_h / max(1, ih))
    # 小さすぎる場合は少し拡大。ただしキャンバス内に収める。
    scale = min(scale * 0.98, out_w / max(1, iw), out_h / max(1, ih))
    nw, nh = max(1, int(iw * scale)), max(1, int(ih * scale))
    fg = img.resize((nw, nh), _Image_v185.Resampling.LANCZOS)
    x = (out_w - nw) // 2
    y = (out_h - nh) // 2
    canvas = bg
    canvas.alpha_composite(fg, (x, y))
    return canvas.convert("RGBA")


def _v185_trim_transparent_or_white(img):
    """チラシ素材の余白を軽く切る。透明があれば透明bbox、無ければ白背景との差分bbox。"""
    if _Image_v185 is None:
        return img
    img = img.convert("RGBA")
    try:
        alpha = img.getchannel("A")
        bbox = alpha.getbbox()
        if bbox and bbox != (0, 0, img.width, img.height):
            return img.crop(bbox)
    except Exception:
        pass
    try:
        rgb = img.convert("RGB")
        bg = _Image_v185.new("RGB", rgb.size, rgb.getpixel((0, 0)))
        diff = _ImageChops_v185.difference(rgb, bg)
        diff = _ImageChops_v185.add(diff, diff, 2.0, -20)
        bbox = diff.getbbox()
        if bbox:
            # 余白を少し残す
            pad = 6
            l, t, r, b = bbox
            l, t = max(0, l-pad), max(0, t-pad)
            r, b = min(img.width, r+pad), min(img.height, b+pad)
            return img.crop((l, t, r, b))
    except Exception:
        pass
    return img


def _v185_prepare_flyer(flyer, canvas_w: int, rng: random.Random, size_ratio: float = 0.42):
    flyer = _v185_trim_transparent_or_white(flyer).convert("RGBA")
    fw, fh = flyer.size
    target_w = int(canvas_w * max(0.22, min(0.65, size_ratio)))
    if fw > 0:
        target_h = int(fh * (target_w / fw))
    else:
        target_h = target_w
    flyer = flyer.resize((max(1, target_w), max(1, target_h)), _Image_v185.Resampling.LANCZOS)

    # 少しだけ明るさ/コントラスト揺らぎ
    try:
        flyer = _ImageEnhance_v185.Brightness(flyer).enhance(rng.uniform(0.94, 1.06))
        flyer = _ImageEnhance_v185.Contrast(flyer).enhance(rng.uniform(0.96, 1.05))
    except Exception:
        pass

    angle = rng.uniform(-13.0, 13.0)
    flyer = flyer.rotate(angle, resample=_Image_v185.Resampling.BICUBIC, expand=True)
    return flyer, angle


def _v185_composite_flyer(base_img, flyer_img, rng: random.Random, position_mode: str = "ランダム下側"):
    base = base_img.convert("RGBA")
    w, h = base.size
    ratio = rng.uniform(0.34, 0.52)
    flyer, angle = _v185_prepare_flyer(flyer_img, w, rng, size_ratio=ratio)
    fw, fh = flyer.size

    # 配置候補: 下側だけ。上掲げは禁止。
    variants = ["left", "center", "right", "left_slant", "right_slant"]
    variant = rng.choice(variants) if position_mode == "ランダム下側" else "center"
    if variant in {"left", "left_slant"}:
        x = int(w * rng.uniform(0.03, 0.18))
    elif variant in {"right", "right_slant"}:
        x = int(w - fw - w * rng.uniform(0.03, 0.18))
    else:
        x = int((w - fw) / 2 + rng.uniform(-0.08, 0.08) * w)
    # 下から差し込み。少し画面外に出しても自然。
    y = int(h - fh - rng.uniform(0.00, 0.08) * h)
    y = min(max(int(h * 0.58), y), h - int(fh * 0.62))
    x = max(-int(fw * 0.08), min(w - int(fw * 0.55), x))

    # 影
    shadow = _Image_v185.new("RGBA", flyer.size, (0, 0, 0, 0))
    try:
        alpha = flyer.getchannel("A")
        shadow.putalpha(alpha.point(lambda p: int(p * 0.26)))
        shadow = shadow.filter(_ImageFilter_v185.GaussianBlur(radius=max(4, w // 160)))
        base.alpha_composite(shadow, (x + int(w * 0.012), y + int(w * 0.012)))
    except Exception:
        pass
    base.alpha_composite(flyer, (x, y))
    return base.convert("RGBA"), {"x": x, "y": y, "angle": round(angle, 2), "variant": variant, "flyer_w": fw, "flyer_h": fh}


def _v185_current_sign_items(max_items: int = 999) -> List[Dict[str, Any]]:
    results: List[MansionSignResultV170] = st.session_state.get("v170_livable_results", []) or []
    sign_map: Dict[int, List[LivableImageV170]] = st.session_state.get("v170_livable_sign_map", {}) or {}
    items: List[Dict[str, Any]] = []
    for r in results:
        signs = sign_map.get(r.no, []) or []
        if not signs:
            continue
        # 基本は1物件1枚。複数看板がある場合は先頭を使う。
        img = signs[0]
        items.append({
            "no": r.no,
            "name": r.name,
            "address": r.address,
            "chome": r.chome,
            "detail_url": r.detail_url,
            "image_url": img.url,
            "context": img.context,
        })
        if len(items) >= int(max_items):
            break
    return items


def _v185_build_zip(outputs: List[Dict[str, Any]]) -> bytes:
    bio = _io_v185.BytesIO()
    with _zipfile_v185.ZipFile(bio, "w", compression=_zipfile_v185.ZIP_DEFLATED) as zf:
        for item in outputs:
            zf.writestr(item["filename"], item["png"])
        # CSVも入れる
        rows = ["no,name,address,image_url,flyer_index,placement,filename"]
        for item in outputs:
            rows.append(
                f'{item.get("no","")},"{str(item.get("name","")).replace(chr(34), chr(34)*2)}","{str(item.get("address","")).replace(chr(34), chr(34)*2)}","{item.get("image_url","")}",{item.get("flyer_index","")},"{item.get("placement","")}","{item.get("filename","")}"'
            )
        zf.writestr("manifest.csv", "\n".join(rows).encode("utf-8-sig"))
    return bio.getvalue()


def render_v185_3x4_flyer_composite() -> None:
    st.divider()
    st.subheader("3:4整形・チラシランダム合成 v185")
    st.caption("v184で取得したマンション名看板画像を、3:4縦長に整え、アップロードしたチラシ画像を下側から自然に合成します。")

    if _Image_v185 is None or _io_v185 is None or _zipfile_v185 is None:
        st.error("Pillow が必要です。PowerShellで `pip install pillow` を実行してください。")
        return

    items = _v185_current_sign_items()
    if not items:
        st.info("まず上の v184 でマンション名看板画像を取得してください。画像ありの結果があると、ここで3:4化・チラシ合成できます。")
        return

    st.success(f"合成対象：マンション名看板画像 {len(items)}件")

    with st.expander("チラシ画像アップロード / 合成設定", expanded=True):
        flyers_uploaded = st.file_uploader(
            "チラシだけの画像をアップロード（最大10枚程度）",
            type=["png", "jpg", "jpeg", "webp"],
            accept_multiple_files=True,
            key="v185_flyer_uploads",
        )
        c1, c2, c3, c4 = st.columns(4)
        out_w = int(c1.number_input("出力横幅", 360, 1800, 900, 60, key="v185_out_w"))
        max_items = int(c2.number_input("生成上限", 1, 200, min(60, len(items)), 1, key="v185_max_items"))
        seed_mode = c3.selectbox("ランダム", ["毎回変える", "固定seed"], index=0, key="v185_seed_mode")
        seed_val = int(c4.number_input("seed", 0, 999999, 185, 1, key="v185_seed_val"))
        fit_mode = st.radio(
            "3:4化方式",
            ["簡易背景拡張", "自然トリミング"],
            index=0,
            horizontal=True,
            key="v185_fit_mode",
            help="本物のAIアウトペイントではありません。重要情報保持なら簡易背景拡張、縁なし重視なら自然トリミングです。",
        )
        make_base_only = st.checkbox("チラシなし3:4画像も同時に作る", value=False, key="v185_make_base_only")

        st.caption("※ v185はローカルPillow処理です。本格的なAIアウトペイントは、別途画像生成/補完API接続が必要です。")

    flyers: List[Any] = []
    for f in (flyers_uploaded or [])[:10]:
        img = _v185_open_uploaded_image(f)
        if img is not None:
            flyers.append(img)

    run = st.button("3:4整形・チラシ合成を生成（v185）", type="primary", use_container_width=True, key="v185_run")

    if run:
        if not flyers and not make_base_only:
            st.warning("チラシ画像をアップロードしてください。チラシなしで3:4だけ作る場合は『チラシなし3:4画像も同時に作る』にチェックしてください。")
            return
        rng = random.Random(seed_val if seed_mode == "固定seed" else int(time.time() * 1000) % 100000000)
        outputs: List[Dict[str, Any]] = []
        progress = st.progress(0.0, text="3:4整形・合成中...")
        target_items = items[:max_items]
        for idx, item in enumerate(target_items, start=1):
            progress.progress((idx - 1) / max(1, len(target_items)), text=f"{idx}/{len(target_items)} {item['name']} を処理中...")
            base_src = _v185_fetch_image(item["image_url"])
            if base_src is None:
                continue
            base_34 = _v185_crop_or_expand_to_3x4(base_src, out_w=out_w, mode=fit_mode)

            if make_base_only:
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_3x4.png"
                outputs.append({
                    **item,
                    "filename": filename,
                    "png": _v185_image_to_png_bytes(base_34),
                    "flyer_index": "none",
                    "placement": "3x4_only",
                })

            if flyers:
                flyer_i = rng.randrange(len(flyers))
                comp, place = _v185_composite_flyer(base_34, flyers[flyer_i], rng, position_mode="ランダム下側")
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_flyer.png"
                outputs.append({
                    **item,
                    "filename": filename,
                    "png": _v185_image_to_png_bytes(comp),
                    "flyer_index": flyer_i + 1,
                    "placement": str(place),
                })
        progress.progress(1.0, text="生成完了")
        st.session_state["v185_outputs"] = outputs

    outputs = st.session_state.get("v185_outputs", []) or []
    if outputs:
        st.success(f"生成完了：{len(outputs)}枚")
        zip_bytes = _v185_build_zip(outputs)
        st.download_button(
            "3:4・チラシ合成画像ZIPをダウンロード",
            data=zip_bytes,
            file_name="v185_3x4_flyer_composite_images.zip",
            mime="application/zip",
            use_container_width=True,
            key="v185_zip_download",
        )
        with st.expander("生成画像プレビュー", expanded=True):
            preview = outputs[:12]
            cols = st.columns(3)
            for i, item in enumerate(preview):
                with cols[i % 3]:
                    st.image(item["png"], caption=f"{item.get('name','')}\n{item.get('address','')}", use_container_width=True)
                    st.caption(item.get("filename", ""))
        if len(outputs) > 12:
            st.caption(f"プレビューは先頭12枚のみ表示しています。全{len(outputs)}枚はZIPに入っています。")


def render_selected_area_livable_sign_images_v170() -> None:  # type: ignore[override]
    # まずv184の取得・表示をそのまま出す
    _V185_PREV_RENDER_SELECTED_AREA()
    # その下にv185の3:4/チラシ合成を追加
    render_v185_3x4_flyer_composite()


# ==================================================
# v186 OVERRIDE: チラシアップロード認識修正版
# 目的:
# - v185で、画面上はアップロード済みでも生成ボタン後に
#   「チラシ画像をアップロードしてください」と出る問題を修正する。
# 原因対策:
# - UploadedFileオブジェクトを直接PILで開くのではなく、必ずbytes化してからBytesIOで開く。
# - アップロード済みチラシbytesを session_state に保持し、ボタン押下の再実行でも消えないようにする。
# - 読み込み失敗時は無言で0枚扱いにせず、診断表示を出す。
# ==================================================


def _v186_uploaded_to_bytes(uploaded) -> Optional[bytes]:
    if uploaded is None:
        return None
    try:
        data = uploaded.getvalue()
        if data:
            return bytes(data)
    except Exception:
        pass
    try:
        uploaded.seek(0)
        data = uploaded.read()
        if data:
            return bytes(data)
    except Exception:
        pass
    return None


def _v186_open_image_from_bytes(data: bytes) -> Optional[Any]:
    if _Image_v185 is None or _io_v185 is None or not data:
        return None
    try:
        return _Image_v185.open(_io_v185.BytesIO(data)).convert("RGBA")
    except Exception:
        return None


def _v186_update_flyer_store(uploaded_files) -> Tuple[List[Dict[str, Any]], List[str]]:
    """アップロードされたチラシをbytesで保存し、以後の再実行でも保持する。"""
    errors: List[str] = []
    stored: List[Dict[str, Any]] = st.session_state.get("v186_flyer_store", []) or []

    if uploaded_files:
        new_store: List[Dict[str, Any]] = []
        seen_hash = set()
        for f in list(uploaded_files)[:10]:
            name = getattr(f, "name", "flyer") or "flyer"
            data = _v186_uploaded_to_bytes(f)
            if not data:
                errors.append(f"{name}: ファイルbytesを読めませんでした")
                continue
            h = _hashlib_v185.md5(data).hexdigest() if _hashlib_v185 is not None else str(len(data)) + name
            if h in seen_hash:
                continue
            seen_hash.add(h)
            img = _v186_open_image_from_bytes(data)
            if img is None:
                errors.append(f"{name}: 画像として開けませんでした")
                continue
            new_store.append({"name": name, "bytes": data, "hash": h, "size": img.size})
        # アップロード欄に1枚以上入っている場合は、現在の選択を正として保存する。
        stored = new_store
        st.session_state["v186_flyer_store"] = stored
    else:
        # 何もアップロードされていない場合でも、直前の保存があればそれを使えるようにする。
        stored = st.session_state.get("v186_flyer_store", []) or []
    return stored, errors


def _v186_store_to_images(store: List[Dict[str, Any]]) -> Tuple[List[Any], List[str]]:
    flyers: List[Any] = []
    errors: List[str] = []
    for i, rec in enumerate(store or [], start=1):
        img = _v186_open_image_from_bytes(rec.get("bytes", b""))
        if img is None:
            errors.append(f"{rec.get('name', 'flyer_'+str(i))}: 保存済みbytesから画像を開けませんでした")
            continue
        flyers.append(img)
    return flyers, errors


def render_v185_3x4_flyer_composite() -> None:  # type: ignore[override]
    st.divider()
    st.subheader("3:4整形・チラシランダム合成 v186（アップロード認識修正版）")
    st.caption("v184で取得したマンション名看板画像を3:4縦長に整え、アップロードしたチラシ画像を下側から自然に合成します。")

    if _Image_v185 is None or _io_v185 is None or _zipfile_v185 is None:
        st.error("Pillow が必要です。PowerShellで `pip install pillow` を実行してください。")
        return

    items = _v185_current_sign_items()
    if not items:
        st.info("まず上の v184 でマンション名看板画像を取得してください。画像ありの結果があると、ここで3:4化・チラシ合成できます。")
        return

    st.success(f"合成対象：マンション名看板画像 {len(items)}件")

    with st.expander("チラシ画像アップロード / 合成設定", expanded=True):
        uploaded_files = st.file_uploader(
            "チラシだけの画像をアップロード（最大10枚程度）",
            type=["png", "jpg", "jpeg", "webp"],
            accept_multiple_files=True,
            key="v186_flyer_uploads",
        )
        flyer_store, upload_errors = _v186_update_flyer_store(uploaded_files)

        if flyer_store:
            names = [str(x.get("name", "flyer")) for x in flyer_store]
            st.success(f"チラシ画像を認識しました：{len(flyer_store)}枚（{', '.join(names[:5])}{' ほか' if len(names) > 5 else ''}）")
        else:
            st.warning("チラシ画像はまだ認識されていません。アップロード後にこの表示が『認識しました』へ変わるか確認してください。")

        if upload_errors:
            with st.expander("チラシ読み込み診断", expanded=True):
                for e in upload_errors:
                    st.error(e)

        c1, c2, c3, c4 = st.columns(4)
        out_w = int(c1.number_input("出力横幅", 360, 1800, 900, 60, key="v185_out_w"))
        max_items = int(c2.number_input("生成上限", 1, 200, min(60, len(items)), 1, key="v185_max_items"))
        seed_mode = c3.selectbox("ランダム", ["毎回変える", "固定seed"], index=0, key="v185_seed_mode")
        seed_val = int(c4.number_input("seed", 0, 999999, 185, 1, key="v185_seed_val"))
        fit_mode = st.radio(
            "3:4化方式",
            ["簡易背景拡張", "自然トリミング"],
            index=0,
            horizontal=True,
            key="v185_fit_mode",
            help="本物のAIアウトペイントではありません。重要情報保持なら簡易背景拡張、縁なし重視なら自然トリミングです。",
        )
        make_base_only = st.checkbox("チラシなし3:4画像も同時に作る", value=False, key="v185_make_base_only")
        clear_flyers = st.checkbox("チラシ保存をクリアする", value=False, key="v186_clear_flyers")
        if clear_flyers:
            st.session_state["v186_flyer_store"] = []
            flyer_store = []
            st.info("チラシ保存をクリアしました。新しくアップロードしてください。")

        st.caption("※ v186はローカルPillow処理です。本格的なAIアウトペイントは、別途画像生成/補完API接続が必要です。")

    flyers, stored_errors = _v186_store_to_images(st.session_state.get("v186_flyer_store", []) or [])
    if stored_errors:
        with st.expander("保存済みチラシ診断", expanded=True):
            for e in stored_errors:
                st.error(e)

    run = st.button("3:4整形・チラシ合成を生成（v186）", type="primary", use_container_width=True, key="v186_run")

    if run:
        # ボタン押下時にも念のため最新アップロード欄から再取得する。
        flyer_store, upload_errors = _v186_update_flyer_store(st.session_state.get("v186_flyer_uploads", []) or [])
        flyers, stored_errors = _v186_store_to_images(flyer_store)
        if not flyers and not make_base_only:
            st.warning("チラシ画像を認識できていません。上の表示が『チラシ画像を認識しました』になっているか確認してください。チラシなしで3:4だけ作る場合は『チラシなし3:4画像も同時に作る』にチェックしてください。")
            with st.expander("v186 チラシ診断", expanded=True):
                st.write("アップロード欄の件数:", len(st.session_state.get("v186_flyer_uploads", []) or []))
                st.write("保存済みチラシ件数:", len(flyer_store or []))
                st.write("画像として開けた件数:", len(flyers or []))
                st.write("アップロードエラー:", upload_errors)
                st.write("保存済みエラー:", stored_errors)
            return

        rng = random.Random(seed_val if seed_mode == "固定seed" else int(time.time() * 1000) % 100000000)
        outputs: List[Dict[str, Any]] = []
        progress = st.progress(0.0, text="3:4整形・合成中...")
        target_items = items[:max_items]
        for idx, item in enumerate(target_items, start=1):
            progress.progress((idx - 1) / max(1, len(target_items)), text=f"{idx}/{len(target_items)} {item['name']} を処理中...")
            base_src = _v185_fetch_image(item["image_url"])
            if base_src is None:
                continue
            base_34 = _v185_crop_or_expand_to_3x4(base_src, out_w=out_w, mode=fit_mode)

            if make_base_only:
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_3x4.png"
                outputs.append({
                    **item,
                    "filename": filename,
                    "png": _v185_image_to_png_bytes(base_34),
                    "flyer_index": "none",
                    "placement": "3x4_only",
                })

            if flyers:
                flyer_i = rng.randrange(len(flyers))
                comp, place = _v185_composite_flyer(base_34, flyers[flyer_i], rng, position_mode="ランダム下側")
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_flyer.png"
                outputs.append({
                    **item,
                    "filename": filename,
                    "png": _v185_image_to_png_bytes(comp),
                    "flyer_index": flyer_i + 1,
                    "placement": str(place),
                })
        progress.progress(1.0, text="生成完了")
        st.session_state["v185_outputs"] = outputs

    outputs = st.session_state.get("v185_outputs", []) or []
    if outputs:
        st.success(f"生成完了：{len(outputs)}枚")
        zip_bytes = _v185_build_zip(outputs)
        st.download_button(
            "3:4・チラシ合成画像ZIPをダウンロード",
            data=zip_bytes,
            file_name="v186_3x4_flyer_composite_images.zip",
            mime="application/zip",
            use_container_width=True,
            key="v186_zip_download",
        )
        with st.expander("生成画像プレビュー", expanded=True):
            preview = outputs[:12]
            cols = st.columns(3)
            for i, item in enumerate(preview):
                with cols[i % 3]:
                    st.image(item["png"], caption=f"{item.get('name','')}\n{item.get('address','')}", use_container_width=True)
                    st.caption(item.get("filename", ""))
        if len(outputs) > 12:
            st.caption(f"プレビューは先頭12枚のみ表示しています。全{len(outputs)}枚はZIPに入っています。")


try:
    _V186_PREV_RENDER_SELECTED_AREA = _V185_PREV_RENDER_SELECTED_AREA
except Exception:
    _V186_PREV_RENDER_SELECTED_AREA = render_selected_area_livable_sign_images_v170


def render_selected_area_livable_sign_images_v170() -> None:  # type: ignore[override]
    # まずv184の取得・表示をそのまま出す
    _V186_PREV_RENDER_SELECTED_AREA()
    # その下にv186の3:4/チラシ合成を追加
    render_v185_3x4_flyer_composite()




# ==================================================
# v187 OVERRIDE: チラシ画像デコード強化版
# 目的:
# - v186で、アップロード欄には表示されるのに「画像として開けませんでした」になる問題を修正する。
# 対策:
# - PILの壊れかけ画像許容をON
# - PNG/JPEG/WebP/GIFのシグネチャ位置を探して、余計な先頭バイトがあれば除去
# - dataURL/base64文字列だった場合もデコード
# - PILで開けない場合は OpenCV(cv2) でも読み込みを試す
# - それでも失敗した場合は、bytes長と先頭バイトを診断に出す
# ==================================================

try:
    from PIL import ImageFile as _ImageFile_v187, ImageOps as _ImageOps_v187
    try:
        _ImageFile_v187.LOAD_TRUNCATED_IMAGES = True
    except Exception:
        pass
except Exception:
    _ImageFile_v187 = None
    _ImageOps_v187 = None

try:
    import base64 as _base64_v187
except Exception:
    _base64_v187 = None

try:
    import numpy as _np_v187
    import cv2 as _cv2_v187
except Exception:
    _np_v187 = None
    _cv2_v187 = None

_V187_SIGS = [
    b"\x89PNG\r\n\x1a\n",
    b"\xff\xd8\xff",
    b"RIFF",  # WebPは RIFF....WEBP
    b"GIF87a",
    b"GIF89a",
]


def _v187_strip_to_image_signature(data: bytes) -> bytes:
    if not data:
        return data
    data = bytes(data)
    # data:image/png;base64,... のような文字列で来た場合の保険
    head = data[:80].lower()
    if head.startswith(b"data:image") and b"base64," in head and _base64_v187 is not None:
        try:
            b64 = data.split(b"base64,", 1)[1]
            return _base64_v187.b64decode(b64, validate=False)
        except Exception:
            pass
    # BOM/空白除去
    data2 = data.lstrip(b"\xef\xbb\xbf\x00\r\n\t ")
    if data2 != data:
        data = data2
    # 先頭に余計なバイトが混じるケースの保険。最初の2KBまで探す。
    best = None
    for sig in _V187_SIGS:
        pos = data.find(sig, 0, min(len(data), 2048))
        if pos >= 0:
            best = pos if best is None else min(best, pos)
    if best and best > 0:
        return data[best:]
    return data


def _v187_open_image_from_bytes(data: bytes) -> Tuple[Optional[Any], str]:
    """bytesから画像を開く。戻り値: (PIL画像, エラー文字列)。"""
    if _Image_v185 is None or _io_v185 is None or not data:
        return None, "画像ライブラリまたはbytesが空です"
    raw_len = len(data or b"")
    data = _v187_strip_to_image_signature(data)
    head_hex = (data[:16] or b"").hex(" ")

    # 1) PILで通常読み込み
    try:
        bio = _io_v185.BytesIO(data)
        img = _Image_v185.open(bio)
        try:
            if _ImageOps_v187 is not None:
                img = _ImageOps_v187.exif_transpose(img)
        except Exception:
            pass
        try:
            img.load()
        except Exception:
            # LOAD_TRUNCATED_IMAGESで通ることがあるので続行
            pass
        return img.convert("RGBA"), ""
    except Exception as e1:
        pil_err = str(e1)

    # 2) OpenCV fallback
    if _cv2_v187 is not None and _np_v187 is not None:
        try:
            arr = _np_v187.frombuffer(data, dtype=_np_v187.uint8)
            cv_img = _cv2_v187.imdecode(arr, _cv2_v187.IMREAD_UNCHANGED)
            if cv_img is not None:
                if len(cv_img.shape) == 2:
                    cv_img = _cv2_v187.cvtColor(cv_img, _cv2_v187.COLOR_GRAY2RGBA)
                elif cv_img.shape[2] == 4:
                    cv_img = _cv2_v187.cvtColor(cv_img, _cv2_v187.COLOR_BGRA2RGBA)
                else:
                    cv_img = _cv2_v187.cvtColor(cv_img, _cv2_v187.COLOR_BGR2RGBA)
                img = _Image_v185.fromarray(cv_img)
                return img.convert("RGBA"), ""
        except Exception as e2:
            return None, f"PIL失敗: {pil_err} / OpenCV失敗: {e2} / bytes={raw_len} / head={head_hex}"

    return None, f"PIL失敗: {pil_err} / bytes={raw_len} / head={head_hex}"


def _v186_open_image_from_bytes(data: bytes) -> Optional[Any]:  # type: ignore[override]
    img, _err = _v187_open_image_from_bytes(data)
    return img


def _v186_update_flyer_store(uploaded_files) -> Tuple[List[Dict[str, Any]], List[str]]:  # type: ignore[override]
    """v187: アップロードされたチラシを、より頑丈にbytes→画像化して保存する。"""
    errors: List[str] = []
    stored: List[Dict[str, Any]] = st.session_state.get("v187_flyer_store", []) or st.session_state.get("v186_flyer_store", []) or []

    if uploaded_files:
        new_store: List[Dict[str, Any]] = []
        seen_hash = set()
        for f in list(uploaded_files)[:10]:
            name = getattr(f, "name", "flyer") or "flyer"
            data = _v186_uploaded_to_bytes(f)
            if not data:
                errors.append(f"{name}: ファイルbytesを読めませんでした")
                continue
            data = _v187_strip_to_image_signature(data)
            h = _hashlib_v185.md5(data).hexdigest() if _hashlib_v185 is not None else str(len(data)) + name
            if h in seen_hash:
                continue
            seen_hash.add(h)
            img, err = _v187_open_image_from_bytes(data)
            if img is None:
                errors.append(f"{name}: 画像として開けませんでした（{err}）")
                continue
            new_store.append({"name": name, "bytes": data, "hash": h, "size": img.size})
        stored = new_store
        st.session_state["v187_flyer_store"] = stored
        st.session_state["v186_flyer_store"] = stored
    else:
        stored = st.session_state.get("v187_flyer_store", []) or st.session_state.get("v186_flyer_store", []) or []
    return stored, errors


def _v186_store_to_images(store: List[Dict[str, Any]]) -> Tuple[List[Any], List[str]]:  # type: ignore[override]
    flyers: List[Any] = []
    errors: List[str] = []
    for i, rec in enumerate(store or [], start=1):
        img, err = _v187_open_image_from_bytes(rec.get("bytes", b""))
        if img is None:
            errors.append(f"{rec.get('name', 'flyer_'+str(i))}: 保存済みbytesから画像を開けませんでした（{err}）")
            continue
        flyers.append(img)
    return flyers, errors


def render_v185_3x4_flyer_composite() -> None:  # type: ignore[override]
    st.divider()
    st.subheader("3:4整形・チラシランダム合成 v187（画像読み込み強化版）")
    st.caption("v184で取得したマンション名看板画像を3:4縦長に整え、アップロードしたチラシ画像を下側から自然に合成します。")

    if _Image_v185 is None or _io_v185 is None or _zipfile_v185 is None:
        st.error("Pillow が必要です。PowerShellで `pip install pillow` を実行してください。")
        return

    items = _v185_current_sign_items()
    if not items:
        st.info("まず上の v184 でマンション名看板画像を取得してください。画像ありの結果があると、ここで3:4化・チラシ合成できます。")
        return

    st.success(f"合成対象：マンション名看板画像 {len(items)}件")

    with st.expander("チラシ画像アップロード / 合成設定", expanded=True):
        uploaded_files = st.file_uploader(
            "チラシだけの画像をアップロード（最大10枚程度）",
            type=["png", "jpg", "jpeg", "webp", "gif"],
            accept_multiple_files=True,
            key="v187_flyer_uploads",
        )
        flyer_store, upload_errors = _v186_update_flyer_store(uploaded_files)

        if flyer_store:
            names = [str(x.get("name", "flyer")) for x in flyer_store]
            st.success(f"チラシ画像を認識しました：{len(flyer_store)}枚（{', '.join(names[:5])}{' ほか' if len(names) > 5 else ''}）")
            try:
                preview_imgs, _ = _v186_store_to_images(flyer_store[:3])
                if preview_imgs:
                    cols_prev = st.columns(min(3, len(preview_imgs)))
                    for pi, im in enumerate(preview_imgs):
                        with cols_prev[pi % len(cols_prev)]:
                            st.image(im, caption=names[pi] if pi < len(names) else "チラシ", use_container_width=True)
            except Exception:
                pass
        else:
            st.warning("チラシ画像はまだ認識されていません。アップロード後にこの表示が『認識しました』へ変わるか確認してください。")

        if upload_errors:
            with st.expander("チラシ読み込み診断", expanded=True):
                for e in upload_errors:
                    st.error(e)
                st.caption("この診断に bytes/head が出ている場合、画像ファイルの中身が一般的なPNG/JPEG/WebPとして読めていません。別形式で保存し直すか、スマホ側でスクショではなく写真として保存した画像を試してください。")

        c1, c2, c3, c4 = st.columns(4)
        out_w = int(c1.number_input("出力横幅", 360, 1800, 900, 60, key="v185_out_w"))
        max_items = int(c2.number_input("生成上限", 1, 200, min(60, len(items)), 1, key="v185_max_items"))
        seed_mode = c3.selectbox("ランダム", ["毎回変える", "固定seed"], index=0, key="v185_seed_mode")
        seed_val = int(c4.number_input("seed", 0, 999999, 185, 1, key="v185_seed_val"))
        fit_mode = st.radio(
            "3:4化方式",
            ["簡易背景拡張", "自然トリミング"],
            index=0,
            horizontal=True,
            key="v185_fit_mode",
            help="本物のAIアウトペイントではありません。重要情報保持なら簡易背景拡張、縁なし重視なら自然トリミングです。",
        )
        make_base_only = st.checkbox("チラシなし3:4画像も同時に作る", value=False, key="v185_make_base_only")
        clear_flyers = st.checkbox("チラシ保存をクリアする", value=False, key="v187_clear_flyers")
        if clear_flyers:
            st.session_state["v187_flyer_store"] = []
            st.session_state["v186_flyer_store"] = []
            flyer_store = []
            st.info("チラシ保存をクリアしました。新しくアップロードしてください。")

        st.caption("※ v187はローカルPillow/OpenCV補助処理です。本格的なAIアウトペイントは、別途画像生成/補完API接続が必要です。")

    flyers, stored_errors = _v186_store_to_images(st.session_state.get("v187_flyer_store", []) or st.session_state.get("v186_flyer_store", []) or [])
    if stored_errors:
        with st.expander("保存済みチラシ診断", expanded=True):
            for e in stored_errors:
                st.error(e)

    run = st.button("3:4整形・チラシ合成を生成（v187）", type="primary", use_container_width=True, key="v187_run")

    if run:
        flyer_store, upload_errors = _v186_update_flyer_store(st.session_state.get("v187_flyer_uploads", []) or [])
        flyers, stored_errors = _v186_store_to_images(flyer_store)
        if not flyers and not make_base_only:
            st.warning("チラシ画像を認識できていません。上の表示が『チラシ画像を認識しました』になっているか確認してください。チラシなしで3:4だけ作る場合は『チラシなし3:4画像も同時に作る』にチェックしてください。")
            with st.expander("v187 チラシ診断", expanded=True):
                st.write("アップロード欄の件数:", len(st.session_state.get("v187_flyer_uploads", []) or []))
                st.write("保存済みチラシ件数:", len(flyer_store or []))
                st.write("画像として開けた件数:", len(flyers or []))
                st.write("アップロードエラー:", upload_errors)
                st.write("保存済みエラー:", stored_errors)
            return

        rng = random.Random(seed_val if seed_mode == "固定seed" else int(time.time() * 1000) % 100000000)
        outputs: List[Dict[str, Any]] = []
        progress = st.progress(0.0, text="3:4整形・合成中...")
        target_items = items[:max_items]
        for idx, item in enumerate(target_items, start=1):
            progress.progress((idx - 1) / max(1, len(target_items)), text=f"{idx}/{len(target_items)} {item['name']} を処理中...")
            base_src = _v185_fetch_image(item["image_url"])
            if base_src is None:
                continue
            base_34 = _v185_crop_or_expand_to_3x4(base_src, out_w=out_w, mode=fit_mode)

            if make_base_only:
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_3x4.png"
                outputs.append({
                    **item,
                    "filename": filename,
                    "png": _v185_image_to_png_bytes(base_34),
                    "flyer_index": "none",
                    "placement": "3x4_only",
                })

            if flyers:
                flyer_i = rng.randrange(len(flyers))
                comp, place = _v185_composite_flyer(base_34, flyers[flyer_i], rng, position_mode="ランダム下側")
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_flyer.png"
                outputs.append({
                    **item,
                    "filename": filename,
                    "png": _v185_image_to_png_bytes(comp),
                    "flyer_index": flyer_i + 1,
                    "placement": str(place),
                })
        progress.progress(1.0, text="生成完了")
        st.session_state["v185_outputs"] = outputs

    outputs = st.session_state.get("v185_outputs", []) or []
    if outputs:
        st.success(f"生成完了：{len(outputs)}枚")
        zip_bytes = _v185_build_zip(outputs)
        st.download_button(
            "3:4・チラシ合成画像ZIPをダウンロード",
            data=zip_bytes,
            file_name="v187_3x4_flyer_composite_images.zip",
            mime="application/zip",
            use_container_width=True,
            key="v187_zip_download",
        )
        with st.expander("生成画像プレビュー", expanded=True):
            preview = outputs[:12]
            cols = st.columns(3)
            for i, item in enumerate(preview):
                with cols[i % 3]:
                    st.image(item["png"], caption=f"{item.get('name','')}\n{item.get('address','')}", use_container_width=True)
                    st.caption(item.get("filename", ""))
        if len(outputs) > 12:
            st.caption(f"プレビューは先頭12枚のみ表示しています。全{len(outputs)}枚はZIPに入っています。")


def render_selected_area_livable_sign_images_v170() -> None:  # type: ignore[override]
    _V185_PREV_RENDER_SELECTED_AREA()
    render_v185_3x4_flyer_composite()



# ==================================================
# v188 OVERRIDE: 3:4縁取り対策 + チラシ角度強化
# 目的:
# - v187の「簡易背景拡張」で、元画像を中に置いたような縁取り/枠感が出る問題を修正。
# - 白フチ/黒フチ/単純余白ではなく、外周を元画像の端から自然に延長した3:4にする。
# - ローカルPillowのみなので本物の生成AIアウトペイントではないが、枠感を消すため
#   端の壁・床・道路・植栽を引き伸ばし/反転/ぼかし/フェザーで補完する。
# - チラシは合成自体は成功したため、たまにもう少し横向きの角度も出るようにする。
# ==================================================

def _v188_feather_mask(size: Tuple[int, int], blend: int, fade_top: bool, fade_bottom: bool, fade_left: bool, fade_right: bool):
    if _Image_v185 is None:
        return None
    w, h = size
    mask = _Image_v185.new('L', (w, h), 255)
    if blend <= 0:
        return mask
    try:
        px = mask.load()
        for y in range(h):
            v = 255
            if fade_top and y < blend:
                v = min(v, int(255 * y / max(1, blend)))
            if fade_bottom and y >= h - blend:
                v = min(v, int(255 * (h - 1 - y) / max(1, blend)))
            if v < 255:
                for x in range(w):
                    px[x, y] = min(px[x, y], max(0, v))
        for x in range(w):
            v = 255
            if fade_left and x < blend:
                v = min(v, int(255 * x / max(1, blend)))
            if fade_right and x >= w - blend:
                v = min(v, int(255 * (w - 1 - x) / max(1, blend)))
            if v < 255:
                for y in range(h):
                    px[x, y] = min(px[x, y], max(0, v))
    except Exception:
        pass
    return mask


def _v188_edge_extend_canvas(main, out_w: int, out_h: int):
    """元画像を3:4内に収め、足りない外周を端画像から補完する。枠/縁取りを作らない。"""
    img = main.convert('RGBA')
    iw, ih = img.size
    if iw <= 0 or ih <= 0:
        return img.resize((out_w, out_h), _Image_v185.Resampling.LANCZOS)

    # 重要情報を残すため、まず画像全体を3:4内にfit。余った部分だけ外周補完。
    scale = min(out_w / iw, out_h / ih)
    nw, nh = max(1, int(iw * scale)), max(1, int(ih * scale))
    fg = img.resize((nw, nh), _Image_v185.Resampling.LANCZOS)
    x = (out_w - nw) // 2
    y = (out_h - nh) // 2

    # ベースはcover cropを強めにぼかしたもの。端補完の隙間や角だけに使う。
    try:
        canvas = _ImageOps_v185.fit(img, (out_w, out_h), method=_Image_v185.Resampling.LANCZOS, centering=(0.5, 0.5)).convert('RGBA')
        canvas = canvas.filter(_ImageFilter_v185.GaussianBlur(radius=max(8, out_w // 70)))
        canvas = _ImageEnhance_v185.Contrast(canvas).enhance(0.94)
        canvas = _ImageEnhance_v185.Brightness(canvas).enhance(0.98)
    except Exception:
        canvas = _Image_v185.new('RGBA', (out_w, out_h), (0, 0, 0, 255))

    # 足りない上下を、元画像の上端/下端から反転拡張。
    try:
        strip_h = max(6, min(nh, int(nh * 0.18)))
        if y > 0 and strip_h > 0:
            top = fg.crop((0, 0, nw, strip_h))
            top = _ImageOps_v185.flip(top).resize((nw, y), _Image_v185.Resampling.BICUBIC)
            top = top.filter(_ImageFilter_v185.GaussianBlur(radius=max(1, out_w // 450)))
            canvas.alpha_composite(top, (x, 0))
        bottom_gap = out_h - (y + nh)
        if bottom_gap > 0 and strip_h > 0:
            bottom = fg.crop((0, max(0, nh - strip_h), nw, nh))
            bottom = _ImageOps_v185.flip(bottom).resize((nw, bottom_gap), _Image_v185.Resampling.BICUBIC)
            bottom = bottom.filter(_ImageFilter_v185.GaussianBlur(radius=max(1, out_w // 450)))
            canvas.alpha_composite(bottom, (x, y + nh))
    except Exception:
        pass

    # 足りない左右を、元画像の左端/右端から反転拡張。
    try:
        strip_w = max(6, min(nw, int(nw * 0.18)))
        if x > 0 and strip_w > 0:
            left = fg.crop((0, 0, strip_w, nh))
            left = _ImageOps_v185.mirror(left).resize((x, nh), _Image_v185.Resampling.BICUBIC)
            left = left.filter(_ImageFilter_v185.GaussianBlur(radius=max(1, out_w // 450)))
            canvas.alpha_composite(left, (0, y))
        right_gap = out_w - (x + nw)
        if right_gap > 0 and strip_w > 0:
            right = fg.crop((max(0, nw - strip_w), 0, nw, nh))
            right = _ImageOps_v185.mirror(right).resize((right_gap, nh), _Image_v185.Resampling.BICUBIC)
            right = right.filter(_ImageFilter_v185.GaussianBlur(radius=max(1, out_w // 450)))
            canvas.alpha_composite(right, (x + nw, y))
    except Exception:
        pass

    # 元画像をそのまま貼る。ただし外周だけ少しフェザーして、四角い境目を消す。
    try:
        blend = max(10, min(42, out_w // 24))
        mask = _v188_feather_mask(
            (nw, nh),
            blend,
            fade_top=(y > 0),
            fade_bottom=(out_h - (y + nh) > 0),
            fade_left=(x > 0),
            fade_right=(out_w - (x + nw) > 0),
        )
        # 元のアルファがある場合は掛け合わせる
        try:
            alpha = fg.getchannel('A')
            mask = _ImageChops_v185.multiply(mask, alpha)
        except Exception:
            pass
        canvas.paste(fg, (x, y), mask)
    except Exception:
        canvas.alpha_composite(fg, (x, y))

    return canvas.convert('RGBA')


def _v185_crop_or_expand_to_3x4(img, out_w: int = 900, mode: str = "外周補完風3:4（縁なし）"):  # type: ignore[override]
    """v188: 3:4整形。
    - 外周補完風3:4（縁なし）: 元画像を残しつつ、足りない外周を端画像から自然に延長。枠感を出さない。
    - 自然トリミング: cover crop。縁なしだが端が切れる場合あり。
    - 簡易背景拡張（旧）: v187以前のぼかし背景方式。確認用に残す。
    """
    if _Image_v185 is None:
        return img
    img = img.convert('RGBA')
    out_w = int(out_w or 900)
    out_h = int(round(out_w * 4 / 3))
    if out_w < 360:
        out_w, out_h = 360, 480

    if mode == "自然トリミング":
        return _ImageOps_v185.fit(img, (out_w, out_h), method=_Image_v185.Resampling.LANCZOS, centering=(0.5, 0.5)).convert('RGBA')

    if "旧" in str(mode) or str(mode) == "簡易背景拡張":
        bg = _ImageOps_v185.fit(img, (out_w, out_h), method=_Image_v185.Resampling.LANCZOS, centering=(0.5, 0.5)).convert('RGBA')
        try:
            bg = bg.filter(_ImageFilter_v185.GaussianBlur(radius=max(10, out_w // 45)))
            bg = _ImageEnhance_v185.Contrast(bg).enhance(0.92)
            bg = _ImageEnhance_v185.Brightness(bg).enhance(0.96)
        except Exception:
            pass
        iw, ih = img.size
        scale = min(out_w / max(1, iw), out_h / max(1, ih))
        scale = min(scale * 0.98, out_w / max(1, iw), out_h / max(1, ih))
        nw, nh = max(1, int(iw * scale)), max(1, int(ih * scale))
        fg = img.resize((nw, nh), _Image_v185.Resampling.LANCZOS)
        x = (out_w - nw) // 2
        y = (out_h - nh) // 2
        bg.alpha_composite(fg, (x, y))
        return bg.convert('RGBA')

    return _v188_edge_extend_canvas(img, out_w, out_h)


def _v185_prepare_flyer(flyer, canvas_w: int, rng: random.Random, size_ratio: float = 0.42):  # type: ignore[override]
    """v188: チラシ合成は成功。たまに少し横向き強めも混ぜる。"""
    flyer = _v185_trim_transparent_or_white(flyer).convert('RGBA')
    fw, fh = flyer.size
    target_w = int(canvas_w * max(0.22, min(0.65, size_ratio)))
    target_h = int(fh * (target_w / fw)) if fw > 0 else target_w
    flyer = flyer.resize((max(1, target_w), max(1, target_h)), _Image_v185.Resampling.LANCZOS)
    try:
        flyer = _ImageEnhance_v185.Brightness(flyer).enhance(rng.uniform(0.94, 1.07))
        flyer = _ImageEnhance_v185.Contrast(flyer).enhance(rng.uniform(0.96, 1.06))
    except Exception:
        pass

    # 多くは自然な軽い角度。約35%だけ横向き強めを混ぜる。
    if rng.random() < 0.35:
        angle = rng.choice([-1, 1]) * rng.uniform(16.0, 30.0)
    else:
        angle = rng.uniform(-14.0, 14.0)
    flyer = flyer.rotate(angle, resample=_Image_v185.Resampling.BICUBIC, expand=True)
    return flyer, angle


def render_v185_3x4_flyer_composite() -> None:  # type: ignore[override]
    st.divider()
    st.subheader("3:4整形・チラシランダム合成 v188（縁なし外周補完風）")
    st.caption("v187で成功したチラシ合成を維持し、3:4化は白フチ/黒フチ/枠感を避ける外周補完風に変更しました。")

    if _Image_v185 is None or _io_v185 is None or _zipfile_v185 is None:
        st.error("Pillow が必要です。PowerShellで `pip install pillow` を実行してください。")
        return

    items = _v185_current_sign_items()
    if not items:
        st.info("まず上の v184 でマンション名看板画像を取得してください。画像ありの結果があると、ここで3:4化・チラシ合成できます。")
        return

    st.success(f"合成対象：マンション名看板画像 {len(items)}件")

    with st.expander("チラシ画像アップロード / 合成設定", expanded=True):
        uploaded_files = st.file_uploader(
            "チラシだけの画像をアップロード（最大10枚程度）",
            type=["png", "jpg", "jpeg", "webp", "gif"],
            accept_multiple_files=True,
            key="v188_flyer_uploads",
        )
        flyer_store, upload_errors = _v186_update_flyer_store(uploaded_files)

        if flyer_store:
            names = [str(x.get("name", "flyer")) for x in flyer_store]
            st.success(f"チラシ画像を認識しました：{len(flyer_store)}枚（{', '.join(names[:5])}{' ほか' if len(names) > 5 else ''}）")
            try:
                preview_imgs, _ = _v186_store_to_images(flyer_store[:3])
                if preview_imgs:
                    cols_prev = st.columns(min(3, len(preview_imgs)))
                    for pi, im in enumerate(preview_imgs):
                        with cols_prev[pi % len(cols_prev)]:
                            st.image(im, caption=names[pi] if pi < len(names) else "チラシ", use_container_width=True)
            except Exception:
                pass
        else:
            st.warning("チラシ画像はまだ認識されていません。アップロード後にこの表示が『認識しました』へ変わるか確認してください。")

        if upload_errors:
            with st.expander("チラシ読み込み診断", expanded=True):
                for e in upload_errors:
                    st.error(e)

        c1, c2, c3, c4 = st.columns(4)
        out_w = int(c1.number_input("出力横幅", 360, 1800, 900, 60, key="v188_out_w"))
        max_items = int(c2.number_input("生成上限", 1, 200, min(60, len(items)), 1, key="v188_max_items"))
        seed_mode = c3.selectbox("ランダム", ["毎回変える", "固定seed"], index=0, key="v188_seed_mode")
        seed_val = int(c4.number_input("seed", 0, 999999, 188, 1, key="v188_seed_val"))
        fit_mode = st.radio(
            "3:4化方式",
            ["外周補完風3:4（縁なし）", "自然トリミング", "簡易背景拡張（旧）"],
            index=0,
            horizontal=True,
            key="v188_fit_mode",
            help="通常は『外周補完風3:4（縁なし）』を使ってください。白フチ/黒フチ/枠感を出さず、端の背景を自然に延長します。",
        )
        make_base_only = st.checkbox("チラシなし3:4画像も同時に作る", value=False, key="v188_make_base_only")
        clear_flyers = st.checkbox("チラシ保存をクリアする", value=False, key="v188_clear_flyers")
        if clear_flyers:
            st.session_state["v187_flyer_store"] = []
            st.session_state["v186_flyer_store"] = []
            flyer_store = []
            st.info("チラシ保存をクリアしました。新しくアップロードしてください。")

        st.caption("※ v188はローカルPillow処理です。本物の生成AIアウトペイントではありませんが、縁取りではなく外周補完風で3:4化します。")

    flyers, stored_errors = _v186_store_to_images(st.session_state.get("v187_flyer_store", []) or st.session_state.get("v186_flyer_store", []) or [])
    if stored_errors:
        with st.expander("保存済みチラシ診断", expanded=True):
            for e in stored_errors:
                st.error(e)

    run = st.button("3:4整形・チラシ合成を生成（v188）", type="primary", use_container_width=True, key="v188_run")

    if run:
        flyer_store, upload_errors = _v186_update_flyer_store(st.session_state.get("v188_flyer_uploads", []) or [])
        flyers, stored_errors = _v186_store_to_images(flyer_store)
        if not flyers and not make_base_only:
            st.warning("チラシ画像を認識できていません。上の表示が『チラシ画像を認識しました』になっているか確認してください。チラシなしで3:4だけ作る場合は『チラシなし3:4画像も同時に作る』にチェックしてください。")
            with st.expander("v188 チラシ診断", expanded=True):
                st.write("アップロード欄の件数:", len(st.session_state.get("v188_flyer_uploads", []) or []))
                st.write("保存済みチラシ件数:", len(flyer_store or []))
                st.write("画像として開けた件数:", len(flyers or []))
                st.write("アップロードエラー:", upload_errors)
                st.write("保存済みエラー:", stored_errors)
            return

        rng = random.Random(seed_val if seed_mode == "固定seed" else int(time.time() * 1000) % 100000000)
        outputs: List[Dict[str, Any]] = []
        progress = st.progress(0.0, text="3:4整形・合成中...")
        target_items = items[:max_items]
        for idx, item in enumerate(target_items, start=1):
            progress.progress((idx - 1) / max(1, len(target_items)), text=f"{idx}/{len(target_items)} {item['name']} を処理中...")
            base_src = _v185_fetch_image(item["image_url"])
            if base_src is None:
                continue
            base_34 = _v185_crop_or_expand_to_3x4(base_src, out_w=out_w, mode=fit_mode)

            if make_base_only:
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_3x4.png"
                outputs.append({
                    **item,
                    "filename": filename,
                    "png": _v185_image_to_png_bytes(base_34),
                    "flyer_index": "none",
                    "placement": "3x4_only",
                })

            if flyers:
                flyer_i = rng.randrange(len(flyers))
                comp, place = _v185_composite_flyer(base_34, flyers[flyer_i], rng, position_mode="ランダム下側")
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_flyer.png"
                outputs.append({
                    **item,
                    "filename": filename,
                    "png": _v185_image_to_png_bytes(comp),
                    "flyer_index": flyer_i + 1,
                    "placement": str(place),
                })
        progress.progress(1.0, text="生成完了")
        st.session_state["v185_outputs"] = outputs

    outputs = st.session_state.get("v185_outputs", []) or []
    if outputs:
        st.success(f"生成完了：{len(outputs)}枚")
        zip_bytes = _v185_build_zip(outputs)
        st.download_button(
            "3:4・チラシ合成画像ZIPをダウンロード",
            data=zip_bytes,
            file_name="v188_3x4_flyer_composite_images.zip",
            mime="application/zip",
            use_container_width=True,
            key="v188_zip_download",
        )
        with st.expander("生成画像プレビュー", expanded=True):
            preview = outputs[:12]
            cols = st.columns(3)
            for i, item in enumerate(preview):
                with cols[i % 3]:
                    st.image(item["png"], caption=f"{item.get('name','')}\n{item.get('address','')}", use_container_width=True)
                    st.caption(item.get("filename", ""))
        if len(outputs) > 12:
            st.caption(f"プレビューは先頭12枚のみ表示しています。全{len(outputs)}枚はZIPに入っています。")


# ==================================================
# v190 OVERRIDE: 偽アウトペイント停止 + 縁なし安全3:4
# 目的:
# - v188の外周補完風で、タイル/壁/看板が伸びて変形する問題を停止。
# - ローカルPillowだけでChatGPT級アウトペイントを再現するのは無理なので、
#   標準は「自然トリミング（縁なし）」に戻す。
# - 情報保持したい場合だけ OpenCV inpaint の補完風を実験モードとして残す。
# - チラシ合成の良さは維持し、たまに横向き角度も混ぜる。
# ==================================================

def _v190_target_size(out_w: int) -> Tuple[int, int]:
    out_w = int(out_w or 900)
    if out_w < 360:
        out_w = 360
    return out_w, int(round(out_w * 4 / 3))


def _v190_natural_cover_crop_3x4(img, out_w: int = 900):
    """縁なし最優先。画像全体を3:4画面いっぱいにするので、白フチ/黒フチ/枠感は出ない。"""
    if _Image_v185 is None:
        return img
    out_w, out_h = _v190_target_size(out_w)
    img = img.convert("RGBA")
    return _ImageOps_v185.fit(
        img,
        (out_w, out_h),
        method=_Image_v185.Resampling.LANCZOS,
        centering=(0.5, 0.5),
    ).convert("RGBA")


def _v190_opencv_inpaint_outpaint_3x4(img, out_w: int = 900):
    """OpenCVが入っている場合だけ使う補完風。
    画像全体を3:4内に収め、足りない外周だけをinpaintで埋める。
    v188のような反転/引き伸ばしは使わない。
    """
    if _Image_v185 is None:
        return img
    out_w, out_h = _v190_target_size(out_w)
    img = img.convert("RGBA")
    iw, ih = img.size
    if iw <= 0 or ih <= 0:
        return img.resize((out_w, out_h), _Image_v185.Resampling.LANCZOS)

    # cv2が無い環境では安全に自然トリミングへ戻す。
    if globals().get("_cv2_v187") is None or globals().get("_np_v187") is None:
        return _v190_natural_cover_crop_3x4(img, out_w)

    try:
        cv2 = globals().get("_cv2_v187")
        np = globals().get("_np_v187")

        scale = min(out_w / iw, out_h / ih)
        nw, nh = max(1, int(iw * scale)), max(1, int(ih * scale))
        fg = img.resize((nw, nh), _Image_v185.Resampling.LANCZOS).convert("RGB")
        x = (out_w - nw) // 2
        y = (out_h - nh) // 2

        # 黒キャンバス + mask。mask領域はinpaintで埋めるため、値は実質無視される。
        canvas = _Image_v185.new("RGB", (out_w, out_h), (0, 0, 0))
        canvas.paste(fg, (x, y))
        arr = np.array(canvas)

        mask = np.full((out_h, out_w), 255, dtype=np.uint8)
        mask[y:y+nh, x:x+nw] = 0

        # 外周が巨大すぎる場合はinpaintが荒れやすいので、先にcover cropを薄く敷く。
        cover = _v190_natural_cover_crop_3x4(img, out_w).convert("RGB")
        cover_arr = np.array(cover)
        arr[mask > 0] = cover_arr[mask > 0]

        # もう一度maskを指定して、境界から自然に寄せる。
        inpainted = cv2.inpaint(arr, mask, 7, cv2.INPAINT_TELEA)
        return _Image_v185.fromarray(inpainted).convert("RGBA")
    except Exception:
        return _v190_natural_cover_crop_3x4(img, out_w)


def _v190_old_blur_background_3x4(img, out_w: int = 900):
    """旧方式。確認用だけ。枠っぽく見えるので非推奨。"""
    img = img.convert("RGBA")
    out_w, out_h = _v190_target_size(out_w)
    bg = _ImageOps_v185.fit(img, (out_w, out_h), method=_Image_v185.Resampling.LANCZOS, centering=(0.5, 0.5)).convert("RGBA")
    try:
        bg = bg.filter(_ImageFilter_v185.GaussianBlur(radius=max(10, out_w // 45)))
        bg = _ImageEnhance_v185.Contrast(bg).enhance(0.92)
        bg = _ImageEnhance_v185.Brightness(bg).enhance(0.96)
    except Exception:
        pass
    iw, ih = img.size
    scale = min(out_w / max(1, iw), out_h / max(1, ih))
    nw, nh = max(1, int(iw * scale)), max(1, int(ih * scale))
    fg = img.resize((nw, nh), _Image_v185.Resampling.LANCZOS)
    x = (out_w - nw) // 2
    y = (out_h - nh) // 2
    bg.alpha_composite(fg, (x, y))
    return bg.convert("RGBA")


def _v185_crop_or_expand_to_3x4(img, out_w: int = 900, mode: str = "自然トリミング（縁なし・推奨）"):  # type: ignore[override]
    """v190: 3:4整形の本命は自然トリミング。
    v188の外周伸ばしは不自然になったため使わない。
    """
    if _Image_v185 is None:
        return img
    mode = str(mode or "")
    if "OpenCV" in mode or "補完" in mode:
        return _v190_opencv_inpaint_outpaint_3x4(img, out_w)
    if "旧" in mode or "ぼかし" in mode or "背景" in mode:
        return _v190_old_blur_background_3x4(img, out_w)
    return _v190_natural_cover_crop_3x4(img, out_w)


def _v185_prepare_flyer(flyer, canvas_w: int, rng: random.Random, size_ratio: float = 0.42):  # type: ignore[override]
    """v190: チラシ合成は成功しているので維持。少し横向きも混ぜる。"""
    flyer = _v185_trim_transparent_or_white(flyer).convert("RGBA")
    fw, fh = flyer.size
    target_w = int(canvas_w * max(0.22, min(0.65, size_ratio)))
    target_h = int(fh * (target_w / fw)) if fw > 0 else target_w
    flyer = flyer.resize((max(1, target_w), max(1, target_h)), _Image_v185.Resampling.LANCZOS)
    try:
        flyer = _ImageEnhance_v185.Brightness(flyer).enhance(rng.uniform(0.94, 1.07))
        flyer = _ImageEnhance_v185.Contrast(flyer).enhance(rng.uniform(0.96, 1.06))
    except Exception:
        pass

    if rng.random() < 0.38:
        angle = rng.choice([-1, 1]) * rng.uniform(16.0, 30.0)
    else:
        angle = rng.uniform(-14.0, 14.0)
    flyer = flyer.rotate(angle, resample=_Image_v185.Resampling.BICUBIC, expand=True)
    return flyer, angle


def render_v185_3x4_flyer_composite() -> None:  # type: ignore[override]
    st.divider()
    st.subheader("3:4整形・チラシランダム合成 v190（縁なし安全版）")
    st.caption("チラシ合成は維持し、v188の変形しやすい外周伸ばしを停止しました。標準は縁なし自然トリミングです。")

    if _Image_v185 is None or _io_v185 is None or _zipfile_v185 is None:
        st.error("Pillow が必要です。PowerShellで `pip install pillow` を実行してください。")
        return

    items = _v185_current_sign_items()
    if not items:
        st.info("まず上の v184 でマンション名看板画像を取得してください。画像ありの結果があると、ここで3:4化・チラシ合成できます。")
        return

    st.success(f"合成対象：マンション名看板画像 {len(items)}件")

    with st.expander("チラシ画像アップロード / 合成設定", expanded=True):
        uploaded_files = st.file_uploader(
            "チラシだけの画像をアップロード（最大10枚程度）",
            type=["png", "jpg", "jpeg", "webp", "gif"],
            accept_multiple_files=True,
            key="v190_flyer_uploads",
        )
        flyer_store, upload_errors = _v186_update_flyer_store(uploaded_files)

        if flyer_store:
            names = [str(x.get("name", "flyer")) for x in flyer_store]
            st.success(f"チラシ画像を認識しました：{len(flyer_store)}枚（{', '.join(names[:5])}{' ほか' if len(names) > 5 else ''}）")
            try:
                preview_imgs, _ = _v186_store_to_images(flyer_store[:3])
                if preview_imgs:
                    cols_prev = st.columns(min(3, len(preview_imgs)))
                    for pi, im in enumerate(preview_imgs):
                        with cols_prev[pi % len(cols_prev)]:
                            st.image(im, caption=names[pi] if pi < len(names) else "チラシ", use_container_width=True)
            except Exception:
                pass
        else:
            st.warning("チラシ画像はまだ認識されていません。アップロード後にこの表示が『認識しました』へ変わるか確認してください。")

        if upload_errors:
            with st.expander("チラシ読み込み診断", expanded=True):
                for e in upload_errors:
                    st.error(e)

        c1, c2, c3, c4 = st.columns(4)
        out_w = int(c1.number_input("出力横幅", 360, 1800, 900, 60, key="v190_out_w"))
        max_items = int(c2.number_input("生成上限", 1, 200, min(60, len(items)), 1, key="v190_max_items"))
        seed_mode = c3.selectbox("ランダム", ["毎回変える", "固定seed"], index=0, key="v190_seed_mode")
        seed_val = int(c4.number_input("seed", 0, 999999, 190, 1, key="v190_seed_val"))

        fit_options = ["自然トリミング（縁なし・推奨）"]
        if globals().get("_cv2_v187") is not None and globals().get("_np_v187") is not None:
            fit_options.append("OpenCV補完風（実験・情報保持）")
        fit_options.append("旧：ぼかし背景（非推奨）")

        fit_mode = st.radio(
            "3:4化方式",
            fit_options,
            index=0,
            horizontal=True,
            key="v190_fit_mode",
            help="v188の外周伸ばしは変形が出たため廃止。基本は自然トリミングを使ってください。ChatGPT級の本物のAI補完は別途画像生成APIが必要です。",
        )
        make_base_only = st.checkbox("チラシなし3:4画像も同時に作る", value=False, key="v190_make_base_only")
        clear_flyers = st.checkbox("チラシ保存をクリアする", value=False, key="v190_clear_flyers")
        if clear_flyers:
            st.session_state["v187_flyer_store"] = []
            st.session_state["v186_flyer_store"] = []
            flyer_store = []
            st.info("チラシ保存をクリアしました。新しくアップロードしてください。")

        st.info("v190では、変形する外周伸ばしを使いません。白フチ/黒フチを作らず、まずは安全な3:4トリミングで出します。")

    flyers, stored_errors = _v186_store_to_images(st.session_state.get("v187_flyer_store", []) or st.session_state.get("v186_flyer_store", []) or [])
    if stored_errors:
        with st.expander("保存済みチラシ診断", expanded=True):
            for e in stored_errors:
                st.error(e)

    run = st.button("3:4整形・チラシ合成を生成（v190）", type="primary", use_container_width=True, key="v190_run")

    if run:
        flyer_store, upload_errors = _v186_update_flyer_store(st.session_state.get("v190_flyer_uploads", []) or [])
        flyers, stored_errors = _v186_store_to_images(flyer_store)
        if not flyers and not make_base_only:
            st.warning("チラシ画像を認識できていません。上の表示が『チラシ画像を認識しました』になっているか確認してください。チラシなしで3:4だけ作る場合は『チラシなし3:4画像も同時に作る』にチェックしてください。")
            with st.expander("v190 チラシ診断", expanded=True):
                st.write("アップロード欄の件数:", len(st.session_state.get("v190_flyer_uploads", []) or []))
                st.write("保存済みチラシ件数:", len(flyer_store or []))
                st.write("画像として開けた件数:", len(flyers or []))
                st.write("アップロードエラー:", upload_errors)
                st.write("保存済みエラー:", stored_errors)
            return

        rng = random.Random(seed_val if seed_mode == "固定seed" else int(time.time() * 1000) % 100000000)
        outputs: List[Dict[str, Any]] = []
        progress = st.progress(0.0, text="3:4整形・合成中...")
        target_items = items[:max_items]
        for idx, item in enumerate(target_items, start=1):
            progress.progress((idx - 1) / max(1, len(target_items)), text=f"{idx}/{len(target_items)} {item['name']} を処理中...")
            base_src = _v185_fetch_image(item["image_url"])
            if base_src is None:
                continue
            base_34 = _v185_crop_or_expand_to_3x4(base_src, out_w=out_w, mode=fit_mode)

            if make_base_only:
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_3x4.png"
                outputs.append({
                    **item,
                    "filename": filename,
                    "png": _v185_image_to_png_bytes(base_34),
                    "flyer_index": "none",
                    "placement": "3x4_only",
                })

            if flyers:
                flyer_i = rng.randrange(len(flyers))
                comp, place = _v185_composite_flyer(base_34, flyers[flyer_i], rng, position_mode="ランダム下側")
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_flyer.png"
                outputs.append({
                    **item,
                    "filename": filename,
                    "png": _v185_image_to_png_bytes(comp),
                    "flyer_index": flyer_i + 1,
                    "placement": str(place),
                })
        progress.progress(1.0, text="生成完了")
        st.session_state["v185_outputs"] = outputs

    outputs = st.session_state.get("v185_outputs", []) or []
    if outputs:
        st.success(f"生成完了：{len(outputs)}枚")
        zip_bytes = _v185_build_zip(outputs)
        st.download_button(
            "3:4・チラシ合成画像ZIPをダウンロード",
            data=zip_bytes,
            file_name="v190_3x4_flyer_composite_images.zip",
            mime="application/zip",
            use_container_width=True,
            key="v190_zip_download",
        )
        with st.expander("生成画像プレビュー", expanded=True):
            preview = outputs[:12]
            cols = st.columns(3)
            for i, item in enumerate(preview):
                with cols[i % 3]:
                    st.image(item["png"], caption=f"{item.get('name','')}\n{item.get('address','')}", use_container_width=True)
                    st.caption(item.get("filename", ""))
        if len(outputs) > 12:
            st.caption(f"プレビューは先頭12枚のみ表示しています。全{len(outputs)}枚はZIPに入っています。")




# ==================================================
# v191 OVERRIDE: 看板保護 + ソフト外周補完風3:4
# 目的:
# - v190の単純3:4トリミングで看板文字が切れる問題を止める。
# - 基本は「看板保護」を優先し、無理にcropせず、必要時は
#   元画像全体を残したままソフト背景補完風で3:4化する。
# - 白フチ/黒フチ/硬い額縁感を避けるため、背景と前景をフェザー合成する。
# - チラシ合成はv190を維持する。
# 注意:
# - これはローカルPillow/OpenCVでできる範囲の補完風処理であり、
#   本物の生成AIアウトペイントではない。
# ==================================================

try:
    from PIL import ImageDraw as _ImageDraw_v191
except Exception:
    _ImageDraw_v191 = None


def _v191_target_size(out_w: int) -> Tuple[int, int]:
    out_w = int(out_w or 900)
    if out_w < 360:
        out_w = 360
    return out_w, int(round(out_w * 4 / 3))


def _v191_clamp(v: int, lo: int, hi: int) -> int:
    return max(lo, min(hi, int(v)))


def _v191_pad_box(box: Tuple[int, int, int, int], w: int, h: int, pad_x: int, pad_y: int) -> Tuple[int, int, int, int]:
    x1, y1, x2, y2 = box
    x1 = _v191_clamp(x1 - pad_x, 0, w)
    y1 = _v191_clamp(y1 - pad_y, 0, h)
    x2 = _v191_clamp(x2 + pad_x, 0, w)
    y2 = _v191_clamp(y2 + pad_y, 0, h)
    if x2 <= x1:
        x1, x2 = 0, w
    if y2 <= y1:
        y1, y2 = 0, h
    return x1, y1, x2, y2


def _v191_detect_protected_box(img) -> Tuple[int, int, int, int]:
    """看板/文字を切りにくくするための保護領域を推定する。
    OpenCVがあれば輪郭・文字っぽい密集領域を拾い、無ければ中央下寄りの安全箱を返す。
    """
    w, h = img.size
    # fallback: 看板は中央〜下寄りに出やすいので、やや広めに守る
    fallback = (
        int(w * 0.08),
        int(h * 0.16),
        int(w * 0.92),
        int(h * 0.88),
    )

    cv2 = globals().get('_cv2_v187')
    np = globals().get('_np_v187')
    if cv2 is None or np is None:
        return fallback

    try:
        rgb = img.convert('RGB')
        arr = np.array(rgb)
        gray = cv2.cvtColor(arr, cv2.COLOR_RGB2GRAY)

        # 軽い平滑化後にエッジ取得
        blur = cv2.GaussianBlur(gray, (5, 5), 0)
        edge = cv2.Canny(blur, 60, 160)
        kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (7, 7))
        edge = cv2.dilate(edge, kernel, iterations=2)
        edge = cv2.morphologyEx(edge, cv2.MORPH_CLOSE, kernel, iterations=1)

        # 画面上部を少し弱める（空や余白対策）。ただし完全無視はしない。
        mask = np.zeros_like(edge)
        x1m, x2m = int(w * 0.04), int(w * 0.96)
        y1m, y2m = int(h * 0.06), int(h * 0.94)
        mask[y1m:y2m, x1m:x2m] = 255
        edge = cv2.bitwise_and(edge, mask)

        contours, _ = cv2.findContours(edge, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
        candidates: List[Tuple[float, Tuple[int, int, int, int]]] = []
        img_area = float(max(1, w * h))
        for c in contours:
            x, y, ww, hh = cv2.boundingRect(c)
            area = ww * hh
            if area < img_area * 0.010 or area > img_area * 0.82:
                continue
            ar = ww / max(1.0, float(hh))
            if ar < 0.35 or ar > 9.5:
                continue
            cx = x + ww / 2.0
            cy = y + hh / 2.0
            # 中央寄り + 下寄りをやや優遇。面積も大事。
            center_bonus = 1.0 - min(1.0, abs(cx - w / 2.0) / (w / 2.0)) * 0.45
            lower_bonus = 1.0 + max(0.0, (cy / max(1.0, h)) - 0.28) * 0.55
            score = area * center_bonus * lower_bonus
            candidates.append((score, (x, y, x + ww, y + hh)))

        if not candidates:
            return fallback

        candidates.sort(key=lambda x: x[0], reverse=True)
        top = candidates[:5]
        xs = [b[0] for _, b in top]
        ys = [b[1] for _, b in top]
        xe = [b[2] for _, b in top]
        ye = [b[3] for _, b in top]
        box = (min(xs), min(ys), max(xe), max(ye))
        box = _v191_pad_box(box, w, h, int(w * 0.06), int(h * 0.06))

        # 保護箱が巨大すぎたらfallbackへ寄せる
        bw = box[2] - box[0]
        bh = box[3] - box[1]
        if bw > w * 0.96 or bh > h * 0.96:
            return fallback
        return box
    except Exception:
        return fallback


def _v191_try_sign_safe_crop(img, out_w: int = 900):
    """看板保護箱を完全に含む3:4 cropを試す。
    成功時は (cropped_img, meta)。厳しすぎる場合は None を返す。
    """
    if _Image_v185 is None:
        return None
    img = img.convert('RGBA')
    iw, ih = img.size
    if iw <= 1 or ih <= 1:
        return None

    target_ratio = 3.0 / 4.0
    out_w, out_h = _v191_target_size(out_w)
    bx1, by1, bx2, by2 = _v191_detect_protected_box(img)
    bw = bx2 - bx1
    bh = by2 - by1

    # 元が十分近いならそのままfitでもほぼ問題なし
    ratio = iw / max(1.0, ih)
    if abs(ratio - target_ratio) < 0.015:
        return _ImageOps_v185.fit(img, (out_w, out_h), method=_Image_v185.Resampling.LANCZOS, centering=(0.5, 0.5)).convert('RGBA'), {
            'mode': 'near_native', 'box': (bx1, by1, bx2, by2)
        }

    if ratio > target_ratio:
        crop_h = ih
        crop_w = int(round(crop_h * target_ratio))
        # 看板保護箱が広すぎるならcrop不適
        if bw > crop_w * 0.90:
            return None
        left_min = max(0, bx2 - crop_w)
        left_max = min(bx1, iw - crop_w)
        if left_min > left_max:
            return None
        left_pref = int(round((bx1 + bx2 - crop_w) / 2.0))
        left = _v191_clamp(left_pref, left_min, left_max)
        crop = (left, 0, left + crop_w, ih)
        # 保護箱が左右端に近すぎる場合は不自然なので補完へ回す
        margin_l = bx1 - crop[0]
        margin_r = crop[2] - bx2
        if min(margin_l, margin_r) < max(8, int(iw * 0.015)):
            return None
    else:
        crop_w = iw
        crop_h = int(round(crop_w / target_ratio))
        if bh > crop_h * 0.90:
            return None
        top_min = max(0, by2 - crop_h)
        top_max = min(by1, ih - crop_h)
        if top_min > top_max:
            return None
        top_pref = int(round((by1 + by2 - crop_h) / 2.0))
        top = _v191_clamp(top_pref, top_min, top_max)
        crop = (0, top, iw, top + crop_h)
        margin_t = by1 - crop[1]
        margin_b = crop[3] - by2
        if min(margin_t, margin_b) < max(8, int(ih * 0.015)):
            return None

    cropped = img.crop(crop)
    out = cropped.resize((out_w, out_h), _Image_v185.Resampling.LANCZOS).convert('RGBA')
    meta = {'mode': 'sign_safe_crop', 'crop': crop, 'box': (bx1, by1, bx2, by2)}
    return out, meta


def _v191_make_soft_feather_mask(size: Tuple[int, int], feather: int = 42):
    if _Image_v185 is None:
        return None
    w, h = size
    feather = int(max(12, min(feather, min(w, h) // 4)))
    mask = _Image_v185.new('L', (w, h), 0)
    if _ImageDraw_v191 is None:
        return mask
    draw = _ImageDraw_v191.Draw(mask)
    draw.rectangle((feather, feather, max(feather + 1, w - feather - 1), max(feather + 1, h - feather - 1)), fill=255)
    if _ImageFilter_v185 is not None:
        mask = mask.filter(_ImageFilter_v185.GaussianBlur(radius=feather))
    return mask


def _v191_soft_outpaint_blend_3x4(img, out_w: int = 900):
    """元画像は切らず、ソフト背景補完風に3:4化する。
    背景はcover+blur、前景はfull fit + フェザー合成。
    """
    if _Image_v185 is None:
        return img
    img = img.convert('RGBA')
    out_w, out_h = _v191_target_size(out_w)

    # 背景: 画面を埋める cover を少しぼかす
    bg = _ImageOps_v185.fit(img, (out_w, out_h), method=_Image_v185.Resampling.LANCZOS, centering=(0.5, 0.5)).convert('RGBA')
    try:
        bg = bg.filter(_ImageFilter_v185.GaussianBlur(radius=max(14, out_w // 28)))
        bg = _ImageEnhance_v185.Contrast(bg).enhance(0.93)
        bg = _ImageEnhance_v185.Brightness(bg).enhance(0.98)
    except Exception:
        pass

    # 前景: 元画像全体をできるだけ大きく残す
    iw, ih = img.size
    scale = min((out_w * 0.985) / max(1, iw), (out_h * 0.985) / max(1, ih))
    nw, nh = max(1, int(iw * scale)), max(1, int(ih * scale))
    fg = img.resize((nw, nh), _Image_v185.Resampling.LANCZOS).convert('RGBA')
    x = (out_w - nw) // 2
    y = (out_h - nh) // 2

    mask = _v191_make_soft_feather_mask((nw, nh), feather=max(18, min(nw, nh) // 18))
    canvas = bg.copy()
    try:
        if mask is not None:
            layer = _Image_v185.new('RGBA', (out_w, out_h), (0, 0, 0, 0))
            layer.paste(fg, (x, y))
            alpha_layer = _Image_v185.new('L', (out_w, out_h), 0)
            alpha_layer.paste(mask, (x, y))
            canvas = _Image_v185.composite(layer, canvas, alpha_layer)
        else:
            canvas.alpha_composite(fg, (x, y))
    except Exception:
        canvas.alpha_composite(fg, (x, y))
    return canvas.convert('RGBA')


def _v191_sign_protect_or_outpaint_3x4(img, out_w: int = 900):
    """優先順位:
    1) 看板保護cropで無理なく入るならcrop
    2) きつい/切れそうならソフト外周補完風へ
    """
    tried = _v191_try_sign_safe_crop(img, out_w)
    if tried is not None:
        return tried[0]
    return _v191_soft_outpaint_blend_3x4(img, out_w)


def _v185_crop_or_expand_to_3x4(img, out_w: int = 900, mode: str = '看板保護＋外周補完風3:4（推奨）'):  # type: ignore[override]
    """v191: 単純トリミングではなく、看板が切れないことを優先する。"""
    if _Image_v185 is None:
        return img
    mode = str(mode or '')
    if 'ソフト背景' in mode or '全景' in mode:
        return _v191_soft_outpaint_blend_3x4(img, out_w)
    if 'トリミング' in mode or '看板保護crop' in mode:
        tried = _v191_try_sign_safe_crop(img, out_w)
        if tried is not None:
            return tried[0]
        return _v191_soft_outpaint_blend_3x4(img, out_w)
    return _v191_sign_protect_or_outpaint_3x4(img, out_w)


def render_v185_3x4_flyer_composite() -> None:  # type: ignore[override]
    st.divider()
    st.subheader('3:4整形・チラシランダム合成 v191（看板保護＋外周補完風）')
    st.caption('看板文字を切らないことを最優先にし、まず看板保護cropを試し、きつい場合はソフト外周補完風で3:4化します。')

    if _Image_v185 is None or _io_v185 is None or _zipfile_v185 is None:
        st.error('Pillow が必要です。PowerShellで `pip install pillow` を実行してください。')
        return

    items = _v185_current_sign_items()
    if not items:
        st.info('まず上の v184 でマンション名看板画像を取得してください。画像ありの結果があると、ここで3:4化・チラシ合成できます。')
        return

    st.success(f'合成対象：マンション名看板画像 {len(items)}件')

    with st.expander('チラシ画像アップロード / 合成設定', expanded=True):
        uploaded_files = st.file_uploader(
            'チラシだけの画像をアップロード（最大10枚程度）',
            type=['png', 'jpg', 'jpeg', 'webp', 'gif'],
            accept_multiple_files=True,
            key='v191_flyer_uploads',
        )
        flyer_store, upload_errors = _v186_update_flyer_store(uploaded_files)

        if flyer_store:
            names = [str(x.get('name', 'flyer')) for x in flyer_store]
            st.success(f"チラシ画像を認識しました：{len(flyer_store)}枚（{', '.join(names[:5])}{' ほか' if len(names) > 5 else ''}）")
            try:
                preview_imgs, _ = _v186_store_to_images(flyer_store[:3])
                if preview_imgs:
                    cols_prev = st.columns(min(3, len(preview_imgs)))
                    for pi, im in enumerate(preview_imgs):
                        with cols_prev[pi % len(cols_prev)]:
                            st.image(im, caption=names[pi] if pi < len(names) else 'チラシ', use_container_width=True)
            except Exception:
                pass
        else:
            st.warning('チラシ画像はまだ認識されていません。アップロード後にこの表示が「認識しました」へ変わるか確認してください。')

        if upload_errors:
            with st.expander('チラシ読み込み診断', expanded=True):
                for e in upload_errors:
                    st.error(e)

        c1, c2, c3, c4 = st.columns(4)
        out_w = int(c1.number_input('出力横幅', 360, 1800, 900, 60, key='v191_out_w'))
        max_items = int(c2.number_input('生成上限', 1, 200, min(60, len(items)), 1, key='v191_max_items'))
        seed_mode = c3.selectbox('ランダム', ['毎回変える', '固定seed'], index=0, key='v191_seed_mode')
        seed_val = int(c4.number_input('seed', 0, 999999, 191, 1, key='v191_seed_val'))

        fit_options = [
            '看板保護＋外周補完風3:4（推奨）',
            '看板保護トリミング（看板優先）',
            'ソフト背景補完（全景優先）',
        ]
        fit_mode = st.radio(
            '3:4化方式',
            fit_options,
            index=0,
            horizontal=True,
            key='v191_fit_mode',
            help='推奨は「看板保護＋外周補完風3:4」です。単純cropで看板が切れそうな場合は、自動で全景保持＋ソフト背景補完へ回します。',
        )
        make_base_only = st.checkbox('チラシなし3:4画像も同時に作る', value=False, key='v191_make_base_only')
        clear_flyers = st.checkbox('チラシ保存をクリアする', value=False, key='v191_clear_flyers')
        if clear_flyers:
            st.session_state['v187_flyer_store'] = []
            st.session_state['v186_flyer_store'] = []
            flyer_store = []
            st.info('チラシ保存をクリアしました。新しくアップロードしてください。')

        st.info('v191では、単純3:4トリミングをやめ、看板が切れそうな画像は自動で外周補完風へ回します。')

    flyers, stored_errors = _v186_store_to_images(st.session_state.get('v187_flyer_store', []) or st.session_state.get('v186_flyer_store', []) or [])
    if stored_errors:
        with st.expander('保存済みチラシ診断', expanded=True):
            for e in stored_errors:
                st.error(e)

    run = st.button('3:4整形・チラシ合成を生成（v191）', type='primary', use_container_width=True, key='v191_run')

    if run:
        flyer_store, upload_errors = _v186_update_flyer_store(st.session_state.get('v191_flyer_uploads', []) or [])
        flyers, stored_errors = _v186_store_to_images(flyer_store)
        if not flyers and not make_base_only:
            st.warning('チラシ画像を認識できていません。上の表示が「チラシ画像を認識しました」になっているか確認してください。チラシなしで3:4だけ作る場合は「チラシなし3:4画像も同時に作る」にチェックしてください。')
            with st.expander('v191 チラシ診断', expanded=True):
                st.write('アップロード欄の件数:', len(st.session_state.get('v191_flyer_uploads', []) or []))
                st.write('保存済みチラシ件数:', len(flyer_store or []))
                st.write('画像として開けた件数:', len(flyers or []))
                st.write('アップロードエラー:', upload_errors)
                st.write('保存済みエラー:', stored_errors)
            return

        rng = random.Random(seed_val if seed_mode == '固定seed' else int(time.time() * 1000) % 100000000)
        outputs: List[Dict[str, Any]] = []
        progress = st.progress(0.0, text='3:4整形・合成中...')
        target_items = items[:max_items]
        for idx, item in enumerate(target_items, start=1):
            progress.progress((idx - 1) / max(1, len(target_items)), text=f"{idx}/{len(target_items)} {item['name']} を処理中...")
            base_src = _v185_fetch_image(item['image_url'])
            if base_src is None:
                continue
            base_34 = _v185_crop_or_expand_to_3x4(base_src, out_w=out_w, mode=fit_mode)

            if make_base_only:
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_3x4.png"
                outputs.append({
                    **item,
                    'filename': filename,
                    'png': _v185_image_to_png_bytes(base_34),
                    'flyer_index': 'none',
                    'placement': '3x4_only',
                })

            if flyers:
                flyer_i = rng.randrange(len(flyers))
                comp, place = _v185_composite_flyer(base_34, flyers[flyer_i], rng, position_mode='ランダム下側')
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_flyer.png"
                outputs.append({
                    **item,
                    'filename': filename,
                    'png': _v185_image_to_png_bytes(comp),
                    'flyer_index': flyer_i + 1,
                    'placement': str(place),
                })
        progress.progress(1.0, text='生成完了')
        st.session_state['v191_outputs'] = outputs

    outputs = st.session_state.get('v191_outputs', []) or []
    if outputs:
        st.success(f'生成完了：{len(outputs)}枚')
        zip_bytes = _v185_build_zip(outputs)
        st.download_button(
            '3:4・チラシ合成画像ZIPをダウンロード',
            data=zip_bytes,
            file_name='v191_3x4_flyer_composite_images.zip',
            mime='application/zip',
            use_container_width=True,
            key='v191_zip_download',
        )
        with st.expander('生成画像プレビュー', expanded=True):
            preview = outputs[:12]
            cols = st.columns(3)
            for i, item in enumerate(preview):
                with cols[i % 3]:
                    st.image(item['png'], caption=f"{item.get('name','')}\n{item.get('address','')}", use_container_width=True)
                    st.caption(item.get('filename', ''))
        if len(outputs) > 12:
            st.caption(f'プレビューは先頭12枚のみ表示しています。全{len(outputs)}枚はZIPに入っています。')


# ==================================================
# v191 FINAL ENTRYPOINT
# すべてのoverride後に main() を呼ぶ。
# ==================================================
# =========================================================
# v192 PATCH: 縁なし・看板見切れ防止・外周補完風3:4
# 貼り付け場所:
#   このブロックをファイル最下部の
#   if __name__ == '__main__':
#   の直前にそのまま追記
# =========================================================

def _v192_target_size(out_w: int) -> Tuple[int, int]:
    out_w = int(out_w or 900)
    if out_w < 360:
        out_w = 360
    return out_w, int(round(out_w * 4 / 3))


def _v192_soft_edge_mask(size: Tuple[int, int], fade_x: int = 0, fade_y: int = 0):
    """
    前景を背景へ自然につなぐためのマスク。
    landscape時は上下だけ、portrait時は左右だけをぼかす。
    """
    if _Image_v185 is None:
        return None
    w, h = size
    mask = _Image_v185.new("L", (w, h), 255)

    if _ImageDraw_v191 is None or _ImageFilter_v185 is None:
        return mask

    fade_x = max(0, int(fade_x))
    fade_y = max(0, int(fade_y))

    if fade_x <= 0 and fade_y <= 0:
        return mask

    m = _Image_v185.new("L", (w, h), 0)
    draw = _ImageDraw_v191.Draw(m)

    x1 = fade_x
    y1 = fade_y
    x2 = max(x1 + 1, w - fade_x - 1)
    y2 = max(y1 + 1, h - fade_y - 1)

    draw.rectangle((x1, y1, x2, y2), fill=255)

    blur_r = max(6, int(max(fade_x, fade_y) * 0.8))
    m = m.filter(_ImageFilter_v185.GaussianBlur(radius=blur_r))
    return m


def _v192_make_fill_from_strip(strip, out_size: Tuple[int, int], blur_radius: int = 18):
    """
    端の細い帯から、足りない外周を埋める背景を作る。
    枠ではなく“続き”に見せる用。
    """
    if _Image_v185 is None:
        return strip
    ow, oh = out_size
    fill = strip.resize((ow, oh), _Image_v185.Resampling.LANCZOS).convert("RGBA")
    try:
        if _ImageFilter_v185 is not None:
            fill = fill.filter(_ImageFilter_v185.GaussianBlur(radius=max(8, int(blur_radius))))
        if _ImageEnhance_v185 is not None:
            fill = _ImageEnhance_v185.Contrast(fill).enhance(0.96)
            fill = _ImageEnhance_v185.Brightness(fill).enhance(0.99)
    except Exception:
        pass
    return fill


def _v192_compose_with_alpha(bg, fg, x: int, y: int, mask):
    """
    fgをmask付きでbgへ自然合成する。
    """
    if _Image_v185 is None:
        return bg
    out = bg.copy().convert("RGBA")
    layer = _Image_v185.new("RGBA", out.size, (0, 0, 0, 0))
    layer.paste(fg, (x, y))

    if mask is None:
        out.alpha_composite(layer)
        return out

    alpha_canvas = _Image_v185.new("L", out.size, 0)
    alpha_canvas.paste(mask, (x, y))
    out = _Image_v185.composite(layer, out, alpha_canvas)
    return out


def _v192_no_frame_outpaint_3x4(img, out_w: int = 900):
    """
    今回の本命。
    - 基本は元画像を切らずに3:4化
    - landscape画像なら上下を補完
    - portrait画像なら左右を補完
    - 額縁っぽくならないよう、補完側と前景境界をフェードさせる
    """
    if _Image_v185 is None:
        return img

    img = img.convert("RGBA")
    out_w, out_h = _v192_target_size(out_w)
    iw, ih = img.size
    if iw <= 1 or ih <= 1:
        return img.resize((out_w, out_h), _Image_v185.Resampling.LANCZOS)

    target_ratio = out_w / max(1.0, out_h)
    src_ratio = iw / max(1.0, ih)

    # ほぼ3:4ならそのまま自然fit
    if abs(src_ratio - target_ratio) < 0.012:
        return _ImageOps_v185.fit(
            img,
            (out_w, out_h),
            method=_Image_v185.Resampling.LANCZOS,
            centering=(0.5, 0.5),
        ).convert("RGBA")

    # 横長画像: 横幅いっぱいに合わせ、上下だけ補完
    if src_ratio >= target_ratio:
        nw = out_w
        nh = max(1, int(round(ih * (out_w / max(1.0, iw)))))
        fg = img.resize((nw, nh), _Image_v185.Resampling.LANCZOS).convert("RGBA")

        top_gap = max(0, (out_h - nh) // 2)
        bottom_gap = max(0, out_h - nh - top_gap)

        canvas = _Image_v185.new("RGBA", (out_w, out_h), (0, 0, 0, 255))
        strip_h = max(10, min(48, nh // 7))

        if top_gap > 0:
            top_strip = fg.crop((0, 0, nw, strip_h))
            top_fill = _v192_make_fill_from_strip(
                top_strip,
                (out_w, top_gap),
                blur_radius=max(10, top_gap // 6),
            )
            canvas.paste(top_fill, (0, 0))

        if bottom_gap > 0:
            bottom_strip = fg.crop((0, max(0, nh - strip_h), nw, nh))
            bottom_fill = _v192_make_fill_from_strip(
                bottom_strip,
                (out_w, bottom_gap),
                blur_radius=max(10, bottom_gap // 6),
            )
            canvas.paste(bottom_fill, (0, top_gap + nh))

        fade_y = max(10, min(34, max(top_gap, bottom_gap) // 2 if max(top_gap, bottom_gap) > 0 else 0))
        mask = _v192_soft_edge_mask((nw, nh), fade_x=0, fade_y=fade_y)
        canvas = _v192_compose_with_alpha(canvas, fg, 0, top_gap, mask)
        return canvas.convert("RGBA")

    # 縦長画像: 高さいっぱいに合わせ、左右だけ補完
    nh = out_h
    nw = max(1, int(round(iw * (out_h / max(1.0, ih)))))
    fg = img.resize((nw, nh), _Image_v185.Resampling.LANCZOS).convert("RGBA")

    left_gap = max(0, (out_w - nw) // 2)
    right_gap = max(0, out_w - nw - left_gap)

    canvas = _Image_v185.new("RGBA", (out_w, out_h), (0, 0, 0, 255))
    strip_w = max(10, min(48, nw // 7))

    if left_gap > 0:
        left_strip = fg.crop((0, 0, strip_w, nh))
        left_fill = _v192_make_fill_from_strip(
            left_strip,
            (left_gap, out_h),
            blur_radius=max(10, left_gap // 6),
        )
        canvas.paste(left_fill, (0, 0))

    if right_gap > 0:
        right_strip = fg.crop((max(0, nw - strip_w), 0, nw, nh))
        right_fill = _v192_make_fill_from_strip(
            right_strip,
            (right_gap, out_h),
            blur_radius=max(10, right_gap // 6),
        )
        canvas.paste(right_fill, (left_gap + nw, 0))

    fade_x = max(10, min(34, max(left_gap, right_gap) // 2 if max(left_gap, right_gap) > 0 else 0))
    mask = _v192_soft_edge_mask((nw, nh), fade_x=fade_x, fade_y=0)
    canvas = _v192_compose_with_alpha(canvas, fg, left_gap, 0, mask)
    return canvas.convert("RGBA")


# v191のソフト背景補完を、額縁っぽくならない方式へ差し替え
def _v191_soft_outpaint_blend_3x4(img, out_w: int = 900):  # type: ignore[override]
    return _v192_no_frame_outpaint_3x4(img, out_w)


# デフォルトはもうcrop優先にしない
def _v191_sign_protect_or_outpaint_3x4(img, out_w: int = 900):  # type: ignore[override]
    return _v192_no_frame_outpaint_3x4(img, out_w)


def _v185_crop_or_expand_to_3x4(img, out_w: int = 900, mode: str = '看板保護＋外周補完風3:4（推奨）'):  # type: ignore[override]
    """
    v192:
    - 既定は「切らない」外周補完風
    - トリミング指定時だけ看板保護cropを試す
    - cropが危ない時は自動で外周補完風へ戻す
    """
    if _Image_v185 is None:
        return img

    mode = str(mode or '')

    if 'トリミング' in mode or 'crop' in mode.lower():
        tried = _v191_try_sign_safe_crop(img, out_w)
        if tried is not None:
            return tried[0]
        return _v192_no_frame_outpaint_3x4(img, out_w)

    return _v192_no_frame_outpaint_3x4(img, out_w)


# 画面文言だけv192に更新
def render_v185_3x4_flyer_composite() -> None:  # type: ignore[override]
    st.divider()
    st.subheader('3:4整形・チラシランダム合成 v192（縁なし・看板保護強化）')
    st.caption('看板文字を切らないことを最優先にし、デフォルトは単純cropではなく、縁なし外周補完風3:4で処理します。')

    if _Image_v185 is None or _io_v185 is None or _zipfile_v185 is None:
        st.error('Pillow が必要です。PowerShellで `pip install pillow` を実行してください。')
        return

    items = _v185_current_sign_items()
    if not items:
        st.info('まず上の v184 でマンション名看板画像を取得してください。画像ありの結果があると、ここで3:4化・チラシ合成できます。')
        return

    st.success(f'合成対象：マンション名看板画像 {len(items)}件')

    with st.expander('チラシ画像アップロード / 合成設定', expanded=True):
        uploaded_files = st.file_uploader(
            'チラシだけの画像をアップロード（最大10枚程度）',
            type=['png', 'jpg', 'jpeg', 'webp', 'gif'],
            accept_multiple_files=True,
            key='v191_flyer_uploads',
        )
        flyer_store, upload_errors = _v186_update_flyer_store(uploaded_files)

        if flyer_store:
            names = [str(x.get('name', 'flyer')) for x in flyer_store]
            st.success(f"チラシ画像を認識しました：{len(flyer_store)}枚（{', '.join(names[:5])}{' ほか' if len(names) > 5 else ''}）")
            try:
                preview_imgs, _ = _v186_store_to_images(flyer_store[:3])
                if preview_imgs:
                    cols_prev = st.columns(min(3, len(preview_imgs)))
                    for pi, im in enumerate(preview_imgs):
                        with cols_prev[pi % len(cols_prev)]:
                            st.image(im, caption=names[pi] if pi < len(names) else 'チラシ', use_container_width=True)
            except Exception:
                pass
        else:
            st.warning('チラシ画像はまだ認識されていません。アップロード後にこの表示が「認識しました」へ変わるか確認してください。')

        if upload_errors:
            with st.expander('チラシ読み込み診断', expanded=True):
                for e in upload_errors:
                    st.error(e)

        c1, c2, c3, c4 = st.columns(4)
        out_w = int(c1.number_input('出力横幅', 360, 1800, 900, 60, key='v191_out_w'))
        max_items = int(c2.number_input('生成上限', 1, 200, min(60, len(items)), 1, key='v191_max_items'))
        seed_mode = c3.selectbox('ランダム', ['毎回変える', '固定seed'], index=0, key='v191_seed_mode')
        seed_val = int(c4.number_input('seed', 0, 999999, 192, 1, key='v191_seed_val'))

        fit_options = [
            '看板保護＋外周補完風3:4（推奨）',
            '看板保護トリミング（任意）',
        ]
        fit_mode = st.radio(
            '3:4化方式',
            fit_options,
            index=0,
            horizontal=True,
            key='v191_fit_mode',
            help='推奨は「看板保護＋外周補完風3:4」です。デフォルトは切らずに外周補完風で3:4化します。',
        )
        make_base_only = st.checkbox('チラシなし3:4画像も同時に作る', value=False, key='v191_make_base_only')
        clear_flyers = st.checkbox('チラシ保存をクリアする', value=False, key='v191_clear_flyers')
        if clear_flyers:
            st.session_state['v187_flyer_store'] = []
            st.session_state['v186_flyer_store'] = []
            flyer_store = []
            st.info('チラシ保存をクリアしました。新しくアップロードしてください。')

        st.info('v192では、既定で単純3:4トリミングを使いません。看板の見切れ防止を優先し、外周補完風で3:4化します。')

    flyers, stored_errors = _v186_store_to_images(st.session_state.get('v187_flyer_store', []) or st.session_state.get('v186_flyer_store', []) or [])
    if stored_errors:
        with st.expander('保存済みチラシ診断', expanded=True):
            for e in stored_errors:
                st.error(e)

    run = st.button('3:4整形・チラシ合成を生成（v192）', type='primary', use_container_width=True, key='v191_run')

    if run:
        flyer_store, upload_errors = _v186_update_flyer_store(st.session_state.get('v191_flyer_uploads', []) or [])
        flyers, stored_errors = _v186_store_to_images(flyer_store)
        if not flyers and not make_base_only:
            st.warning('チラシ画像を認識できていません。上の表示が「チラシ画像を認識しました」になっているか確認してください。チラシなしで3:4だけ作る場合は「チラシなし3:4画像も同時に作る」にチェックしてください。')
            with st.expander('v192 チラシ診断', expanded=True):
                st.write('アップロード欄の件数:', len(st.session_state.get('v191_flyer_uploads', []) or []))
                st.write('保存済みチラシ件数:', len(flyer_store or []))
                st.write('画像として開けた件数:', len(flyers or []))
                st.write('アップロードエラー:', upload_errors)
                st.write('保存済みエラー:', stored_errors)
            return

        rng = random.Random(seed_val if seed_mode == '固定seed' else int(time.time() * 1000) % 100000000)
        outputs: List[Dict[str, Any]] = []
        progress = st.progress(0.0, text='3:4整形・合成中...')
        target_items = items[:max_items]

        for idx, item in enumerate(target_items, start=1):
            progress.progress((idx - 1) / max(1, len(target_items)), text=f"{idx}/{len(target_items)} {item['name']} を処理中...")
            base_src = _v185_fetch_image(item['image_url'])
            if base_src is None:
                continue

            base_34 = _v185_crop_or_expand_to_3x4(base_src, out_w=out_w, mode=fit_mode)

            if make_base_only:
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_3x4.png"
                outputs.append({
                    **item,
                    'filename': filename,
                    'png': _v185_image_to_png_bytes(base_34),
                    'flyer_index': 'none',
                    'placement': '3x4_only',
                })

            if flyers:
                flyer_i = rng.randrange(len(flyers))
                comp, place = _v185_composite_flyer(base_34, flyers[flyer_i], rng, position_mode='ランダム下側')
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_flyer.png"
                outputs.append({
                    **item,
                    'filename': filename,
                    'png': _v185_image_to_png_bytes(comp),
                    'flyer_index': flyer_i + 1,
                    'placement': str(place),
                })

        progress.progress(1.0, text='生成完了')
        st.session_state['v191_outputs'] = outputs

    outputs = st.session_state.get('v191_outputs', []) or []
    if outputs:
        st.success(f'生成完了：{len(outputs)}枚')
        zip_bytes = _v185_build_zip(outputs)
        st.download_button(
            '3:4・チラシ合成画像ZIPをダウンロード',
            data=zip_bytes,
            file_name='v192_3x4_flyer_composite_images.zip',
            mime='application/zip',
            use_container_width=True,
            key='v191_zip_download',
        )
        with st.expander('生成画像プレビュー', expanded=True):
            preview = outputs[:12]
            cols = st.columns(3)
            for i, item in enumerate(preview):
                with cols[i % 3]:
                    st.image(item['png'], caption=f"{item.get('name','')}\n{item.get('address','')}", use_container_width=True)
                    st.caption(item.get('filename', ''))
        if len(outputs) > 12:
            st.caption(f'プレビューは先頭12枚のみ表示しています。全{len(outputs)}枚はZIPに入っています。')

# =========================================================
# v192 PATCH END
# =========================================================

# =========================================================
# v193 PATCH: AI風外周補完3:4（縁なし・看板見切れ防止の再修正版）
# 貼り付け場所:
#   このブロックをファイル最下部の
#   if __name__ == '__main__':
#   の直前にそのまま追記
# =========================================================

def _v193_target_size(out_w: int) -> Tuple[int, int]:
    out_w = int(out_w or 900)
    if out_w < 360:
        out_w = 360
    return out_w, int(round(out_w * 4 / 3))


def _v193_cover_background_3x4(img, out_size: Tuple[int, int]):
    """
    背景全体を3:4いっぱいに“埋める”用のベース画像。
    単なる帯追加ではなく、元画像全体をcoverで広げてぼかす。
    これで「上だけ/下だけ帯が付く」見え方を避ける。
    """
    if _Image_v185 is None:
        return img
    ow, oh = out_size
    base = img.convert('RGBA')
    bg = _ImageOps_v185.fit(
        base,
        (ow, oh),
        method=_Image_v185.Resampling.LANCZOS,
        centering=(0.5, 0.5),
    )
    try:
        if _ImageFilter_v185 is not None:
            bg = bg.filter(_ImageFilter_v185.GaussianBlur(radius=max(14, int(min(ow, oh) * 0.018))))
        if _ImageEnhance_v185 is not None:
            bg = _ImageEnhance_v185.Contrast(bg).enhance(0.94)
            bg = _ImageEnhance_v185.Brightness(bg).enhance(1.01)
    except Exception:
        pass
    return bg.convert('RGBA')


def _v193_contain_foreground(img, out_size: Tuple[int, int]):
    """
    元画像を一切切らずに前景として保持。
    看板文字が見切れないことを優先する。
    """
    if _Image_v185 is None:
        return img
    ow, oh = out_size
    fg = _ImageOps_v185.contain(
        img.convert('RGBA'),
        (ow, oh),
        method=_Image_v185.Resampling.LANCZOS,
    )
    return fg.convert('RGBA')


def _v193_soft_mask(size: Tuple[int, int], fade: int = 26):
    """
    前景の周囲を自然に溶かすマスク。
    枠線/額縁っぽさを消すため、四辺を軽くフェードする。
    """
    if _Image_v185 is None:
        return None
    w, h = size
    if w <= 2 or h <= 2:
        return _Image_v185.new('L', (max(1, w), max(1, h)), 255)

    fade = max(8, int(fade))
    m = _Image_v185.new('L', (w, h), 0)
    if _ImageDraw_v191 is None:
        return _Image_v185.new('L', (w, h), 255)
    draw = _ImageDraw_v191.Draw(m)
    inset = min(fade, max(1, w // 8), max(1, h // 8))
    draw.rectangle((inset, inset, max(inset + 1, w - inset - 1), max(inset + 1, h - inset - 1)), fill=255)
    if _ImageFilter_v185 is not None:
        m = m.filter(_ImageFilter_v185.GaussianBlur(radius=max(10, fade)))
    return m


def _v193_alpha_paste(bg, fg, x: int, y: int, mask):
    if _Image_v185 is None:
        return bg
    out = bg.copy().convert('RGBA')
    layer = _Image_v185.new('RGBA', out.size, (0, 0, 0, 0))
    layer.paste(fg, (x, y))
    if mask is None:
        out.alpha_composite(layer)
        return out
    alpha = _Image_v185.new('L', out.size, 0)
    alpha.paste(mask, (x, y))
    out = _Image_v185.composite(layer, out, alpha)
    return out


def _v193_ai_style_no_frame_3x4(img, out_w: int = 900):
    """
    v193の本命。
    - 元画像は切らない（看板見切れ防止）
    - 背景は3:4 cover + ぼかし
    - 前景はcontainで全体保持
    - 四辺フェードで“縁追加”見えを減らす
    """
    if _Image_v185 is None:
        return img

    out_w, out_h = _v193_target_size(out_w)
    base = img.convert('RGBA')
    bg = _v193_cover_background_3x4(base, (out_w, out_h))
    fg = _v193_contain_foreground(base, (out_w, out_h))

    fw, fh = fg.size
    x = max(0, (out_w - fw) // 2)
    y = max(0, (out_h - fh) // 2)

    fade = max(12, int(min(fw, fh) * 0.035))
    mask = _v193_soft_mask((fw, fh), fade=fade)
    out = _v193_alpha_paste(bg, fg, x, y, mask)
    return out.convert('RGBA')


# v193では、デフォルトの3:4化を全面的にこちらへ寄せる
def _v185_crop_or_expand_to_3x4(img, out_w: int = 900, mode: str = '看板保護＋AI風外周補完3:4（推奨）'):  # type: ignore[override]
    """
    既定は必ず v193 のAI風外周補完。
    ユーザーが明示的にトリミングを選んだ時だけ、看板保護cropを試す。
    cropで危なければ自動でv193へ戻す。
    """
    if _Image_v185 is None:
        return img

    mode = str(mode or '')
    if 'トリミング' in mode or 'crop' in mode.lower():
        tried = _v191_try_sign_safe_crop(img, out_w)
        if tried is not None:
            return tried[0]
        return _v193_ai_style_no_frame_3x4(img, out_w)

    return _v193_ai_style_no_frame_3x4(img, out_w)


def render_v185_3x4_flyer_composite() -> None:  # type: ignore[override]
    st.divider()
    st.subheader('マンション画像 → チラシ合成')
    st.caption('既定では、単純cropや帯追加を使わず、背景全体を3:4 cover + ソフトぼかしで埋め、元画像は切らずに保持します。')

    if _Image_v185 is None or _io_v185 is None or _zipfile_v185 is None:
        st.error('Pillow が必要です。PowerShellで `pip install pillow` を実行してください。')
        return

    items = _v185_current_sign_items()
    if not items:
        st.info('まず上の看板画像取得でマンション名看板画像を取得してください。画像ありの結果があると、ここで3:4化・チラシ合成できます。')
        return

    st.success(f'合成対象：マンション名看板画像 {len(items)}件')

    with st.expander('チラシ画像アップロード / 合成設定', expanded=True):
        uploaded_files = st.file_uploader(
            'チラシだけの画像をアップロード（最大10枚程度）',
            type=['png', 'jpg', 'jpeg', 'webp', 'gif'],
            accept_multiple_files=True,
            key='v191_flyer_uploads',
        )
        flyer_store, upload_errors = _v186_update_flyer_store(uploaded_files)

        if flyer_store:
            names = [str(x.get('name', 'flyer')) for x in flyer_store]
            st.success(f"チラシ画像を認識しました：{len(flyer_store)}枚（{', '.join(names[:5])}{' ほか' if len(names) > 5 else ''}）")
        else:
            st.warning('チラシ画像はまだ認識されていません。アップロード後にこの表示が「認識しました」へ変わるか確認してください。')

        if upload_errors:
            with st.expander('チラシ読み込み診断', expanded=True):
                for e in upload_errors:
                    st.error(e)

        c1, c2, c3, c4 = st.columns(4)
        out_w = int(c1.number_input('出力横幅', 360, 1800, 900, 60, key='v191_out_w'))
        max_items = int(c2.number_input('生成上限', 1, 200, min(60, len(items)), 1, key='v191_max_items'))
        seed_mode = c3.selectbox('ランダム', ['毎回変える', '固定seed'], index=0, key='v191_seed_mode')
        seed_val = int(c4.number_input('seed', 0, 999999, 193, 1, key='v191_seed_val'))

        fit_options = [
            '看板保護＋AI風外周補完3:4（推奨）',
            '看板保護トリミング（任意）',
        ]
        fit_mode = st.radio(
            '3:4化方式',
            fit_options,
            index=0,
            horizontal=True,
            key='v191_fit_mode',
            help='推奨は「看板保護＋AI風外周補完3:4」です。デフォルトでは元画像を切らずに3:4化します。',
        )
        make_base_only = st.checkbox('チラシなし3:4画像も同時に作る', value=False, key='v191_make_base_only')
        clear_flyers = st.checkbox('チラシ保存をクリアする', value=False, key='v191_clear_flyers')
        if clear_flyers:
            st.session_state['v187_flyer_store'] = []
            st.session_state['v186_flyer_store'] = []
            flyer_store = []
            st.info('チラシ保存をクリアしました。新しくアップロードしてください。')

        st.info('v193では、既定で単純な縁追加/帯追加を使いません。背景全体をcoverで埋めてから、元画像を切らずに重ねます。')

    flyers, stored_errors = _v186_store_to_images(st.session_state.get('v187_flyer_store', []) or st.session_state.get('v186_flyer_store', []) or [])
    if stored_errors:
        with st.expander('保存済みチラシ診断', expanded=True):
            for e in stored_errors:
                st.error(e)

    run = st.button('3:4整形・チラシ合成を生成（v193）', type='primary', use_container_width=True, key='v191_run')

    if run:
        flyer_store, upload_errors = _v186_update_flyer_store(st.session_state.get('v191_flyer_uploads', []) or [])
        flyers, stored_errors = _v186_store_to_images(flyer_store)
        if not flyers and not make_base_only:
            st.warning('チラシ画像を認識できていません。上の表示が「チラシ画像を認識しました」になっているか確認してください。チラシなしで3:4だけ作る場合は「チラシなし3:4画像も同時に作る」にチェックしてください。')
            with st.expander('v193 チラシ診断', expanded=True):
                st.write('アップロード欄の件数:', len(st.session_state.get('v191_flyer_uploads', []) or []))
                st.write('保存済みチラシ件数:', len(flyer_store or []))
                st.write('画像として開けた件数:', len(flyers or []))
                st.write('アップロードエラー:', upload_errors)
                st.write('保存済みエラー:', stored_errors)
            return

        rng = random.Random(seed_val if seed_mode == '固定seed' else int(time.time() * 1000) % 100000000)
        outputs: List[Dict[str, Any]] = []
        progress = st.progress(0.0, text='3:4整形・合成中...')
        target_items = items[:max_items]

        for idx, item in enumerate(target_items, start=1):
            progress.progress((idx - 1) / max(1, len(target_items)), text=f"{idx}/{len(target_items)} {item['name']} を処理中...")
            base_src = _v185_fetch_image(item['image_url'])
            if base_src is None:
                continue

            base_34 = _v185_crop_or_expand_to_3x4(base_src, out_w=out_w, mode=fit_mode)

            if make_base_only:
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_3x4.png"
                outputs.append({
                    **item,
                    'filename': filename,
                    'png': _v185_image_to_png_bytes(base_34),
                    'flyer_index': 'none',
                    'placement': '3x4_only',
                })

            if flyers:
                flyer_i = rng.randrange(len(flyers))
                comp, place = _v185_composite_flyer(base_34, flyers[flyer_i], rng, position_mode='ランダム下側')
                filename = f"{idx:03d}_{_v185_safe_filename(item['address'] or item['name'])}_flyer.png"
                outputs.append({
                    **item,
                    'filename': filename,
                    'png': _v185_image_to_png_bytes(comp),
                    'flyer_index': flyer_i + 1,
                    'placement': str(place),
                })

        progress.progress(1.0, text='生成完了')
        st.session_state['v191_outputs'] = outputs

    outputs = st.session_state.get('v191_outputs', []) or []
    if outputs:
        st.success(f'生成完了：{len(outputs)}枚')
        zip_bytes = _v185_build_zip(outputs)
        st.download_button(
            '3:4・チラシ合成画像ZIPをダウンロード',
            data=zip_bytes,
            file_name='v193_3x4_flyer_composite_images.zip',
            mime='application/zip',
            use_container_width=True,
            key='v191_zip_download',
        )
        with st.expander('生成画像プレビュー', expanded=True):
            preview = outputs[:12]
            cols = st.columns(3)
            for i, item in enumerate(preview):
                with cols[i % 3]:
                    st.image(item['png'], caption=f"{item.get('name','')}\n{item.get('address','')}", use_container_width=True)
                    st.caption(item.get('filename', ''))
        if len(outputs) > 12:
            st.caption(f'プレビューは先頭12枚のみ表示しています。全{len(outputs)}枚はZIPに入っています。')

# =========================================================
# v193 PATCH END
# =========================================================


# =========================================================
# v195 PATCH START: Excel指定マンション → リバブル画像抽出（均等配分）
# - ルート生成とは独立した単体機能
# - 指定マンション配布Excelからマンション名/住所を読み取り、リバブル詳細ページ画像を取得
# - 市区町村ごとにできるだけ均等に、合計20件前後を選ぶ
# - 画像取得できない市区町村がある場合は、画像がある市区町村から補填
# - Google Street View/APIは使わない
# =========================================================

try:
    import difflib as _difflib_v195
    import math as _math_v195
except Exception:
    pass


def _v195_compact_text(s: str) -> str:
    try:
        return _v184_compact(str(s or ""))
    except Exception:
        t = str(s or "").replace("　", " ")
        t = re.sub(r"\s+", "", t)
        return _v170_zen_to_han(t).lower()


def _v195_is_empty(v) -> bool:
    if v is None:
        return True
    s = str(v).strip()
    return not s or s.lower() in {"nan", "none", "null"}


def _v195_read_excel_or_csv(uploaded) -> Tuple[List[Dict[str, Any]], List[str], Dict[str, Any]]:
    """アップロードされたExcel/CSVから全シートの行を読む。列名は後段で自動推定する。"""
    warnings: List[str] = []
    meta: Dict[str, Any] = {"sheets": [], "raw_rows": 0}
    rows: List[Dict[str, Any]] = []
    if uploaded is None:
        return rows, warnings, meta
    if _pd_v170 is None:
        return rows, ["pandas が必要です。PowerShellで `pip install pandas openpyxl` を実行してください。"], meta
    try:
        data = uploaded.getvalue()
        name = getattr(uploaded, "name", "uploaded") or "uploaded"
        bio = _io_v170.BytesIO(data)
        if name.lower().endswith(".csv"):
            df = _pd_v170.read_csv(bio, dtype=str, encoding="utf-8-sig")
            sheets = {"CSV": df}
        else:
            sheets = _pd_v170.read_excel(bio, sheet_name=None, dtype=str, engine=None)
        for sheet_name, df in (sheets or {}).items():
            if df is None or getattr(df, "empty", True):
                continue
            df = df.dropna(how="all")
            if getattr(df, "empty", True):
                continue
            cols = [str(c).strip() for c in list(df.columns)]
            meta["sheets"].append({"sheet": str(sheet_name), "rows": int(len(df)), "cols": cols})
            for ridx, rec in df.fillna("").iterrows():
                d = {str(k).strip(): ("" if _v195_is_empty(v) else str(v).strip()) for k, v in rec.to_dict().items()}
                if any(str(v).strip() for v in d.values()):
                    d["__sheet__"] = str(sheet_name)
                    d["__row__"] = int(ridx) + 2
                    rows.append(d)
        meta["raw_rows"] = len(rows)
    except Exception as e:
        warnings.append(f"Excel/CSVを読めませんでした: {e}")
    return rows, warnings, meta


def _v195_column_candidates(rows: List[Dict[str, Any]]) -> Dict[str, str]:
    """列名と値の雰囲気から、マンション名列・住所列を推定する。"""
    if not rows:
        return {"name_col": "", "addr_col": ""}
    cols = [c for c in rows[0].keys() if not str(c).startswith("__")]
    name_words = ("マンション", "物件名", "建物名", "名称", "施設名", "配布先", "名称名", "name")
    addr_words = ("住所", "所在地", "住所地", "市区町村", "町名", "番地", "address")

    def label_score(col: str, words) -> int:
        lc = str(col).lower()
        return sum(20 for w in words if str(w).lower() in lc)

    def value_addr_score(col: str) -> int:
        vals = [str(r.get(col, "")) for r in rows[:80]]
        score = 0
        pref_pat = "|".join(map(re.escape, _V170_PREFS))
        for v in vals:
            cv = _v170_zen_to_han(v)
            if re.search(pref_pat, cv):
                score += 5
            if re.search(r"(市|区|町|村).{0,20}([0-9一二三四五六七八九十]+丁目|[0-9]+[-－ー])", cv):
                score += 3
        return score

    def value_name_score(col: str) -> int:
        vals = [str(r.get(col, "")) for r in rows[:80]]
        score = 0
        for v in vals:
            cv = v.strip()
            if not cv or len(cv) > 60:
                continue
            if any(x in cv for x in _V170_PREFS) or "丁目" in cv:
                continue
            if any(x in cv for x in ("マンション", "ハイツ", "コーポ", "レジデンス", "パレス", "メゾン", "ライオンズ", "サン", "プラザ", "ヒルズ", "ガーデン", "アパート", "荘", "ハウス", "ヴィラ")):
                score += 4
            else:
                score += 1
        return score

    addr_rank = sorted(cols, key=lambda c: (label_score(c, addr_words) + value_addr_score(c), value_addr_score(c)), reverse=True)
    name_rank = sorted(cols, key=lambda c: (label_score(c, name_words) + value_name_score(c), value_name_score(c)), reverse=True)
    addr_col = addr_rank[0] if addr_rank and (label_score(addr_rank[0], addr_words) + value_addr_score(addr_rank[0])) > 0 else ""
    name_col = name_rank[0] if name_rank and (label_score(name_rank[0], name_words) + value_name_score(name_rank[0])) > 0 else ""
    if name_col == addr_col:
        # 住所列と被った場合は次点の名前列へ逃がす
        for c in name_rank[1:]:
            if c != addr_col:
                name_col = c
                break
    return {"name_col": name_col, "addr_col": addr_col}


def _v195_extract_address_from_row(row: Dict[str, Any], addr_col: str = "") -> str:
    if addr_col and row.get(addr_col):
        return _v170_normalize_text(str(row.get(addr_col, "")))
    joined = " ".join(str(v) for k, v in row.items() if not str(k).startswith("__") and str(v).strip())
    # 既存の住所抽出をまず使う
    addr = _v170_extract_address_from_text(joined)
    if addr:
        return addr
    # 都道府県なしの住所も拾う
    m = re.search(r"([^\s,，、]+?[市区町村][^\s,，、]{1,80})", joined)
    return _v170_normalize_text(m.group(1)) if m else ""


def _v195_extract_name_from_row(row: Dict[str, Any], name_col: str = "", address: str = "") -> str:
    if name_col and row.get(name_col):
        return _v170_normalize_text(str(row.get(name_col, "")))
    # 住所っぽくない短めの文字列を名前候補にする
    best = ""
    for k, v in row.items():
        if str(k).startswith("__"):
            continue
        s = _v170_normalize_text(str(v or ""))
        if not s or s == address:
            continue
        if any(p in s for p in _V170_PREFS) or "丁目" in s or re.search(r"[0-9０-９]+[-－ー][0-9０-９]+", s):
            continue
        if len(s) <= 80:
            if not best or len(s) > len(best):
                best = s
    return best


def _v195_parse_pref_city_town(address: str, row: Dict[str, Any] = None) -> Dict[str, str]:
    """住所から都道府県/市区町村/町名/丁目を切り出す。"""
    addr = _v170_normalize_text(address or "")
    addr = _v170_zen_to_han(addr)
    pref = ""
    for p in _V170_PREFS:
        if p in addr:
            pref = p
            break
    # 列に都道府県が分かれている可能性も見る
    if not pref and row:
        joined = " ".join(str(v) for k, v in row.items() if not str(k).startswith("__"))
        for p in _V170_PREFS:
            if p in joined:
                pref = p
                break
    rest = addr
    if pref and pref in rest:
        rest = rest.split(pref, 1)[1]

    city = ""
    # 政令市区/23区/一般市町村を広めに取得
    m = re.match(r"(.+?(?:市.+?区|市|区|郡.+?町|郡.+?村|町|村))", rest)
    if m:
        city = m.group(1)
        rest2 = rest[m.end():]
    else:
        rest2 = rest

    # 町名は丁目/番地/数字の手前まで。丁目があれば町名は丁目手前。
    town = ""
    m2 = re.match(r"(.+?)(?:[0-9一二三四五六七八九十]+丁目|[0-9]+|番|番地|号|[-－ー])", rest2)
    if m2:
        town = m2.group(1)
    else:
        town = re.split(r"\s+", rest2.strip())[0] if rest2.strip() else ""
        town = town[:30]
    town = town.strip(" 　,，、")
    chome = _v170_extract_chome(address)
    return {"pref": pref, "city": city, "town": town, "chome": chome, "address_norm": addr}


def _v195_parse_excel_rows(raw_rows: List[Dict[str, Any]], name_col: str = "", addr_col: str = "") -> Tuple[List[Dict[str, Any]], List[str], Dict[str, Any]]:
    warnings: List[str] = []
    if not name_col or not addr_col:
        guess = _v195_column_candidates(raw_rows)
        name_col = name_col or guess.get("name_col", "")
        addr_col = addr_col or guess.get("addr_col", "")
    parsed: List[Dict[str, Any]] = []
    for i, row in enumerate(raw_rows, start=1):
        addr = _v195_extract_address_from_row(row, addr_col)
        name = _v195_extract_name_from_row(row, name_col, addr)
        info = _v195_parse_pref_city_town(addr, row)
        if not name and not addr:
            continue
        if not info.get("pref") or not info.get("city") or not info.get("town"):
            warnings.append(f"{row.get('__sheet__','')} {row.get('__row__','')}: 住所から都道府県/市区町村/町名を十分に読めませんでした: {addr}")
        parsed.append({
            "excel_no": i,
            "sheet": row.get("__sheet__", ""),
            "excel_row": row.get("__row__", ""),
            "name": name,
            "address": addr,
            "pref": info.get("pref", ""),
            "city": info.get("city", ""),
            "town": info.get("town", ""),
            "chome": info.get("chome", ""),
            "group_city": f"{info.get('pref','')} {info.get('city','')}".strip(),
            "group_town": f"{info.get('pref','')} {info.get('city','')} {info.get('town','')}".strip(),
            "raw": row,
        })
    meta = {"name_col": name_col, "addr_col": addr_col, "parsed_count": len(parsed)}
    return parsed, warnings, meta


def _v195_livable_group_from_parsed(p: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    if not p.get("pref") or not p.get("city") or not p.get("town"):
        return None
    name = f"{p.get('city','')}{p.get('town','')}"
    if p.get("chome"):
        name += p.get("chome")
    return {
        "pref": p.get("pref", ""),
        "city": p.get("city", ""),
        "town": p.get("town", ""),
        "chome": p.get("chome", ""),
        "name": name,
        "areas": [name],
        "sources": ["excel_v195"],
    }


def _v195_match_score(excel_item: Dict[str, Any], live_row: MansionRowV170) -> int:
    en = _v195_compact_text(excel_item.get("name", ""))
    ea = _v195_compact_text(excel_item.get("address", ""))
    ln = _v195_compact_text(live_row.name)
    la = _v195_compact_text(live_row.address)
    score = 0
    if en and ln:
        if en == ln:
            score += 85
        elif en in ln or ln in en:
            score += 65
        else:
            try:
                score += int(55 * _difflib_v195.SequenceMatcher(None, en, ln).ratio())
            except Exception:
                pass
    if ea and la:
        if ea == la:
            score += 70
        elif ea in la or la in ea:
            score += 55
        else:
            # 丁目/番地の数字一致を少し評価
            ed = re.findall(r"\d+", ea)
            ld = re.findall(r"\d+", la)
            if ed and ld and ed[:2] == ld[:2]:
                score += 25
            try:
                score += int(30 * _difflib_v195.SequenceMatcher(None, ea, la).ratio())
            except Exception:
                pass
    if excel_item.get("chome") and excel_item.get("chome") == live_row.chome:
        score += 10
    return int(score)


def _v195_find_best_livable_row(excel_item: Dict[str, Any], town_rows: List[MansionRowV170], min_score: int = 58) -> Tuple[Optional[MansionRowV170], int]:
    best = None
    best_score = -1
    for r in town_rows or []:
        sc = _v195_match_score(excel_item, r)
        if sc > best_score:
            best = r
            best_score = sc
    if best is not None and best_score >= int(min_score):
        return best, best_score
    return None, best_score


def _v195_balanced_select(items: List[Dict[str, Any]], target: int = 20, group_key: str = "group_city") -> List[Dict[str, Any]]:
    buckets: Dict[str, List[Dict[str, Any]]] = {}
    for it in items:
        k = it.get(group_key) or it.get("group_city") or "未分類"
        buckets.setdefault(k, []).append(it)
    # 市区町村名順。ただし各バケツ内はExcel順を維持。
    keys = sorted(buckets.keys())
    selected: List[Dict[str, Any]] = []
    while len(selected) < int(target) and any(buckets.get(k) for k in keys):
        for k in list(keys):
            if len(selected) >= int(target):
                break
            if buckets.get(k):
                selected.append(buckets[k].pop(0))
    return selected


def _v195_results_to_csv_bytes(items: List[Dict[str, Any]]) -> bytes:
    buf = _io_v170.StringIO()
    w = _csv_v170.writer(buf)
    w.writerow(["selected_no", "city_group", "excel_sheet", "excel_row", "excel_name", "excel_address", "livable_name", "livable_address", "score", "image_url", "detail_url", "status", "warning"])
    for idx, it in enumerate(items or [], start=1):
        w.writerow([
            idx, it.get("group_city", ""), it.get("sheet", ""), it.get("excel_row", ""), it.get("excel_name", ""), it.get("excel_address", ""),
            it.get("name", ""), it.get("address", ""), it.get("score", ""), it.get("image_url", ""), it.get("detail_url", ""), it.get("status", ""), it.get("warning", ""),
        ])
    return buf.getvalue().encode("utf-8-sig")


def _v195_build_excel_image_zip(items: List[Dict[str, Any]], make_flyer: bool, flyers: List[Any], seed: int = 195) -> bytes:
    rng = random.Random(seed)
    outputs: List[Dict[str, Any]] = []
    for idx, it in enumerate(items or [], start=1):
        base = _v185_fetch_image(it.get("image_url", ""))
        if base is None:
            continue
        safe = _v185_safe_filename(f"{it.get('group_city','')}_{it.get('name') or it.get('excel_name') or idx}")
        outputs.append({
            **it,
            "no": idx,
            "filename": f"{idx:03d}_{safe}_original.png",
            "png": _v185_image_to_png_bytes(base),
            "flyer_index": "none",
            "placement": "original",
        })
        if make_flyer and flyers:
            flyer_i = rng.randrange(len(flyers))
            comp, place = _v185_composite_flyer(base.convert("RGBA"), flyers[flyer_i], rng, position_mode="ランダム下側")
            outputs.append({
                **it,
                "no": idx,
                "filename": f"{idx:03d}_{safe}_flyer.png",
                "png": _v185_image_to_png_bytes(comp),
                "flyer_index": flyer_i + 1,
                "placement": str(place),
            })
    return _v185_build_zip(outputs)


def _v195_render_excel_designated_mansion_images() -> None:
    st.divider()
    st.subheader("指定マンションExcel → 画像取得")
    st.caption("指定マンション配布のExcelから、マンション名・住所を読み取り、リバブルの画像を市区町村ごとにできるだけ均等に取得します。ルート作成とは独立して使えます。")

    if _pd_v170 is None:
        st.error("Excel読み込みに pandas / openpyxl が必要です。PowerShellで `pip install pandas openpyxl` を実行してください。")
        return
    if requests is None or _BeautifulSoup_v170 is None:
        st.error("requests / beautifulsoup4 が必要です。PowerShellで `pip install requests beautifulsoup4` を実行してください。")
        return

    with st.expander("Excelアップロード / 抽出設定", expanded=True):
        uploaded = st.file_uploader(
            "指定マンション配布のExcel/CSVをアップロード",
            type=["xlsx", "xls", "csv"],
            accept_multiple_files=False,
            key="v195_excel_upload",
        )
        raw_rows, read_warnings, read_meta = _v195_read_excel_or_csv(uploaded) if uploaded is not None else ([], [], {})
        guess = _v195_column_candidates(raw_rows) if raw_rows else {"name_col": "", "addr_col": ""}
        all_cols = [c for c in (raw_rows[0].keys() if raw_rows else []) if not str(c).startswith("__")]
        c1, c2 = st.columns(2)
        name_col = c1.selectbox("マンション名の列（自動推定）", [""] + all_cols, index=([""] + all_cols).index(guess.get("name_col", "")) if guess.get("name_col", "") in all_cols else 0, key="v195_name_col") if all_cols else ""
        addr_col = c2.selectbox("住所の列（自動推定）", [""] + all_cols, index=([""] + all_cols).index(guess.get("addr_col", "")) if guess.get("addr_col", "") in all_cols else 0, key="v195_addr_col") if all_cols else ""

        c3, c4, c5, c6 = st.columns(4)
        target_count = int(c3.number_input("最終画像数", 1, 100, 20, 1, key="v195_target_count"))
        min_score = int(c4.number_input("一致判定スコア", 20, 150, 58, 1, key="v195_min_score"))
        max_details_per_town = int(c5.number_input("町名ごとの詳細確認上限", 10, 200, 80, 5, key="v195_max_details"))
        group_mode = c6.selectbox("均等配分単位", ["市区町村", "町名"], index=0, key="v195_group_mode")

        make_flyer = st.checkbox("チラシ合成版も一緒に作る（任意）", value=False, key="v195_make_flyer")
        flyers: List[Any] = []
        if make_flyer:
            flyer_uploads = st.file_uploader(
                "チラシだけの画像をアップロード（任意）",
                type=["png", "jpg", "jpeg", "webp", "gif"],
                accept_multiple_files=True,
                key="v195_flyer_uploads",
            )
            try:
                flyer_store, upload_errors = _v186_update_flyer_store(flyer_uploads or [])
                flyers, stored_errors = _v186_store_to_images(flyer_store)
                if flyers:
                    st.success(f"チラシ画像を認識しました：{len(flyers)}枚")
                if upload_errors or stored_errors:
                    with st.expander("チラシ読み込み診断", expanded=False):
                        for e in list(upload_errors or []) + list(stored_errors or []):
                            st.error(e)
            except Exception as e:
                st.warning(f"チラシ読み込みで問題が出ました: {e}")

        if raw_rows:
            st.success(f"Excel/CSV読込：{len(raw_rows)}行")
            with st.expander("読み込みシート/列情報", expanded=False):
                st.write(read_meta)
        for w in read_warnings[:10]:
            st.warning(w)

        run = st.button("指定マンション画像を取得", type="primary", use_container_width=True, key="v195_run")

    if uploaded is not None and raw_rows:
        parsed, parse_warnings, parse_meta = _v195_parse_excel_rows(raw_rows, name_col=name_col, addr_col=addr_col)
        if parsed:
            st.markdown("#### Excel解析プレビュー")
            preview_rows = [{"マンション名": p.get("name"), "住所": p.get("address"), "市区町村": p.get("group_city"), "町名": p.get("town"), "丁目": p.get("chome")} for p in parsed[:20]]
            try:
                st.dataframe(preview_rows, use_container_width=True, hide_index=True)
            except Exception:
                st.write(preview_rows)
            if len(parsed) > 20:
                st.caption(f"プレビューは先頭20行のみ。全{len(parsed)}行を対象にします。")
        for w in parse_warnings[:8]:
            st.warning(w)

    if run:
        if not uploaded:
            st.warning("Excel/CSVをアップロードしてください。")
            return
        raw_rows, read_warnings, _ = _v195_read_excel_or_csv(uploaded)
        parsed, parse_warnings, parse_meta = _v195_parse_excel_rows(raw_rows, name_col=name_col, addr_col=addr_col)
        targets = [p for p in parsed if p.get("name") and p.get("pref") and p.get("city") and p.get("town")]
        if not targets:
            st.error("マンション名・住所・都道府県/市区町村/町名を読める行がありませんでした。列指定を確認してください。")
            return

        # 町名単位でリバブル取得をキャッシュしながら、Excel行ごとに一致候補を探す
        town_cache: Dict[str, List[MansionRowV170]] = {}
        town_meta: Dict[str, Any] = {}
        found_items: List[Dict[str, Any]] = []
        errors: List[str] = []
        prog = st.progress(0.0, text="Excel指定マンションをリバブルで照合中...")
        total = len(targets)
        for idx, p in enumerate(targets, start=1):
            prog.progress((idx-1)/max(1, total), text=f"{idx}/{total} {p.get('name','')} を確認中...")
            g = _v195_livable_group_from_parsed(p)
            if not g:
                continue
            town_key = f"{g.get('pref')}|{g.get('city')}|{g.get('town')}"
            if town_key not in town_cache:
                try:
                    rows, meta, warns = _v184_rows_for_group(g, max_details_per_town=max_details_per_town, max_pages=6)
                    town_cache[town_key] = rows or []
                    town_meta[town_key] = {"meta": meta, "warnings": warns, "group": g}
                    for ww in warns or []:
                        if len(errors) < 20:
                            errors.append(str(ww))
                except Exception as e:
                    town_cache[town_key] = []
                    if len(errors) < 20:
                        errors.append(f"{p.get('group_town')}: リバブル取得失敗: {e}")
            best, score = _v195_find_best_livable_row(p, town_cache.get(town_key, []), min_score=min_score)
            if best is None:
                continue
            try:
                signs, warn = _v170_read_detail_for_signs(best, timeout=20)
            except Exception as e:
                signs, warn = [], f"詳細画像取得失敗: {e}"
            usable = [s for s in signs or [] if getattr(s, "label", "") != "除外" and getattr(s, "url", "")]
            if not usable:
                continue
            img = sorted(usable, key=lambda x: getattr(x, "priority", 99))[0]
            found_items.append({
                "excel_no": p.get("excel_no"),
                "sheet": p.get("sheet"),
                "excel_row": p.get("excel_row"),
                "excel_name": p.get("name"),
                "excel_address": p.get("address"),
                "group_city": p.get("group_city"),
                "group_town": p.get("group_town"),
                "name": best.name,
                "address": best.address,
                "chome": best.chome,
                "detail_url": best.detail_url,
                "detail_id": best.detail_id,
                "score": score,
                "image_url": img.url,
                "context": getattr(img, "context", ""),
                "status": "画像あり",
                "warning": warn,
            })
        prog.progress(1.0, text="照合完了")

        group_key = "group_town" if group_mode == "町名" else "group_city"
        selected = _v195_balanced_select(found_items, target=target_count, group_key=group_key)
        st.session_state["v195_excel_found_items"] = found_items
        st.session_state["v195_excel_selected_items"] = selected
        st.session_state["v195_excel_errors"] = errors
        st.success(f"画像あり候補：{len(found_items)}件 / 均等配分で選択：{len(selected)}件")

    found_items = st.session_state.get("v195_excel_found_items", []) or []
    selected = st.session_state.get("v195_excel_selected_items", []) or []
    errors = st.session_state.get("v195_excel_errors", []) or []
    if errors:
        with st.expander("取得メモ/警告", expanded=False):
            for e in errors[:50]:
                st.warning(e)

    if selected:
        st.markdown("#### 均等配分で選ばれた画像")
        counts: Dict[str, int] = {}
        for it in selected:
            counts[it.get("group_city", "未分類")] = counts.get(it.get("group_city", "未分類"), 0) + 1
        st.caption(" / ".join([f"{k}: {v}枚" for k, v in sorted(counts.items())]))
        csv_bytes = _v195_results_to_csv_bytes(selected)
        st.download_button("選択結果CSVをダウンロード", data=csv_bytes, file_name="v195_excel_designated_mansion_selected.csv", mime="text/csv", use_container_width=True, key="v195_csv")

        c1, c2 = st.columns(2)
        seed = int(c1.number_input("ZIP作成seed", 0, 999999, 195, 1, key="v195_zip_seed"))
        make_zip_flyer = c2.checkbox("ZIPにチラシ合成版も入れる", value=bool(st.session_state.get("v195_make_flyer", False)), key="v195_zip_make_flyer")
        flyers_for_zip: List[Any] = []
        if make_zip_flyer:
            try:
                flyer_store = st.session_state.get("v186_flyer_store", []) or st.session_state.get("v187_flyer_store", []) or []
                flyers_for_zip, _errs = _v186_store_to_images(flyer_store)
            except Exception:
                flyers_for_zip = []
            if not flyers_for_zip:
                st.info("チラシ合成版をZIPに入れるには、上のチラシ画像アップロードで認識させてから再実行してください。原本画像のみでもZIP作成できます。")

        zip_bytes = _v195_build_excel_image_zip(selected, make_flyer=make_zip_flyer and bool(flyers_for_zip), flyers=flyers_for_zip, seed=seed)
        st.download_button("画像ZIPをダウンロード", data=zip_bytes, file_name="v195_excel_designated_mansion_images.zip", mime="application/zip", use_container_width=True, key="v195_zip")

        cols = st.columns(4)
        for i, it in enumerate(selected[:24]):
            with cols[i % 4]:
                st.image(it.get("image_url", ""), caption=f"{i+1}. {it.get('name','')}\n{it.get('address','')}", use_container_width=True)
                st.caption(f"Excel: {it.get('excel_name','')} / score {it.get('score','')}")
        if len(selected) > 24:
            st.caption(f"プレビューは先頭24枚のみ。全{len(selected)}枚はZIPに入ります。")
    elif found_items:
        st.info("画像あり候補はありますが、選択結果が空です。最終画像数や均等配分設定を確認してください。")


try:
    _V195_PREV_RENDER_SELECTED_AREA = render_selected_area_livable_sign_images_v170
except Exception:
    _V195_PREV_RENDER_SELECTED_AREA = None


def render_selected_area_livable_sign_images_v170() -> None:  # type: ignore[override]
    if _V195_PREV_RENDER_SELECTED_AREA is not None:
        _V195_PREV_RENDER_SELECTED_AREA()
    _v195_render_excel_designated_mansion_images()

# =========================================================
# v195 PATCH END
# =========================================================


try:
    _V196_OLD_COLUMN_CANDIDATES = _v195_column_candidates
except Exception:
    _V196_OLD_COLUMN_CANDIDATES = None

# =========================================================
# v196 PATCH START: openpyxl不要のExcel読込＋指定物件シート優先
# =========================================================
# 目的:
# - ユーザー環境で openpyxl が未インストールでも .xlsx を読めるようにする。
# - Excelの「ふりがな（phonetic）」を本文に混ぜない。
# - 「指定物件」シートを優先して読む。
# - 住所に都道府県が無い場合でも、市区列やファイル内の都道府県から補完する。
# =========================================================

import zipfile as _zipfile_v196
import xml.etree.ElementTree as _ET_v196
import csv as _csv_v196


def _v196_col_to_index(cell_ref: str) -> int:
    m = re.match(r"([A-Z]+)", str(cell_ref or "").upper())
    if not m:
        return 0
    n = 0
    for ch in m.group(1):
        n = n * 26 + (ord(ch) - 64)
    return n - 1


def _v196_shared_string_text(si) -> str:
    """Excelの共有文字列から、ふりがな(rPh)を除いて本文だけ読む。"""
    ns = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
    parts = []
    for child in list(si):
        tag = child.tag.split("}")[-1]
        if tag == "t":
            parts.append(child.text or "")
        elif tag == "r":
            t = child.find(ns + "t")
            if t is not None:
                parts.append(t.text or "")
        # rPh / phoneticPr は読み飛ばす
    return "".join(parts)


def _v196_read_xlsx_tables(data: bytes) -> Tuple[List[Dict[str, Any]], List[str], Dict[str, Any]]:
    warnings: List[str] = []
    meta: Dict[str, Any] = {"sheets": [], "raw_rows": 0, "reader": "v196_zip_xml_no_openpyxl"}
    all_tables: List[Dict[str, Any]] = []

    ns_main = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
    ns_rel = "{http://schemas.openxmlformats.org/officeDocument/2006/relationships}"

    try:
        with _zipfile_v196.ZipFile(_io_v170.BytesIO(data)) as z:
            names = set(z.namelist())

            shared: List[str] = []
            if "xl/sharedStrings.xml" in names:
                root = _ET_v196.fromstring(z.read("xl/sharedStrings.xml"))
                for si in root.findall(ns_main + "si"):
                    shared.append(_v196_shared_string_text(si))

            wb = _ET_v196.fromstring(z.read("xl/workbook.xml"))
            rels = _ET_v196.fromstring(z.read("xl/_rels/workbook.xml.rels"))
            relmap = {}
            for r in rels:
                rid = r.attrib.get("Id")
                target = r.attrib.get("Target", "")
                if rid:
                    relmap[rid] = target

            sheet_defs = []
            sheets_node = wb.find(ns_main + "sheets")
            if sheets_node is not None:
                for sh in sheets_node.findall(ns_main + "sheet"):
                    sname = sh.attrib.get("name", "")
                    rid = sh.attrib.get(ns_rel + "id", "")
                    target = relmap.get(rid, "")
                    if target:
                        if target.startswith("/"):
                            spath = target.lstrip("/")
                        elif target.startswith("xl/"):
                            spath = target
                        else:
                            spath = "xl/" + target
                        sheet_defs.append((sname, spath))

            for sheet_name, spath in sheet_defs:
                if spath not in names:
                    continue
                root = _ET_v196.fromstring(z.read(spath))
                grid: List[List[str]] = []
                for row in root.findall(ns_main + "sheetData/" + ns_main + "row"):
                    vals: Dict[int, str] = {}
                    for c in row.findall(ns_main + "c"):
                        cref = c.attrib.get("r", "")
                        ci = _v196_col_to_index(cref)
                        ctype = c.attrib.get("t", "")
                        text = ""

                        v = c.find(ns_main + "v")
                        if v is not None and v.text is not None:
                            raw = v.text
                            if ctype == "s":
                                try:
                                    idx = int(raw)
                                    text = shared[idx] if 0 <= idx < len(shared) else raw
                                except Exception:
                                    text = raw
                            else:
                                text = raw

                        # inlineStr対応
                        is_node = c.find(ns_main + "is")
                        if is_node is not None:
                            inline_parts = []
                            for child in list(is_node):
                                tag = child.tag.split("}")[-1]
                                if tag == "t":
                                    inline_parts.append(child.text or "")
                                elif tag == "r":
                                    t = child.find(ns_main + "t")
                                    if t is not None:
                                        inline_parts.append(t.text or "")
                            text = "".join(inline_parts)

                        vals[ci] = str(text).strip()

                    if vals:
                        max_i = max(vals.keys())
                        grid.append([vals.get(i, "") for i in range(max_i + 1)])
                    else:
                        grid.append([])

                # それらしいヘッダー行を探す
                header_idx = None
                best_score = -1
                for i, r in enumerate(grid[:30]):
                    joined = " ".join(str(x) for x in r)
                    score = 0
                    if any(k in joined for k in ("マンション名", "物件名", "建物名", "名称")):
                        score += 5
                    if any(k in joined for k in ("住所", "所在地", "市区", "市区町村")):
                        score += 5
                    if any(k in joined for k in ("予定数", "配布数")):
                        score += 1
                    if score > best_score and score >= 5:
                        best_score = score
                        header_idx = i

                if header_idx is None:
                    continue

                headers_raw = [str(x).strip() for x in grid[header_idx]]
                headers: List[str] = []
                for j, h in enumerate(headers_raw):
                    h = h.strip()
                    if not h:
                        h = f"列{j+1}"
                    # 重複列名対策
                    base = h
                    n = 2
                    while h in headers:
                        h = f"{base}_{n}"
                        n += 1
                    headers.append(h)

                table_rows: List[Dict[str, Any]] = []
                for ridx, r in enumerate(grid[header_idx + 1:], start=header_idx + 2):
                    if not any(str(x).strip() for x in r):
                        continue
                    d: Dict[str, Any] = {}
                    for j, h in enumerate(headers):
                        v = r[j].strip() if j < len(r) else ""
                        d[h] = v
                    if any(str(v).strip() for v in d.values()):
                        d["__sheet__"] = str(sheet_name)
                        d["__row__"] = int(ridx)
                        table_rows.append(d)

                if table_rows:
                    all_tables.append({
                        "sheet": str(sheet_name),
                        "rows": table_rows,
                        "cols": headers,
                        "score": best_score,
                    })
                    meta["sheets"].append({"sheet": str(sheet_name), "rows": len(table_rows), "cols": headers, "score": best_score})

        if not all_tables:
            return [], ["Excel内にマンション名/住所を読める表が見つかりませんでした。"], meta

        # 指定物件系を優先。戸建・禁止は除外候補にする。
        def table_rank(t: Dict[str, Any]) -> int:
            name = str(t.get("sheet", ""))
            cols = " ".join(map(str, t.get("cols", [])))
            rank = int(t.get("score", 0))
            if "指定" in name or "指定" in cols:
                rank += 50
            if "物件" in name or "物件" in cols or "マンション" in cols:
                rank += 30
            if "戸建" in name:
                rank -= 40
            if "禁止" in name:
                rank -= 80
            return rank

        ranked = sorted(all_tables, key=table_rank, reverse=True)
        chosen = ranked[0]
        rows = chosen["rows"]

        meta["chosen_sheet"] = chosen.get("sheet", "")
        meta["chosen_cols"] = chosen.get("cols", [])
        meta["raw_rows"] = len(rows)
        if len(ranked) > 1:
            meta["other_candidate_sheets"] = [{"sheet": t.get("sheet"), "rows": len(t.get("rows", [])), "rank": table_rank(t)} for t in ranked[1:]]
        return rows, warnings, meta
    except Exception as e:
        return [], [f"Excelを標準XMLリーダーで読めませんでした: {e}"], meta


def _v195_read_excel_or_csv(uploaded) -> Tuple[List[Dict[str, Any]], List[str], Dict[str, Any]]:  # type: ignore[override]
    """v196: openpyxl不要。xlsxはzip/xml直読み、csvは標準csvで読む。"""
    warnings: List[str] = []
    meta: Dict[str, Any] = {"sheets": [], "raw_rows": 0, "reader": "v196"}
    rows: List[Dict[str, Any]] = []
    if uploaded is None:
        return rows, warnings, meta
    try:
        data = uploaded.getvalue()
        name = getattr(uploaded, "name", "uploaded") or "uploaded"
        lname = str(name).lower()

        if lname.endswith(".csv"):
            text = data.decode("utf-8-sig", errors="replace")
            reader = _csv_v196.DictReader(_io_v170.StringIO(text))
            for i, rec in enumerate(reader, start=2):
                d = {str(k or "").strip(): ("" if _v195_is_empty(v) else str(v).strip()) for k, v in (rec or {}).items()}
                if any(str(v).strip() for v in d.values()):
                    d["__sheet__"] = "CSV"
                    d["__row__"] = i
                    rows.append(d)
            meta["sheets"] = [{"sheet": "CSV", "rows": len(rows), "cols": list(rows[0].keys()) if rows else []}]
            meta["raw_rows"] = len(rows)
            return rows, warnings, meta

        if lname.endswith(".xlsx") or lname.endswith(".xlsm") or lname.endswith(".xls"):
            # xlsは本来zip/xmlでは読めないが、最近の拡張子偽装もあるため一度試す
            rows, warnings, meta = _v196_read_xlsx_tables(data)
            return rows, warnings, meta

        warnings.append("対応形式は .xlsx / .xlsm / .csv です。")
        return rows, warnings, meta
    except Exception as e:
        warnings.append(f"Excel/CSVを読めませんでした: {e}")
        return rows, warnings, meta


def _v196_clean_city_name(s: str) -> str:
    s = _v170_normalize_text(str(s or ""))
    s = _v170_zen_to_han(s)
    m = re.search(r"(.+?[市区町村])", s)
    return m.group(1) if m else s


def _v196_city_to_pref(city: str) -> str:
    city = _v196_clean_city_name(city)
    # 今回のリバブル志木センター系・首都圏で最低限必要な市区を補完
    saitama = {
        "朝霞市", "志木市", "新座市", "和光市", "富士見市", "ふじみ野市", "さいたま市", "川口市",
        "戸田市", "蕨市", "草加市", "越谷市", "三郷市", "八潮市", "所沢市", "入間市", "狭山市",
        "川越市", "上尾市", "桶川市", "春日部市", "久喜市", "蓮田市", "白岡市"
    }
    chiba = {"松戸市", "柏市", "流山市", "我孫子市", "市川市", "船橋市", "鎌ケ谷市", "野田市", "浦安市", "千葉市"}
    tokyo_23 = {
        "千代田区","中央区","港区","新宿区","文京区","台東区","墨田区","江東区","品川区","目黒区",
        "大田区","世田谷区","渋谷区","中野区","杉並区","豊島区","北区","荒川区","板橋区","練馬区",
        "足立区","葛飾区","江戸川区"
    }
    if city in saitama:
        return "埼玉県"
    if city in chiba:
        return "千葉県"
    if city in tokyo_23 or city.endswith("市") and city in {"武蔵野市","三鷹市","調布市","府中市","小金井市","国分寺市","国立市","立川市","町田市","八王子市"}:
        return "東京都"
    return ""


def _v196_dominant_pref_from_rows(rows: List[Dict[str, Any]]) -> str:
    counts: Dict[str, int] = {}
    for row in rows or []:
        joined = " ".join(str(v) for k, v in row.items() if not str(k).startswith("__"))
        for p in _V170_PREFS:
            if p in joined:
                counts[p] = counts.get(p, 0) + 1
    if counts:
        return sorted(counts.items(), key=lambda kv: kv[1], reverse=True)[0][0]
    return ""


def _v195_parse_excel_rows(raw_rows: List[Dict[str, Any]], name_col: str = "", addr_col: str = "") -> Tuple[List[Dict[str, Any]], List[str], Dict[str, Any]]:  # type: ignore[override]
    """v196: 市区列/都道府県列が分かれているExcelにも対応。"""
    warnings: List[str] = []
    if not name_col or not addr_col:
        guess = _v195_column_candidates(raw_rows)
        name_col = name_col or guess.get("name_col", "")
        addr_col = addr_col or guess.get("addr_col", "")

    # 市区列・都道府県列も自動推定
    cols = [c for c in (raw_rows[0].keys() if raw_rows else []) if not str(c).startswith("__")]
    city_col = ""
    pref_col = ""
    for c in cols:
        cs = str(c)
        if not city_col and any(k in cs for k in ("市区", "市区町村", "市町村")):
            city_col = c
        if not pref_col and "都道府県" in cs:
            pref_col = c
    dominant_pref = _v196_dominant_pref_from_rows(raw_rows)

    parsed: List[Dict[str, Any]] = []
    for i, row in enumerate(raw_rows, start=1):
        addr = _v195_extract_address_from_row(row, addr_col)
        city_from_col = _v196_clean_city_name(row.get(city_col, "")) if city_col else ""
        pref_from_col = str(row.get(pref_col, "")).strip() if pref_col else ""

        # 住所に市区がない/弱い場合は市区列を先頭に足す
        if city_from_col and city_from_col not in addr:
            addr = f"{city_from_col}{addr}"

        name = _v195_extract_name_from_row(row, name_col, addr)
        info = _v195_parse_pref_city_town(addr, row)

        if not info.get("city") and city_from_col:
            info["city"] = city_from_col

        if not info.get("pref"):
            pref_guess = pref_from_col if pref_from_col in _V170_PREFS else ""
            if not pref_guess and info.get("city"):
                pref_guess = _v196_city_to_pref(info.get("city", ""))
            if not pref_guess:
                pref_guess = dominant_pref
            info["pref"] = pref_guess

        # 住所正規化も都道府県付きに寄せる
        address_norm = info.get("address_norm", addr)
        if info.get("pref") and info.get("pref") not in address_norm:
            address_norm = info.get("pref") + address_norm
        info["address_norm"] = address_norm

        if not name and not addr:
            continue
        if not info.get("pref") or not info.get("city") or not info.get("town"):
            warnings.append(f"{row.get('__sheet__','')} {row.get('__row__','')}: 住所から都道府県/市区町村/町名を十分に読めませんでした: {addr}")

        parsed.append({
            "excel_no": i,
            "sheet": row.get("__sheet__", ""),
            "excel_row": row.get("__row__", ""),
            "name": name,
            "address": address_norm,
            "pref": info.get("pref", ""),
            "city": info.get("city", ""),
            "town": info.get("town", ""),
            "chome": info.get("chome", ""),
            "group_city": f"{info.get('pref','')} {info.get('city','')}".strip(),
            "group_town": f"{info.get('pref','')} {info.get('city','')} {info.get('town','')}".strip(),
            "raw": row,
        })

    meta = {"name_col": name_col, "addr_col": addr_col, "city_col": city_col, "pref_col": pref_col, "dominant_pref": dominant_pref, "parsed_count": len(parsed)}
    return parsed, warnings, meta


def _v195_column_candidates(rows: List[Dict[str, Any]]) -> Dict[str, str]:  # type: ignore[override]
    """v196: 指定物件Excelの列名に強くする。"""
    if not rows:
        return {"name_col": "", "addr_col": ""}
    cols = [c for c in rows[0].keys() if not str(c).startswith("__")]
    name_col = ""
    addr_col = ""

    for c in cols:
        cs = str(c)
        if not name_col and any(k in cs for k in ("マンション名", "物件名", "建物名", "名称")):
            name_col = c
        if not addr_col and any(k in cs for k in ("住所", "所在地")):
            addr_col = c

    if name_col and addr_col:
        return {"name_col": name_col, "addr_col": addr_col}

    # 足りない場合だけ旧ロジックへ
    try:
        return _V196_OLD_COLUMN_CANDIDATES(rows)
    except Exception:
        return {"name_col": name_col, "addr_col": addr_col}


try:
    _V196_OLD_COLUMN_CANDIDATES
except NameError:
    # ここに到達する頃には上でoverride済みなので、旧関数を残せない環境向けの保険
    pass

# =========================================================
# v196 PATCH END
# =========================================================


# =========================================================
# v197 PATCH START: 指定マンション画像を住所順でまとめて表示/出力
# =========================================================

import unicodedata as _unicodedata_v197

_V197_PREF_ORDER = {
    "北海道": 1, "青森県": 2, "岩手県": 3, "宮城県": 4, "秋田県": 5, "山形県": 6, "福島県": 7,
    "茨城県": 8, "栃木県": 9, "群馬県": 10, "埼玉県": 11, "千葉県": 12, "東京都": 13, "神奈川県": 14,
    "新潟県": 15, "富山県": 16, "石川県": 17, "福井県": 18, "山梨県": 19, "長野県": 20,
    "岐阜県": 21, "静岡県": 22, "愛知県": 23, "三重県": 24,
    "滋賀県": 25, "京都府": 26, "大阪府": 27, "兵庫県": 28, "奈良県": 29, "和歌山県": 30,
    "鳥取県": 31, "島根県": 32, "岡山県": 33, "広島県": 34, "山口県": 35,
    "徳島県": 36, "香川県": 37, "愛媛県": 38, "高知県": 39,
    "福岡県": 40, "佐賀県": 41, "長崎県": 42, "熊本県": 43, "大分県": 44, "宮崎県": 45, "鹿児島県": 46, "沖縄県": 47,
}
_V197_KANJI_NUM = {"一":1, "二":2, "三":3, "四":4, "五":5, "六":6, "七":7, "八":8, "九":9, "十":10}

def _v197_norm_addr_text(s: str) -> str:
    s = str(s or "")
    s = _unicodedata_v197.normalize("NFKC", s)
    s = s.replace("−", "-").replace("ー", "-").replace("－", "-").replace("―", "-").replace("–", "-")
    s = re.sub(r"\s+", "", s)
    return s

def _v197_chome_num(value: str) -> int:
    s = _v197_norm_addr_text(value)
    m = re.search(r"(\d+)\s*丁目", s)
    if m:
        return int(m.group(1))
    m = re.search(r"([一二三四五六七八九十])丁目", s)
    if m:
        return _V197_KANJI_NUM.get(m.group(1), 999)
    return 0

def _v197_extract_block_numbers(addr: str):
    s = _v197_norm_addr_text(addr)
    nums = [int(x) for x in re.findall(r"\d+", s)]
    return tuple(nums[:8]) if nums else tuple()

def _v197_sort_key(item):
    pref = str(item.get("pref") or item.get("excel_pref") or "")
    city = str(item.get("city") or item.get("excel_city") or item.get("group_city") or "")
    town = str(item.get("town") or item.get("excel_town") or "")
    chome = str(item.get("chome") or item.get("excel_chome") or "")
    addr = str(item.get("address") or item.get("excel_address") or item.get("matched_address") or item.get("title") or "")
    name = str(item.get("name") or item.get("excel_name") or item.get("matched_name") or item.get("title") or "")

    gc = str(item.get("group_city") or "")
    if (not pref or not city) and gc:
        for p in _V197_PREF_ORDER.keys():
            if p in gc:
                pref = pref or p
                city = city or gc.replace(p, "").strip()
                break

    addr_norm = _v197_norm_addr_text(addr)
    if not pref:
        for p in _V197_PREF_ORDER.keys():
            if p in addr_norm:
                pref = p
                break
    if not city:
        m = re.search(r"(.+?[市区町村])", addr_norm)
        if m:
            city = m.group(1)
    if not town:
        try:
            info = _v195_parse_pref_city_town(addr_norm, {})
            town = info.get("town", "") or town
            chome = chome or info.get("chome", "")
        except Exception:
            pass

    try:
        city_clean = _v196_clean_city_name(city)
    except Exception:
        city_clean = city

    return (
        _V197_PREF_ORDER.get(pref, 999),
        pref,
        _v197_norm_addr_text(city_clean),
        _v197_norm_addr_text(town),
        _v197_chome_num(chome or addr_norm),
        _v197_extract_block_numbers(addr_norm),
        _v197_norm_addr_text(name),
    )

def _v197_sort_items_by_address(items):
    try:
        return sorted(list(items or []), key=_v197_sort_key)
    except Exception:
        return list(items or [])

try:
    _V197_OLD_BALANCED_SELECT = _v195_balanced_select
except Exception:
    _V197_OLD_BALANCED_SELECT = None

def _v195_balanced_select(candidates, limit, group_key="group_city"):
    if _V197_OLD_BALANCED_SELECT is None:
        selected = list(candidates or [])[:int(limit or 20)]
    else:
        selected = _V197_OLD_BALANCED_SELECT(candidates, limit, group_key)
    return _v197_sort_items_by_address(selected)

def _v197_apply_address_order_to_session():
    try:
        for key in [
            "v195_selected", "v195_selected_items", "v195_results",
            "v195_selected_candidates", "v196_selected",
            "excel_mansion_selected", "v195_candidates"
        ]:
            if key in st.session_state and isinstance(st.session_state[key], list):
                st.session_state[key] = _v197_sort_items_by_address(st.session_state[key])
    except Exception:
        pass

try:
    _V197_OLD_RENDER = render_v195_excel_designated_mansion_images
except Exception:
    _V197_OLD_RENDER = None

def render_v195_excel_designated_mansion_images():
    if _V197_OLD_RENDER is not None:
        result = _V197_OLD_RENDER()
        _v197_apply_address_order_to_session()
        return result
    st.error("v197: 既存の指定マンションExcel画面が見つかりません。")

# =========================================================
# v197 PATCH END
# =========================================================



if __name__ == '__main__':
    main()
