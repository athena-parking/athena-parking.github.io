/* ============================================================
   Athena Parking - routing engine
   Edge-based Dijkstra so turn cost is expressible.
   In production this runs at PUBLISH time (networkx) and the
   output is baked to JSON. Here it runs client-side to prove it.
   ============================================================ */

/* createEngine(map) -> a self-contained engine bound to ONE map.

   Deliberately a factory rather than a module-level global: the publish
   backend must validate an UPLOADED map, and it must do so with exactly
   this code. Two validators would drift, and the day they disagree is the
   day a broken map goes live. */
function createEngine(MAP) {

  const TURN_PENALTY  = 15;   // metre-equivalents: a turn costs ~15 m of "thinking"
  const LEVEL_PENALTY = 40;   // changing level is expensive and confusing
  const STRAIGHT_DEG  = 25;   // below this, it is not a turn
  const UTURN_DEG     = 130;
  const BEND_DEG      = 40;   // a run of road that bends this far round is "follow the road round"
  const AVOID_PENALTY = 500;  // "avoid if possible": only taken when nothing else gets there

  const G = { nodes: {}, slots: {}, out: {}, edges: {}, flats: {}, flatIndex: [], turns: {} };
  var NODE_AT = {};                   // the map's own nodes, for work done before the graph is built
  MAP.nodes.forEach(function (n) { NODE_AT[n.id] = n; });

  /* ---------- routing overlay (written in the routes editor) ----------
     MAP.routing holds the editor's rules, keyed by stretch: an edge's key is
     its two end nodes' stable keys, sorted and joined by "~", so "fwd" means
     travelling from the first of those to the second. A rule can set the
     traffic direction, how the stretch may be used, and the words for each
     direction. It is applied here, in place, before anything reads the map,
     and it is idempotent: a direction is set absolutely, never toggled, so
     a map that has been through this once comes out the same the second time. */
  (function applyRouting() {
    var R = MAP.routing;
    if (!R) return;
    if (R.turns) G.turns = R.turns;
    if (!R.edges) return;
    var NK = {};
    MAP.nodes.forEach(function (n) { NK[n.id] = n.key || n.id; });
    var slotsOn = {};
    (MAP.slots || []).forEach(function (s) { (slotsOn[s.edge] = slotsOn[s.edge] || []).push(s); });
    MAP.edges.forEach(function (e) {
      var ov = e.key && R.edges[e.key];
      if (!ov) return;
      var ends = e.key.split("~");
      function flip() {
        var t = e.from; e.from = e.to; e.to = t;
        if (e.shape) e.shape = e.shape.slice().reverse();      // a curved road runs the other way too
        // the old forward words now describe the reverse; a missing reverse leaves the new forward automatic
        var fwd = e.instruction, rev = e.instructionRev;
        e.instruction = rev == null ? null : rev; e.instructionRev = fwd == null ? null : fwd;
        var pf = e.photo, pr = e.photoRev;
        e.photo = pr == null ? null : pr; e.photoRev = pf == null ? null : pf;
        // a bay's position along the aisle and its side are measured from `from`
        (slotsOn[e.id] || []).forEach(function (sl) {
          sl.t = Math.round((1 - sl.t) * 10000) / 10000;
          sl.side = -(sl.side == null ? 1 : sl.side);
        });
      }
      if (ov.dir === "fwd" || ov.dir === "rev") {
        if (NK[e.from] !== (ov.dir === "fwd" ? ends[0] : ends[1])) flip();
        e.oneway = true;
      } else if (ov.dir === "both") {
        e.oneway = false;
      }
      if (ov.use === "walk") { e.mode = ["foot"]; e.avoid = false; }
      else if (ov.use === "closed") { e.mode = []; e.avoid = false; }
      else if (ov.use === "avoid") e.avoid = true;
      else if (ov.use === "normal") e.avoid = false;
      var fwdIsFT = NK[e.from] === ends[0];
      // "" is a deliberate choice of the automatic wording; it must not fall back to the other direction's words
      // Words or a photo given for one direction belong to that direction only: the other
      // direction says its own (or the automatic words) and shows its own photo (or none),
      // never the first one's - "turn right under the bar" is wrong driven the other way.
      if (ov.say) {
        if (ov.say.fwd != null) e[fwdIsFT ? "instruction" : "instructionRev"] = ov.say.fwd;
        if (ov.say.rev != null) e[fwdIsFT ? "instructionRev" : "instruction"] = ov.say.rev;
        if (e.instructionRev == null) e.instructionRev = "";
      }
      if (ov.photo) {
        if (ov.photo.fwd != null) e[fwdIsFT ? "photo" : "photoRev"] = ov.photo.fwd || null;
        if (ov.photo.rev != null) e[fwdIsFT ? "photoRev" : "photo"] = ov.photo.rev || null;
        if (e.photoRev == null) e.photoRev = "";
      }
    });
  })();

  /* ---------- build ---------- */
  function buildGraph() {
    MAP.nodes.forEach(function (n) { G.nodes[n.id] = n; G.out[n.id] = []; });

    MAP.edges.forEach(function (e) {
      G.edges[e.id] = e;
      G.out[e.from].push(Object.assign({}, e, { dir: 1, a: e.from, b: e.to }));
      if (!e.oneway) G.out[e.to].push(Object.assign({}, e, { dir: -1, a: e.to, b: e.from }));
    });

    // Expand slot runs -> individual slot leaves hanging off an edge.
    MAP.slotRuns.forEach(function (run) {
      var count = run.to - run.from + 1;
      for (var i = 0; i < count; i++) {
        var num  = run.from + i;
        var id   = run.prefix + String(num).padStart(2, "0");
        var pair = Math.floor(i / 2);                        // slots come in facing pairs
        var t    = (pair + 0.5) / Math.ceil(count / 2);      // fraction along the aisle
        G.slots[id] = {
          id: id, edge: run.edge, t: t,
          side: num % 2 ? run.oddSide : run.evenSide,
          landmark: run.pillarPrefix + (Math.floor(pair / run.pillarEvery) + 1)
        };
      }
    });

    // Slots placed one at a time in the editor. A run assumes a tidy line of
    // identical bays; where the real thing is not tidy, someone clicks each bay
    // and we store exactly that. Same shape either way: a point on an edge.
    (MAP.slots || []).forEach(function (s) {
      G.slots[s.id] = { id: s.id, edge: s.edge, t: s.t,
                        side: s.side == null ? 1 : s.side,
                        landmark: s.landmark || null, hand: true };
    });

    // Expand the block table into the full flat roster. 546 flats are
    // DECLARED, never enumerated - the same trick as slotRuns.
    MAP.blocks.forEach(function (b) {
      // Ground-floor units are numbered G1..Gn and are NOT zero-padded like the
      // towers above them - E-G3, never E-003. A block without them declares none.
      for (var g = 1; g <= (b.ground || 0); g++) {
        var gid = b.id + "-G" + g;
        G.flats[gid] = { id: gid, block: b.id, blockName: b.name,
                         floor: 0, unit: g, lobby: b.lobby, slots: [] };
        G.flatIndex.push(gid);
      }
      for (var fl = 1; fl <= b.floors; fl++) {
        for (var u = 1; u <= b.perFloor; u++) {
          var id = b.id + "-" + fl + String(u).padStart(2, "0");
          G.flats[id] = { id: id, block: b.id, blockName: b.name,
                          floor: fl, unit: u, lobby: b.lobby, slots: [] };
          G.flatIndex.push(id);
        }
      }
    });

    // A hand-placed slot can name its own flat, which saves keeping a separate
    // allotment row in step with it.
    (MAP.slots || []).forEach(function (s) {
      if (!s.flat) return;
      var f = G.flats[s.flat];
      if (!f) return;
      if (f.slots.indexOf(s.id) < 0) f.slots.push(s.id);
      G.slots[s.id].flat = s.flat;
    });

    // A zone roster records which flats park inside it without saying which
    // bay. That is weaker than a slot but far better than nothing: it still
    // resolves to a place the router can reach.
    (MAP.areas || []).forEach(function (a) {
      if (!a.node || !a.flats) return;
      a.flats.forEach(function (f) {
        var fl = G.flats[f.flat];
        if (!fl || fl.park) return;
        fl.park = a.node; fl.parkName = a.name; fl.parkSlots = f.slots || null;
      });
    });

    // Merge the RWA's allotted-slot sheet on top. Unknown flats are left
    // for validate() to report, never silently created here.
    MAP.allotments.forEach(function (a) {
      var f = G.flats[a.flat];
      if (!f) return;
      a.slots.forEach(function (sid) {
        if (!G.slots[sid]) return;
        f.slots.push(sid);
        G.slots[sid].flat = a.flat;
      });
    });
  }

  /* What to call a node out loud. A lift core is drawn as one area with a
     plain name ("Block A") and split into one node per level, and those nodes
     carry a "(B2)" that the map file needs and a resident does not. Say the
     area's name; fall back to the node's own for everything else.
     One definition, because the list row, the journey header and the last line
     of the directions must never call the same place three things. */
  var AREA_NAME = {};
  (MAP.areas || []).forEach(function (a) { if (a.node) AREA_NAME[a.node] = a.name; });
  function isLift(n) { return !!n && (n.lift === true || /\blift\b/i.test(n.name || "")); }
  function nodeLabel(n) {
    if (!n) return "";
    if (isLift(n) && AREA_NAME[n.id]) return AREA_NAME[n.id] + " lift";
    return n.name || n.id;
  }

  /* Normalised key so "d802", "D-802" and "d 802" all match. */
  function normFlat(s) { return String(s || "").toUpperCase().replace(/[^A-Z0-9]/g, ""); }

  /* "A1503" -> "A-1503". Block letter, floor, then a 2-digit unit.
     "EG3" -> "E-G3" for ground-floor units, which carry no floor number. */
  function flatIdFromKey(key) {
    var g = /^([A-Z])G([0-9]+)$/.exec(key);
    if (g) return g[1] + "-G" + g[2];
    var m = /^([A-Z])([0-9]+)$/.exec(key);
    if (!m || m[2].length < 3) return key;
    return m[1] + "-" + m[2];
  }

  /* ---------- geometry ---------- */
  function bearing(a, b) { return Math.atan2(b.xy[1] - a.xy[1], b.xy[0] - a.xy[0]); }

  /* A curved road keeps its path in `shape`: points from its `from` end to its `to` end.
     A straight one is just its two ends. Turns, barricades and bay positions all follow
     the shape, so a bend reads as the road it is, not as the line between its ends. */
  function shapeOf(e) {
    if (e.shape && e.shape.length >= 2) return e.shape;
    var a = G.nodes[e.from] || NODE_AT[e.from], b = G.nodes[e.to] || NODE_AT[e.to];
    return [a.xy, b.xy];
  }
  // the points of a directed edge (or the part-aisle leg) in the order it is travelled
  function dirPts(pe) {
    var e = G.edges[pe.id] || pe, pts = shapeOf(e);
    return pe.a === e.from ? pts : pts.slice().reverse();
  }
  function bearingXY(p, q) { return Math.atan2(q[1] - p[1], q[0] - p[0]); }
  // which way the road faces leaving its start, and arriving at its end
  function departBearing(pe) {
    var pts = dirPts(pe), i = 1;
    while (i < pts.length - 1 && Math.abs(pts[i][0] - pts[0][0]) + Math.abs(pts[i][1] - pts[0][1]) < 0.01) i++;
    return bearingXY(pts[0], pts[i]);
  }
  function arriveBearing(pe) {
    var pts = dirPts(pe), n = pts.length - 1, i = n - 1;
    while (i > 0 && Math.abs(pts[i][0] - pts[n][0]) + Math.abs(pts[i][1] - pts[n][1]) < 0.01) i--;
    return bearingXY(pts[i], pts[n]);
  }
  /* A rounded corner turns along its curve, not at its junction (which sits half way round
     it): there the turn is read from the road either side of the curve, where it runs
     straight again. Everywhere else it is read at the junction itself, as before. */
  function plen(pts) { var L = 0; for (var i = 0; i + 1 < pts.length; i++) L += Math.hypot(pts[i + 1][0] - pts[i][0], pts[i + 1][1] - pts[i][1]); return L; }
  // which way the road runs at distance s along it
  function headingAlong(pts, s) {
    var acc = 0;
    for (var i = 0; i + 1 < pts.length; i++) {
      var l = Math.hypot(pts[i + 1][0] - pts[i][0], pts[i + 1][1] - pts[i][1]);
      if (l > 0.01 && (acc + l >= s || i + 2 === pts.length)) return bearingXY(pts[i], pts[i + 1]);
      acc += l;
    }
    return bearingXY(pts[0], pts[pts.length - 1]);
  }
  // how far either side of a rounded corner its curve reaches, in map units along this road
  function reach(n, pe, pts) {
    if (!n || !n.round || !n.round.w) return 0;
    var e = G.edges[pe.id] || pe, L = plen(pts);
    return Math.min(L, (n.round.w + 1) * L / (e.len || L));
  }
  function arriveHeading(pe) {
    var pts = dirPts(pe), w = reach(G.nodes[pe.b], pe, pts);
    return w ? headingAlong(pts, plen(pts) - w) : arriveBearing(pe);
  }
  function departHeading(pe) {
    var pts = dirPts(pe), w = reach(G.nodes[pe.a], pe, pts);
    return w ? headingAlong(pts, w) : departBearing(pe);
  }
  // how much a road bends along its own length, in degrees (right positive), leaving out the
  // part of a rounded corner the turn at that corner already counts
  function bendAlong(pe) {
    var pts = dirPts(pe);
    if (pts.length < 3) return 0;
    var L = plen(pts), s0 = reach(G.nodes[pe.a], pe, pts), s1 = L - reach(G.nodes[pe.b], pe, pts);
    var acc = 0, prev = null, sum = 0;
    for (var i = 0; i + 1 < pts.length; i++) {
      var l = Math.hypot(pts[i + 1][0] - pts[i][0], pts[i + 1][1] - pts[i][1]);
      if (l > 0.01 && acc + l > s0 && acc < s1) {
        var h = bearingXY(pts[i], pts[i + 1]);
        if (prev != null) { var d = (h - prev) * 180 / Math.PI; while (d > 180) d -= 360; while (d < -180) d += 360; sum += d; }
        prev = h;
      }
      acc += l;
    }
    return sum;
  }
  // the point a fraction t of the way along the road (by length), and the road from one end to it
  function pointAt(e, t) {
    var pts = shapeOf(e);
    if (pts.length === 2) return [pts[0][0] + (pts[1][0] - pts[0][0]) * t, pts[0][1] + (pts[1][1] - pts[0][1]) * t];
    var lens = [], L = 0;
    for (var i = 0; i + 1 < pts.length; i++) { var l = Math.hypot(pts[i + 1][0] - pts[i][0], pts[i + 1][1] - pts[i][1]); lens.push(l); L += l; }
    var want = t * L, acc = 0;
    for (var j = 0; j < lens.length; j++) {
      if (acc + lens[j] >= want) {
        var f = lens[j] ? (want - acc) / lens[j] : 0;
        return [pts[j][0] + (pts[j + 1][0] - pts[j][0]) * f, pts[j][1] + (pts[j + 1][1] - pts[j][1]) * f];
      }
      acc += lens[j];
    }
    return pts[pts.length - 1].slice();
  }
  function partTo(e, t, fromEnd) {
    var pts = shapeOf(e), P = pointAt(e, t);
    if (fromEnd === "to") { pts = pts.slice().reverse(); t = 1 - t; }
    if (pts.length === 2) return [pts[0], P];
    var lens = [], L = 0;
    for (var i = 0; i + 1 < pts.length; i++) { var l = Math.hypot(pts[i + 1][0] - pts[i][0], pts[i + 1][1] - pts[i][1]); lens.push(l); L += l; }
    var out = [pts[0]], acc = 0, want = t * L;
    for (var j = 0; j < lens.length && acc + lens[j] < want; j++) { acc += lens[j]; out.push(pts[j + 1]); }
    out.push(P);
    return out;
  }

  function turnBetween(prev, next) {
    if (!prev) return { deg: 0, kind: "start" };
    // Only THIS edge changing level counts as a level change.
    if (G.nodes[next.a].level !== G.nodes[next.b].level) return { deg: 0, kind: "level" };
    var p = G.nodes[prev.a], q = G.nodes[prev.b];
    // Just came off a ramp or lift: 2D bearing of the previous edge is meaningless.
    if (p.level !== q.level) return { deg: 0, kind: "straight" };
    // the way the road faces leaving the junction, against the way the last one faced arriving
    var d = (departHeading(next) - arriveHeading(prev)) * 180 / Math.PI;
    while (d > 180) d -= 360;
    while (d < -180) d += 360;
    var m = Math.abs(d);
    // SVG y grows downward, so a positive (clockwise) delta is a right turn.
    var kind = "straight";
    if (m >= UTURN_DEG) kind = "uturn";
    else if (m > STRAIGHT_DEG) kind = (d > 0 ? "right" : "left") + (m < 60 ? "-slight" : "");
    return { deg: d, kind: kind };
  }

  function stepCost(prev, next, mode) {
    var c = next.len;
    var t = turnBetween(prev, next);
    if (t.kind !== "straight" && t.kind !== "start") c += TURN_PENALTY;
    if (G.nodes[next.a].level !== G.nodes[next.b].level) c += LEVEL_PENALTY;
    if (next.type === "aisle" && mode === "car") c += 10;  // do not cut through aisles to save distance
    if (next.avoid) c += AVOID_PENALTY;
    return c;
  }

  /* ---------- barricades ----------
     A barricade is a line drawn across the plan. No route may cross it: not
     along a stretch it cuts, and not through a junction it runs over, from one
     side of it to the other. It blocks cars and people on foot unless it says
     walkers can pass. Pure geometry against the map as it is, so it needs no
     rebuild and keeps working when roads are redrawn. */
  var BARS = (((MAP.routing && MAP.routing.barricades) || [])).filter(function (b) {
    return b && b.level && Array.isArray(b.a) && Array.isArray(b.b);
  }).map(function (b) {
    // reach a few px past each end, so a line drawn to the kerb still closes the road
    var dx = b.b[0] - b.a[0], dy = b.b[1] - b.a[1], L = Math.sqrt(dx * dx + dy * dy) || 1, x = 4 / L;
    return { id: b.id, level: b.level, modes: b.foot ? ["car"] : ["car", "foot"],
             a: [b.a[0] - dx * x, b.a[1] - dy * x], b: [b.b[0] + dx * x, b.b[1] + dy * x] };
  });
  var BAR_TOL = 3;                    // a junction this close to a barricade is on it
  function orient(a, b, c) { return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0]); }
  function properCross(p1, p2, q1, q2) {
    var d1 = orient(q1, q2, p1), d2 = orient(q1, q2, p2), d3 = orient(p1, p2, q1), d4 = orient(p1, p2, q2);
    return ((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) && ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0));
  }
  function distToSeg(p, a, b) {
    var dx = b[0] - a[0], dy = b[1] - a[1], L2 = dx * dx + dy * dy || 1e-9;
    var t = Math.max(0, Math.min(1, ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / L2));
    var x = a[0] + t * dx - p[0], y = a[1] + t * dy - p[1];
    return Math.sqrt(x * x + y * y);
  }
  // does going from p to q on this level cross a barricade that stops this mode?
  function segBarred(level, p, q, mode) {
    for (var i = 0; i < BARS.length; i++) {
      var b = BARS[i];
      if (b.level === level && b.modes.indexOf(mode) >= 0 && properCross(p, q, b.a, b.b)) return true;
    }
    return false;
  }
  // passing through point x on this level, arriving from point p and leaving towards point q
  function passBarredAt(level, x, p, q, mode) {
    for (var i = 0; i < BARS.length; i++) {
      var b = BARS[i];
      if (b.level !== level || b.modes.indexOf(mode) < 0 || distToSeg(x, b.a, b.b) > BAR_TOL) continue;
      if (orient(b.a, b.b, p) * orient(b.a, b.b, q) < 0) return true;
    }
    return false;
  }
  function passBarred(n, p, q, mode) { return passBarredAt(n.level, n.xy, p, q, mode); }
  // does a run of points (a road, or part of one) cross a barricade anywhere along it?
  function ptsBarred(level, pts, mode) {
    for (var i = 0; i + 1 < pts.length; i++) if (segBarred(level, pts[i], pts[i + 1], mode)) return true;
    for (var j = 1; j + 1 < pts.length; j++) if (passBarredAt(level, pts[j], pts[j - 1], pts[j + 1], mode)) return true;
    return false;
  }
  var BARRED = {};                    // edge id -> { car: true, foot: true } when a barricade cuts it
  if (BARS.length) MAP.edges.forEach(function (e) {
    var a = NODE_AT[e.from], b = NODE_AT[e.to];
    if (!a || !b || a.level !== b.level) return;
    var pts = shapeOf(e);
    ["car", "foot"].forEach(function (m) {
      if (ptsBarred(a.level, pts, m)) (BARRED[e.id] = BARRED[e.id] || {})[m] = true;
    });
  });
  function usable(e, mode) { return e.mode.indexOf(mode) >= 0 && !(BARRED[e.id] && BARRED[e.id][mode]); }
  // may a route arrive on `prev` and leave on `next` (two directed edges meeting at a node)?
  function canPass(prev, next, mode) {
    if (!BARS.length || !prev) return true;
    var n = G.nodes[prev.b], p = G.nodes[prev.a], q = G.nodes[next.b];
    if (!n || !p || !q || p.level !== n.level || q.level !== n.level) return true;
    var arr = dirPts(prev), dep = dirPts(next);           // the road's own points either side of the junction
    return !passBarred(n, arr[arr.length - 2], dep[1], mode);
  }

  /* ---------- edge-based Dijkstra ---------- */
  function ekey(e) { return e.id + ":" + e.dir; }

  // noFirst: an edge id the path may not start on (no U-turn back up the ramp it just came down).
  // goalOk: when given, an arrival at the goal only counts if goalOk(arriving edge) says so.
  function findPath(startId, goalId, mode, noFirst, goalOk) {
    if (!G.out[startId]) return null;
    var dist = {}, prevOf = {}, seen = {}, pq = [];

    G.out[startId].filter(function (e) { return usable(e, mode) && e.id !== noFirst; }).forEach(function (e) {
      var k = ekey(e);
      dist[k] = stepCost(null, e, mode);
      pq.push({ e: e, d: dist[k], p: null });
    });

    var best = null;
    while (pq.length) {
      pq.sort(function (x, y) { return x.d - y.d; });
      var cur = pq.shift();
      var k = ekey(cur.e);
      if (seen[k]) continue;
      seen[k] = true;
      prevOf[k] = cur.p;

      if (cur.e.b === goalId && (!goalOk || goalOk(cur.e))) { best = cur.e; break; }

      G.out[cur.e.b].filter(function (e) { return usable(e, mode); }).forEach(function (nx) {
        if (nx.id === cur.e.id) return;                    // no immediate backtrack
        if (!canPass(cur.e, nx, mode)) return;             // never through a barricade
        var nk = ekey(nx), nd = cur.d + stepCost(cur.e, nx, mode);
        if (dist[nk] === undefined || nd < dist[nk]) {
          dist[nk] = nd;
          pq.push({ e: nx, d: nd, p: cur.e });
        }
      });
    }
    if (!best) return null;

    var chain = [], e = best;
    while (e) { chain.unshift(e); e = prevOf[ekey(e)]; }
    return { edges: chain, cost: dist[ekey(best)] };
  }

  /* ---------- path -> human steps ---------- */
  var GLYPH = {
    start: "●", straight: "↑", "left-slight": "↖", left: "←",
    "right-slight": "↗", right: "→", uturn: "↺", level: "⇅"
  };

  function defaultText(e, turn, len) {
    var d = {
      straight: "Continue straight", left: "Turn left", right: "Turn right",
      "left-slight": "Bear left", "right-slight": "Bear right",
      uturn: "Turn back", start: "Set off", level: "Change level"
    }[turn.kind] || "Continue";
    // The distance in the words has to be the distance actually travelled. On
    // the final leg into a slot that is only part of the aisle, so it is passed
    // in - taking e.len there told the visitor to drive past their own bay.
    // e is only read for its length, so a caller that already knows the
    // distance - a merged run, or the part-aisle leg into a slot - passes it
    // in and may leave e null.
    return d + " for about " + Math.round(len == null ? e.len : len) + " m.";
  }

  /* A directed stretch as the routes editor names it: "<edge key>|fwd" or "|rev". */
  function dirKey(pe) {
    var e = G.edges[pe.id];
    if (!e || !e.key) return null;
    var first = e.key.split("~")[0];
    var a = G.nodes[pe.a];
    return e.key + "|" + (((a && a.key) || pe.a) === first ? "fwd" : "rev");
  }
  /* Words written for one particular turn: arriving on `prev`, leaving on `next`. */
  function turnText(prev, next) {
    if (!prev) return null;
    var k1 = dirKey(prev), k2 = dirKey(next);
    return (k1 && k2 && G.turns[k1 + ">" + k2]) || null;
  }
  var TURN_WORD = {
    straight: "Continue straight", left: "Turn left", right: "Turn right",
    "left-slight": "Bear left", "right-slight": "Bear right",
    uturn: "Turn back", start: "Set off", level: "Go"
  };
  /* {turn} and {dist} let one sentence serve every way into a stretch: the
     turn is worked out from where the visitor comes from, the distance from
     how far this step really runs. */
  var PLACEHOLDER = /\{(turn|dist)\}/i;
  function fillText(tpl, kind, len) {
    return tpl.replace(/\{turn\}/gi, TURN_WORD[kind] || "Continue")
              .replace(/\{dist\}/gi, "about " + Math.round(len) + " m");
  }

  function toSteps(path, dest) {
    var steps = [];

    path.edges.forEach(function (e, i) {
      var turn = turnBetween(path.edges[i - 1] || null, e);
      // A two-way edge is walked in both directions, but "keep the fountain on
      // your left" is only true one way round. Use the authored reverse text;
      // an empty one is a deliberate "say it automatically" and does not fall back.
      // Words written for this exact turn win over both.
      var text = turnText(path.edges[i - 1] || null, e) ||
                 (e.dir === -1 && e.instructionRev != null ? e.instructionRev : e.instruction);

      // Merge unlabelled straight runs - never say "continue straight" five times.
      if (!text && turn.kind === "straight" && steps.length) {
        var last = steps[steps.length - 1];
        last.len += e.len;
        last.merged++;
        last.bendDeg = (last.bendDeg || 0) + turn.deg + bendAlong(e);
        // The distance is IN the sentence, so a run that grew has to say so.
        // Without this a six-edge aisle read "set off for about 51 m" with
        // 183 m on the chip beside it - two numbers for one leg, one of them
        // the distance to somewhere the visitor was not going.
        if (last.auto) last.text = defaultText(null, last.turn, last.len);
        return;
      }
      steps.push({
        glyph: GLYPH[turn.kind] || "↑",
        kind: turn.kind,
        text: text || defaultText(e, turn),
        tpl: text && PLACEHOLDER.test(text) ? text : null,
        // Authored text is the surveyor's words and is never rewritten.
        auto: !text, turn: turn,
        len: e.len, merged: 0, bendDeg: bendAlong(e),
        edge: i,          // index of the step's first path edge, so a map can draw each step
        level: G.nodes[e.b].level,
        photo: (e.dir === -1 && e.photoRev != null ? e.photoRev : e.photo) || null
      });
    });

    // A run along a road that bends a long way round says so: "continue straight" would not do.
    steps.forEach(function (st) {
      var b = st.bendDeg || 0;
      delete st.bendDeg;
      if (!st.auto || Math.abs(b) < BEND_DEG || (st.kind !== "straight" && st.kind !== "start")) return;
      st.bend = b > 0 ? "right" : "left";
      st.text = (st.kind === "start" ? "Set off and follow" : "Follow") + " the road round to the " + st.bend +
                " for about " + Math.round(st.len) + " m.";
    });

    if (dest.kind === "slot") {
      var s = dest.slot, ae = G.edges[s.edge];
      var lastEdge = path.edges[path.edges.length - 1];
      var rev = dest.approach === "to";       // reached from the far end, because a barricade closes the near one

      // The final leg runs ALONG the aisle edge, which the graph search stops short of.
      // Without this the visitor is never told to turn into the aisle at all.
      if (!lastEdge || lastEdge.id !== ae.id) {
        var pseudo = rev ? { id: ae.id, a: ae.to, b: ae.from, len: ae.len, dir: -1 }
                         : { id: ae.id, a: ae.from, b: ae.to, len: ae.len, dir: 1 };
        var at = turnBetween(lastEdge, pseudo);
        var own = rev ? (ae.instructionRev != null ? ae.instructionRev : ae.instruction) : ae.instruction;
        var legText = turnText(lastEdge, pseudo) || own;
        var legLen = ae.len * (rev ? 1 - s.t : s.t);
        steps.push({
          glyph: GLYPH[at.kind] || "↑", kind: at.kind, turn: at,
          text: legText || defaultText(ae, at, legLen),
          tpl: legText && PLACEHOLDER.test(legText) ? legText : null,
          len: Math.round(legLen), merged: 0, edge: path.edges.length,   // the part-aisle leg
          level: G.nodes[ae.to].level,
          photo: (rev ? (ae.photoRev != null ? ae.photoRev : ae.photo) : ae.photo) || null
        });
      }
      steps.push({
        glyph: "⚑", kind: "arrive", final: true,
        text: arrivalText(s, rev),
        len: 0, merged: 0,
        level: G.nodes[ae.to].level, photo: null
      });
    } else {
      steps.push({
        glyph: "⚑", kind: "arrive", final: true,
        text: dest.flat
          ? "You have arrived at " + nodeLabel(dest.node) + ". Take the lift to floor " +
            dest.flat.floor + " for flat " + dest.flat.id + "."
          : "You have arrived at " + nodeLabel(dest.node) + ".",
        len: 0, merged: 0, level: dest.node.level, photo: null
      });
    }
    // placeholders are filled last, once merged runs know their full length
    steps.forEach(function (st) { if (st.tpl) st.text = fillText(st.tpl, st.kind, st.len); });
    return steps;
  }

  /* ---------- destination resolution ---------- */
  /* The last line a visitor reads is the one that has to be right. A run-built
     slot carries a written side and a pillar; one placed by hand carries +1/-1
     from which side of the aisle was clicked, and no pillar at all. Print what
     exists and nothing else - "on your 1, beside pillar null" is worse than
     silence. The final leg is always driven from the edge's `from` to its `to`,
     and in screen coordinates that makes +1 the driver's left. */
  function sideWord(side) {
    if (side === "left" || side === "right") return side;
    if (side === 1)  return "left";
    if (side === -1) return "right";
    return null;
  }
  /* The number is what is painted on the wall, so it leads; the flat is how
     you know the number is the right one. "s-359" is neither - it is the key
     this file happens to use, and it never belongs in front of a driver. */
  function slotNumber(id) { return String(id).replace(/^s-/, ""); }
  function arrivalText(s, reversed) {
    var who  = s.flat ? "This is " + s.flat + "'s parking, bay " + slotNumber(s.id)
                      : "This is visitor bay " + slotNumber(s.id);
    // driven the other way along the aisle, the bay is on the other hand
    var side = sideWord(reversed && typeof s.side === "number" ? -s.side : s.side);
    var mark = s.landmark ? ", beside pillar " + s.landmark : "";
    return who + (side ? ", on your " + side : "") + mark + ".";
  }

  function resolveDest(id) {
    if (G.slots[id]) {
      return { kind: "slot", slot: G.slots[id], node: G.nodes[G.edges[G.slots[id].edge].from] };
    }

    // "A-1503@lobby" forces the lobby even when a slot is on record.
    var raw = String(id);
    var forceLobby = /@lobby$/i.test(raw);
    var flat = G.flats[flatIdFromKey(normFlat(raw.replace(/@lobby$/i, "")))];
    if (flat) {
      if (!forceLobby && flat.slots.length) return resolveDest(flat.slots[0]);
      if (!forceLobby && flat.park && G.nodes[flat.park])
        return { kind: "node", node: G.nodes[flat.park], flat: flat, approx: true };
      if (G.nodes[flat.lobby]) return { kind: "node", node: G.nodes[flat.lobby], flat: flat };
      // The flat exists on the block plan but nothing on the map knows where
      // it parks. Saying so beats routing confidently to nowhere.
      return { kind: "unlocated", flat: flat };
    }

    if (G.nodes[id]) return { kind: "node", node: G.nodes[id] };
    return null;
  }

  function route(startId, destId, mode) {
    var dest = resolveDest(destId);
    if (!dest) return { error: "Unknown destination." };
    if (dest.kind === "unlocated")
      return { error: "Flat " + dest.flat.id + " is on the block plan, but its parking " +
                      "is not on the map yet." };
    // A bay is a point part-way along an aisle, not a node, so it cannot be
    // handed to the graph search as-is. Start from the head of its aisle - the
    // same place resolveDest() lands a bay used as a DESTINATION. Without this
    // a bay start returns "no route available", which reads as a broken map
    // rather than as an id the router never accepted.
    // A bay on a stretch closed to this way of travelling cannot be reached that way: the last
    // leg is driven along the bay's own aisle, so the aisle itself has to allow it.
    if (dest.kind === "slot") {
      var ae0 = G.edges[dest.slot.edge];
      if (ae0 && (ae0.mode || []).indexOf(mode) < 0)
        return { error: "This bay is on a stretch that is closed to " + (mode === "car" ? "cars" : "walking") + "." };
    }
    var from = resolveDest(startId);
    var startNode = from && from.node ? from.node.id : startId;
    // Starting at a bay (walking from your car), leave it by the end of its aisle
    // that no barricade separates it from.
    if (from && from.kind === "slot" && BARS.length) {
      var se = G.edges[from.slot.edge], SA = G.nodes[se.from], SB = G.nodes[se.to];
      if (ptsBarred(SA.level, partTo(se, from.slot.t, "from"), mode)) {
        if (ptsBarred(SB.level, partTo(se, from.slot.t, "to"), mode)) return { error: "That bay is cut off by a barricade." };
        startNode = SB.id;
      }
    }
    // Where the search has to get to. A node is itself. A bay is reached along its
    // aisle from the aisle's start; when a barricade stands between that end and
    // the bay, from the other end instead (if the aisle is not one-way); when both
    // are closed, it cannot be reached at all.
    var goals = [];
    if (dest.kind === "slot") {
      var ae = G.edges[dest.slot.edge], A = G.nodes[ae.from], B = G.nodes[ae.to];
      var legA = partTo(ae, dest.slot.t, "from"), legB = partTo(ae, dest.slot.t, "to");
      var arrive = function (N, leg) {
        return BARS.length ? function (e) { var ap = dirPts(e); return !passBarred(N, ap[ap.length - 2], leg[1], mode); } : null;
      };
      if (!ptsBarred(A.level, legA, mode)) goals.push({ node: A, approach: "from", ok: arrive(A, legA) });
      if (BARS.length && !ae.oneway && !ptsBarred(B.level, legB, mode)) goals.push({ node: B, approach: "to", ok: arrive(B, legB) });
      if (!goals.length) return { error: "This bay is cut off by a barricade." };
    } else goals.push({ node: dest.node, approach: null, ok: null });

    var path = null, goal = null;
    var via = entranceFor(dest);
    for (var gi = 0; gi < goals.length && !path; gi++) {
      goal = goals[gi];
      // Which ramp a block's cars take is a rule, not a distance: a car arriving at
      // ground level for a block with an entrance set goes through that ramp's foot
      // (an underground node), and from there may not turn straight back up it.
      if (via && mode === "car" && G.nodes[startNode] && G.nodes[startNode].level === "G" &&
          G.nodes[via] && via !== startNode) {
        var p1 = findPath(startNode, via, mode);
        var p2 = p1 && (via === goal.node.id ? { edges: [], cost: 0 }
                                             : findPath(via, goal.node.id, mode, p1.edges[p1.edges.length - 1].id, goal.ok));
        if (p1 && p2) path = { edges: p1.edges.concat(p2.edges), cost: p1.cost + p2.cost, via: via };
      }
      if (!path) path = findPath(startNode, goal.node.id, mode, null, goal.ok);
    }
    if (!path) return { error: "No " + mode + " route available to that destination." };
    if (goal.approach) dest = Object.assign({}, dest, { node: goal.node, approach: goal.approach });
    return { dest: dest, path: path, steps: toSteps(path, dest), cost: path.cost };
  }
  /* The entrance rule that applies to a destination: by block letter for a
     flat's bay or lobby, "visitor" for visitor bays and visitor parking. */
  function entranceFor(dest) {
    var E = MAP.routing && MAP.routing.entrances;
    if (!E || !dest) return null;
    var g = null;
    if (dest.kind === "slot") g = dest.slot.flat ? String(dest.slot.flat).split("-")[0] : "visitor";
    else if (dest.flat) g = dest.flat.block;
    else if (dest.node && /visitor/i.test(dest.node.name || dest.node.id)) g = "visitor";
    return (g && E[g]) || null;
  }

  /* ---------- publish-time validation ----------
     Worth more than any pathfinding cleverness: this is what stops
     a bad edge from silently routing someone into a wall. */
  function validate() {
    var issues = [];
    var anchors = MAP.nodes.filter(function (n) { return n.anchor; });
    var dests   = MAP.nodes.filter(function (n) { return n.dest; });

    MAP.nodes.forEach(function (n) {
      var hasOut = G.out[n.id] && G.out[n.id].length;
      var hasIn  = MAP.edges.some(function (e) { return e.to === n.id; });
      if (!hasOut && !hasIn) issues.push({ sev: "err", msg: "Orphan node: " + n.id });
    });

    var DIRECTIONAL = /(^|[^a-z])(left|right|clockwise|anticlockwise|counter-?clockwise)([^a-z]|$)/i;
    MAP.edges.forEach(function (e) {
      if (!G.nodes[e.from] || !G.nodes[e.to]) issues.push({ sev: "err", msg: "Edge " + e.id + " references a missing node" });
      if (!("instruction" in e)) issues.push({ sev: "warn", msg: "Edge " + e.id + " has no instruction field" });
      // Directional wording on a two-way edge is wrong in one of the two directions.
      if (!e.oneway && e.instruction && DIRECTIONAL.test(e.instruction) && e.instructionRev == null)
        issues.push({ sev: "warn", msg: "Edge " + e.id + ' says "' + e.instruction +
          '" but is two-way - it needs an instructionRev, or it is wrong going the other way' });
    });

    anchors.forEach(function (a) {
      dests.forEach(function (d) {
        // A placard can sit ON a destination (an entry that is also somewhere
        // you might be sent). You are already there; that is not unreachable.
        if (a.id === d.id) return;
        if (!findPath(a.id, d.id, "car") && !findPath(a.id, d.id, "foot"))
          issues.push({ sev: "err", msg: "Unreachable: " + a.id + " -> " + d.id });
      });
    });

    Object.keys(G.slots).forEach(function (id) {
      if (!G.edges[G.slots[id].edge]) issues.push({ sev: "err", msg: "Slot " + id + " on missing edge" });
    });

    // Reverse reachability: can a car actually get back OUT of every aisle?
    // Derived from the graph, not hardcoded - a new level gets checked automatically.
    MAP.edges.filter(function (e) { return e.type === "aisle"; }).forEach(function (e) {
      [e.from, e.to].forEach(function (end) {
        var canLeave = anchors.some(function (t) { return findPath(end, t.id, "car"); });
        if (!canLeave) issues.push({ sev: "err", msg: "Dead end - no way out of " + end + " by car" });
      });
    });

    var seenSlot = {};
    (MAP.slots || []).forEach(function (s) {
      if (!s.id) issues.push({ sev: "err", msg: "A slot has no id" });
      else if (seenSlot[s.id]) issues.push({ sev: "err", msg: "Slot " + s.id + " is defined twice" });
      seenSlot[s.id] = 1;
      if (!G.edges[s.edge])
        issues.push({ sev: "err", msg: "Slot " + s.id + " sits on missing edge " + s.edge });
      if (!(s.t >= 0 && s.t <= 1))
        issues.push({ sev: "err", msg: "Slot " + s.id + " is off the end of its aisle" });
      if (s.flat && !G.flats[s.flat])
        issues.push({ sev: "err", msg: "Slot " + s.id + " is allotted to " + s.flat +
                     " - no such flat in the block plan" });
      // An unnamed bay is either a visitor bay (fine, say so) or work in
      // progress (worth a nudge). The flag is what tells them apart.
      if (!s.flat && !s.visitor)
        issues.push({ sev: "warn", msg: "Slot " + s.id + " has no flat against it yet" });
    });

    /* ---- the allotment sheet is the error-prone human input; check it hard ---- */
    var claimed = {};
    MAP.allotments.forEach(function (a) {
      if (!G.flats[a.flat])
        issues.push({ sev: "err", msg: "Allotment for " + a.flat + " - no such flat in the block plan" });
      a.slots.forEach(function (sid) {
        if (!G.slots[sid])
          issues.push({ sev: "err", msg: "Flat " + a.flat + " allotted unknown slot " + sid });
        else if (claimed[sid])
          issues.push({ sev: "err", msg: "Slot " + sid + " allotted twice: " + claimed[sid] + " and " + a.flat });
        else claimed[sid] = a.flat;
      });
    });

    MAP.blocks.forEach(function (b) {
      // Declaring the roster before the lobbies are surveyed is the normal
      // order of work, so this is a warning. It only becomes wrong if it ships.
      if (!b.lobby)
        issues.push({ sev: "warn", msg: "Block " + b.id + " has no lobby node yet - its flats " +
                     "fall back to whatever parking zone lists them" });
      else if (!G.nodes[b.lobby])
        issues.push({ sev: "err", msg: "Block " + b.id + " lobby node '" + b.lobby + "' does not exist" });
    });

    // The routes editor's rules must still find what they were written for.
    var R = MAP.routing;
    if (R) {
      var EK = {};
      MAP.edges.forEach(function (e) { if (e.key) EK[e.key] = e; });
      Object.keys(R.edges || {}).forEach(function (k) {
        if (!EK[k]) issues.push({ sev: "warn", msg: "Routing rule for stretch " + k + " matches no stretch on the map" });
      });
      Object.keys(R.turns || {}).forEach(function (k) {
        var parts = k.split(">");
        if (parts.length !== 2 || parts.some(function (x) { return !EK[x.split("|")[0]]; }))
          issues.push({ sev: "warn", msg: "Turn wording " + k + " refers to a stretch that is not on the map" });
      });
      MAP.edges.forEach(function (e) {
        if (!e.shape) return;
        var a = NODE_AT[e.from], b = NODE_AT[e.to], f = e.shape[0], l = e.shape[e.shape.length - 1];
        if (a && b && (Math.hypot(f[0] - a.xy[0], f[1] - a.xy[1]) > 1 || Math.hypot(l[0] - b.xy[0], l[1] - b.xy[1]) > 1))
          issues.push({ sev: "warn", msg: "The curve of stretch " + e.id + " does not start and end at its junctions" });
      });
      (R.barricades || []).forEach(function (b) {
        if (!MAP.levels.some(function (l) { return l.id === b.level; }))
          issues.push({ sev: "warn", msg: "Barricade " + b.id + " is on a level the map does not have" });
      });
      Object.keys(R.entrances || {}).forEach(function (g) {
        if (!G.nodes[R.entrances[g]])
          issues.push({ sev: "err", msg: "Entrance for " + g + " goes through '" + R.entrances[g] + "', which is not on the map" });
      });
    }

    var slots = Object.keys(G.slots).length;
    var flats = G.flatIndex.length;
    var mapped = G.flatIndex.filter(function (id) { return G.flats[id].slots.length; }).length;

    issues.push({ sev: "info", msg: flats + " flats declared across " + MAP.blocks.length + " blocks" });
    issues.push({ sev: "info", msg: slots + " slots indexed, " + (slots - Object.keys(claimed).length) + " unallotted" });
    if (flats > slots)
      issues.push({ sev: "warn", msg: flats + " flats but only " + slots + " slots mapped - at least " +
        (flats - slots) + " flats cannot have one. The remaining parking levels still need surveying." });
    issues.push({ sev: "warn", msg: (flats - mapped) + " flats have no allotted slot on record; " +
      "they route to their block lobby instead." });
    return issues;
  }


  buildGraph();

  return {
    G: G, route: route, validate: validate, resolveDest: resolveDest,
    findPath: findPath, toSteps: toSteps, turnBetween: turnBetween, dirKey: dirKey,
    entranceFor: entranceFor, fillText: fillText,
    canPass: canPass, isBarred: function (id, mode) { return !!(BARRED[id] && BARRED[id][mode]); },
    dirPts: dirPts, edgePts: function (id) { return shapeOf(G.edges[id]); },
    pointAt: function (id, t) { return pointAt(G.edges[id], t); },
    partTo: function (id, t, fromEnd) { return partTo(G.edges[id], t, fromEnd); },
    normFlat: normFlat, flatIdFromKey: flatIdFromKey,
    slotNumber: slotNumber, nodeLabel: nodeLabel, isLift: isLift
  };
}

if (typeof module !== "undefined" && module.exports) module.exports = { createEngine: createEngine };
