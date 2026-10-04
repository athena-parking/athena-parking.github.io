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

  const G = { nodes: {}, slots: {}, out: {}, edges: {}, flats: {}, flatIndex: [] };

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

  function turnBetween(prev, next) {
    if (!prev) return { deg: 0, kind: "start" };
    // Only THIS edge changing level counts as a level change.
    if (G.nodes[next.a].level !== G.nodes[next.b].level) return { deg: 0, kind: "level" };
    var p = G.nodes[prev.a], q = G.nodes[prev.b], r = G.nodes[next.b];
    // Just came off a ramp or lift: 2D bearing of the previous edge is meaningless.
    if (p.level !== q.level) return { deg: 0, kind: "straight" };
    var d = (bearing(q, r) - bearing(p, q)) * 180 / Math.PI;
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
    return c;
  }

  /* ---------- edge-based Dijkstra ---------- */
  function ekey(e) { return e.id + ":" + e.dir; }

  function findPath(startId, goalId, mode) {
    if (!G.out[startId]) return null;
    var dist = {}, prevOf = {}, seen = {}, pq = [];

    G.out[startId].filter(function (e) { return e.mode.indexOf(mode) >= 0; }).forEach(function (e) {
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

      if (cur.e.b === goalId) { best = cur.e; break; }

      G.out[cur.e.b].filter(function (e) { return e.mode.indexOf(mode) >= 0; }).forEach(function (nx) {
        if (nx.id === cur.e.id) return;                    // no immediate backtrack
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

  function toSteps(path, dest) {
    var steps = [];

    path.edges.forEach(function (e, i) {
      var turn = turnBetween(path.edges[i - 1] || null, e);
      // A two-way edge is walked in both directions, but "keep the fountain on
      // your left" is only true one way round. Use the authored reverse text.
      var text = (e.dir === -1 && e.instructionRev) ? e.instructionRev : e.instruction;

      // Merge unlabelled straight runs - never say "continue straight" five times.
      if (!text && turn.kind === "straight" && steps.length) {
        var last = steps[steps.length - 1];
        last.len += e.len;
        last.merged++;
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
        // Authored text is the surveyor's words and is never rewritten.
        auto: !text, turn: turn,
        len: e.len, merged: 0,
        edge: i,          // index of the step's first path edge, so a map can draw each step
        level: G.nodes[e.b].level,
        photo: e.photo || null
      });
    });

    if (dest.kind === "slot") {
      var s = dest.slot, ae = G.edges[s.edge];
      var lastEdge = path.edges[path.edges.length - 1];

      // The final leg runs ALONG the aisle edge, which the graph search stops short of.
      // Without this the visitor is never told to turn into the aisle at all.
      if (!lastEdge || lastEdge.id !== ae.id) {
        var pseudo = { id: ae.id, a: ae.from, b: ae.to, len: ae.len };
        var at = turnBetween(lastEdge, pseudo);
        steps.push({
          glyph: GLYPH[at.kind] || "↑", kind: at.kind,
          text: ae.instruction || defaultText(ae, at, ae.len * s.t),
          len: Math.round(ae.len * s.t), merged: 0, edge: path.edges.length,   // the part-aisle leg
          level: G.nodes[ae.to].level, photo: ae.photo || null
        });
      }
      steps.push({
        glyph: "⚑", kind: "arrive", final: true,
        text: arrivalText(s),
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
  function arrivalText(s) {
    var who  = s.flat ? "This is " + s.flat + "'s parking, bay " + slotNumber(s.id)
                      : "This is visitor bay " + slotNumber(s.id);
    var side = sideWord(s.side);
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
    var from = resolveDest(startId);
    var path = findPath(from && from.node ? from.node.id : startId, dest.node.id, mode);
    if (!path) return { error: "No " + mode + " route available to that destination." };
    return { dest: dest, path: path, steps: toSteps(path, dest), cost: path.cost };
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
      if (!e.oneway && e.instruction && DIRECTIONAL.test(e.instruction) && !e.instructionRev)
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
    findPath: findPath, toSteps: toSteps,
    normFlat: normFlat, flatIdFromKey: flatIdFromKey,
    slotNumber: slotNumber, nodeLabel: nodeLabel, isLift: isLift
  };
}

if (typeof module !== "undefined" && module.exports) module.exports = { createEngine: createEngine };
