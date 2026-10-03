/* ============================================================
   Athena Parking — service worker

   Purpose: the placards now all sit at the threshold of a dead zone.
   Someone scans where there is signal, then walks or drives somewhere
   there is none. This keeps a copy so the app still opens down there.

   Two strategies on purpose:

     shell (index.html, engine.js, icons)  -> cache first
         Rarely changes and must open instantly. A stale shell is
         harmless; a slow one is not.

     data (map.js, scanpoints.js)          -> network first, short timeout
         This is the map itself. Serving yesterday's map to someone
         who HAS signal would be a silent wrong-turn bug, so we always
         prefer the live copy and fall back to cache only when the
         network genuinely is not there.
   ============================================================ */

const VERSION    = "athena-3424065737";
const DATA_FILES = ["map.js", "scanpoints.js"];
const NET_TIMEOUT = 2500;

const PRECACHE = [
  "./",
  "./index.html",
  "./engine.js",
  "./map.js",
  "./scanpoints.js",
  "./manifest.webmanifest"
];

/* The level backdrops are named inside map.js, not here - hard-coding a
   filename would silently stop caching the plan the day it is renamed, and
   the failure only shows up offline, where nobody can fix it. Read the
   published map and cache whatever it actually points at. */
function planUrls(cache) {
  return cache.match("./map.js")
    .then(r => r ? r.text() : "")
    .then(t => {
      const seen = new Set();
      let m;
      // Floor plans are NOT cached any more: the multi-map view they were the
      // backdrop for is gone, and a megabyte of CAD sheets nothing renders is a
      // megabyte the visitor downloads at the gate for nothing.
      // Turn photographs matter more than anything else here: the whole reason
      // one exists is a junction that words describe badly, and that junction is
      // underground where there is no network to fetch it from.
      const pic = /"photo"\s*:\s*"([^"]+)"/g;
      while ((m = pic.exec(t))) seen.add("./photos/" + m[1] + ".jpg");
      return [...seen];
    })
    .catch(() => []);
}

/* ---------- install ---------- */
self.addEventListener("install", event => {
  event.waitUntil(
    caches.open(VERSION)
      // cache.add() is allowed to satisfy itself from the browser HTTP cache,
      // which would bake a STALE copy into the offline cache at install time -
      // the one place staleness is unrecoverable. Force a real network read.
      // Individually, so one missing optional file cannot fail the whole install.
      .then(cache => Promise.all(PRECACHE.map(u =>
        cache.add(new Request(u, { cache: "reload" })).catch(() => null)))
        .then(() => planUrls(cache))
        .then(urls => Promise.all(urls.map(u =>
          cache.add(new Request(u, { cache: "reload" })).catch(() => null)))))
      .then(() => self.skipWaiting())
  );
});

/* ---------- activate: drop caches from older versions ---------- */
self.addEventListener("activate", event => {
  event.waitUntil(
    caches.keys()
      .then(keys => Promise.all(keys.filter(k => k !== VERSION).map(k => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

/* ---------- helpers ---------- */
function isData(url) {
  return DATA_FILES.some(f => url.pathname.endsWith("/" + f) || url.pathname === "/" + f);
}

function timedFetch(request, ms) {
  return new Promise(resolve => {
    let settled = false;
    const done = v => { if (!settled) { settled = true; resolve(v); } };
    setTimeout(() => done(null), ms);
    fetch(request).then(r => done(r && r.ok ? r : null)).catch(() => done(null));
  });
}

/* Serve the cached shell for any navigation. The query string differs per
   placard (?s=G1, ?s=TD) but the HTML is identical, so match without it. */
async function handleNavigation(request) {
  const cache = await caches.open(VERSION);

  const fresh = timedFetch(request, NET_TIMEOUT).then(r => {
    if (r) cache.put("./index.html", r.clone());
    return r;
  });

  const cached = await cache.match("./index.html", { ignoreSearch: true });
  if (cached) { fresh.catch(() => {}); return cached; }

  const net = await fresh;
  if (net) return net;

  return new Response(
    "<!doctype html><meta charset=utf-8><title>Offline</title>" +
    "<body style=\"font:16px system-ui;padding:2rem;background:#05070f;color:#f3f6fc\">" +
    "<h1>No saved map yet</h1><p>This placard could not be opened because there is no " +
    "connection and nothing is saved on this phone yet. Move to where there is signal " +
    "and scan again.</p>",
    { status: 503, headers: { "Content-Type": "text/html; charset=utf-8" } }
  );
}

/* The map data: prefer live, fall back to saved. */
async function handleData(request) {
  const cache = await caches.open(VERSION);
  const net = await timedFetch(request, NET_TIMEOUT);
  if (net) { cache.put(request, net.clone()); return net; }
  const cached = await cache.match(request, { ignoreSearch: true });
  return cached || Response.error();
}

/* Floor-plan images are large and immutable; once saved, always serve saved. */
/* Everything else: instant from cache, refreshed quietly for next time. */
async function handleShell(request) {
  const cache = await caches.open(VERSION);
  const cached = await cache.match(request, { ignoreSearch: true });

  const update = fetch(request)
    .then(r => { if (r && r.ok) cache.put(request, r.clone()); return r; })
    .catch(() => null);

  if (cached) { update.catch(() => {}); return cached; }
  const net = await update;
  return net || Response.error();
}

/* ---------- routing ---------- */
self.addEventListener("fetch", event => {
  const request = event.request;
  if (request.method !== "GET") return;

  const url = new URL(request.url);
  if (url.origin !== self.location.origin) return;

  // The admin surface must never be cached or served from cache.
  if (url.pathname.startsWith("/api/") ||
      url.pathname.endsWith("/admin.html") ||
      url.pathname.endsWith("/editor.html")) return;

  if (request.mode === "navigate") { event.respondWith(handleNavigation(request)); return; }
  if (isData(url))                 { event.respondWith(handleData(request));       return; }
  event.respondWith(handleShell(request));
});
