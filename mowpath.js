/*!
 * MowPath: coverage path planning for lawns. No dependencies.
 *
 * Input is a lawn outline, obstacle outlines (house, beds, trees), a mower deck
 * width and a few preferences. Output is a route that mows every reachable part
 * of the lawn: perimeter laps first, then parallel stripes at the angle that
 * minimises estimated mowing time.
 *
 * How it works
 *  1. Project lat/lng to local metres and rasterise the lawn (obstacles cut out).
 *  2. Build a signed distance field. Contours of that field are exact offset
 *     curves, so perimeter laps and "keep the deck off the wall" margins fall
 *     out of one primitive and work for any concave shape.
 *  3. For each candidate stripe angle, sample evenly spaced stripes, split them
 *     where obstacles interrupt them, and group the pieces into boustrophedon
 *     cells (chains of stripes that connect one-to-one).
 *  4. Order the cells (exact dynamic programming up to 8 cells, greedy beyond),
 *     choosing entry side and direction for each, with transit paths that stay
 *     inside the lawn.
 *  5. Score each angle by time = distance / speed + turning, keep the best, then
 *     verify by stamping the deck footprint over the final route.
 */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.MowPath = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  const DEG = Math.PI / 180;
  const R_EARTH = 6378137;
  const INF = 1e9;
  const tick = () => new Promise((r) => setTimeout(r, 0));
  const now = () => (typeof performance !== 'undefined' ? performance.now() : Date.now());
  const clamp = (v, a, b) => Math.max(a, Math.min(b, v));

  /* ---------- geometry helpers ---------- */

  function projection(lat0, lng0) {
    const kx = DEG * R_EARTH * Math.cos(lat0 * DEG);
    const ky = DEG * R_EARTH;
    return {
      toXY: (lat, lng) => [(lng - lng0) * kx, (lat - lat0) * ky],
      toLL: (x, y) => [lat0 + y / ky, lng0 + x / kx],
    };
  }

  function polyArea(p) {
    let a = 0;
    for (let i = 0, n = p.length; i < n; i++) {
      const q = p[(i + 1) % n];
      a += p[i][0] * q[1] - q[0] * p[i][1];
    }
    return a / 2;
  }

  function bboxOf(pts) {
    let minx = Infinity, miny = Infinity, maxx = -Infinity, maxy = -Infinity;
    for (const [x, y] of pts) {
      if (x < minx) minx = x;
      if (x > maxx) maxx = x;
      if (y < miny) miny = y;
      if (y > maxy) maxy = y;
    }
    return { minx, miny, maxx, maxy };
  }

  function pointInPoly(x, y, poly) {
    let inside = false;
    for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
      const [xi, yi] = poly[i], [xj, yj] = poly[j];
      if ((yi > y) !== (yj > y) && x < ((xj - xi) * (y - yi)) / (yj - yi) + xi) inside = !inside;
    }
    return inside;
  }

  function simplifyOpen(pts, tol) {
    const n = pts.length;
    if (n < 3) return pts.slice();
    const keep = new Uint8Array(n);
    keep[0] = keep[n - 1] = 1;
    const stack = [[0, n - 1]];
    while (stack.length) {
      const [i, j] = stack.pop();
      const [x1, y1] = pts[i], [x2, y2] = pts[j];
      const dx = x2 - x1, dy = y2 - y1, L = Math.hypot(dx, dy);
      let md = 0, mi = -1;
      for (let k = i + 1; k < j; k++) {
        const d = L > 1e-12
          ? Math.abs(dy * (pts[k][0] - x1) - dx * (pts[k][1] - y1)) / L
          : Math.hypot(pts[k][0] - x1, pts[k][1] - y1);
        if (d > md) { md = d; mi = k; }
      }
      if (md > tol && mi >= 0) { keep[mi] = 1; stack.push([i, mi], [mi, j]); }
    }
    return pts.filter((_, i) => keep[i]);
  }

  function simplifyClosed(pts, tol) {
    const n = pts.length;
    if (n < 5) return pts.slice();
    let far = 0, fd = -1;
    for (let i = 1; i < n; i++) {
      const d = (pts[i][0] - pts[0][0]) ** 2 + (pts[i][1] - pts[0][1]) ** 2;
      if (d > fd) { fd = d; far = i; }
    }
    const a = simplifyOpen(pts.slice(0, far + 1), tol);
    const b = simplifyOpen(pts.slice(far).concat([pts[0]]), tol);
    return a.slice(0, -1).concat(b.slice(0, -1));
  }

  /* ---------- raster, distance field, contours ---------- */

  function fillPoly(mask, nx, ny, ox, oy, h, poly, val) {
    const n = poly.length;
    let minY = Infinity, maxY = -Infinity;
    for (const p of poly) { if (p[1] < minY) minY = p[1]; if (p[1] > maxY) maxY = p[1]; }
    const j0 = Math.max(0, Math.ceil((minY - oy) / h - 0.5));
    const j1 = Math.min(ny - 1, Math.floor((maxY - oy) / h - 0.5));
    for (let j = j0; j <= j1; j++) {
      const y = oy + (j + 0.5) * h;
      const xs = [];
      for (let k = 0; k < n; k++) {
        const a = poly[k], b = poly[(k + 1) % n];
        if ((a[1] <= y) !== (b[1] <= y)) xs.push(a[0] + ((y - a[1]) * (b[0] - a[0])) / (b[1] - a[1]));
      }
      xs.sort((p, q) => p - q);
      for (let m = 0; m + 1 < xs.length; m += 2) {
        const i0 = Math.max(0, Math.ceil((xs[m] - ox) / h - 0.5));
        const i1 = Math.min(nx - 1, Math.floor((xs[m + 1] - ox) / h - 0.5));
        for (let i = i0; i <= i1; i++) mask[j * nx + i] = val;
      }
    }
  }

  function makeGrid(lawn, holes, w) {
    const bb = bboxOf(lawn);
    const maxDim = Math.max(bb.maxx - bb.minx, bb.maxy - bb.miny);
    const h = Math.max(0.08, maxDim / 800);
    const pad = w + 4 * h;
    const ox = bb.minx - pad, oy = bb.miny - pad;
    const nx = Math.ceil((bb.maxx - bb.minx + 2 * pad) / h) + 1;
    const ny = Math.ceil((bb.maxy - bb.miny + 2 * pad) / h) + 1;
    const mask = new Uint8Array(nx * ny);
    fillPoly(mask, nx, ny, ox, oy, h, lawn, 1);
    for (const hp of holes) fillPoly(mask, nx, ny, ox, oy, h, hp, 0);
    return { h, ox, oy, nx, ny, mask };
  }

  function dt1d(f, n, d, v, z) {
    let k = 0;
    v[0] = 0; z[0] = -Infinity; z[1] = Infinity;
    for (let q = 1; q < n; q++) {
      let s = (f[q] + q * q - (f[v[k]] + v[k] * v[k])) / (2 * q - 2 * v[k]);
      while (s <= z[k]) {
        k--;
        s = (f[q] + q * q - (f[v[k]] + v[k] * v[k])) / (2 * q - 2 * v[k]);
      }
      k++; v[k] = q; z[k] = s; z[k + 1] = Infinity;
    }
    k = 0;
    for (let q = 0; q < n; q++) {
      while (z[k + 1] < q) k++;
      d[q] = (q - v[k]) * (q - v[k]) + f[v[k]];
    }
  }

  // Squared distance (in cells) from every cell to the nearest site cell.
  function edtSq(sites, nx, ny) {
    const out = new Float32Array(nx * ny);
    const n = Math.max(nx, ny);
    const f = new Float64Array(n), d = new Float64Array(n), v = new Int32Array(n), z = new Float64Array(n + 1);
    for (let i = 0; i < nx; i++) {
      for (let j = 0; j < ny; j++) f[j] = sites[j * nx + i] ? 0 : INF;
      dt1d(f, ny, d, v, z);
      for (let j = 0; j < ny; j++) out[j * nx + i] = d[j];
    }
    for (let j = 0; j < ny; j++) {
      for (let i = 0; i < nx; i++) f[i] = out[j * nx + i];
      dt1d(f, nx, d, v, z);
      for (let i = 0; i < nx; i++) out[j * nx + i] = d[i];
    }
    return out;
  }

  // Signed distance to the mowable boundary: positive inside, negative outside.
  function signedField(G) {
    const { nx, ny, h, mask } = G;
    const N = nx * ny;
    const inv = new Uint8Array(N);
    for (let i = 0; i < N; i++) inv[i] = mask[i] ? 0 : 1;
    const dOut = edtSq(inv, nx, ny);
    const dIn = edtSq(mask, nx, ny);
    const F = new Float32Array(N);
    for (let i = 0; i < N; i++) {
      F[i] = mask[i] ? (Math.sqrt(dOut[i]) - 0.5) * h : -(Math.sqrt(dIn[i]) - 0.5) * h;
    }
    return F;
  }

  const CASES = [
    [], [[3, 0]], [[0, 1]], [[3, 1]], [[1, 2]], null, [[0, 2]], [[3, 2]],
    [[2, 3]], [[0, 2]], null, [[1, 2]], [[3, 1]], [[0, 1]], [[3, 0]], [],
  ];

  function contourLoops(G, F, r) {
    const { nx, ny, ox, oy, h } = G;
    const ex = [], ey = [];
    const keyToE = new Map();
    const segA = [], segB = [];
    const at = new Map();
    const edge = (key, x, y) => {
      let e = keyToE.get(key);
      if (e === undefined) { e = ex.length; ex.push(x); ey.push(y); keyToE.set(key, e); }
      return e;
    };
    const link = (e, s) => { const l = at.get(e); if (l) l.push(s); else at.set(e, [s]); };
    const edgeAt = (e, k, v0, v1, v2, v3, x0, y0) => {
      if (e === 0) return edge(2 * k, x0 + ((r - v0) / (v1 - v0)) * h, y0);
      if (e === 1) return edge(2 * (k + 1) + 1, x0 + h, y0 + ((r - v1) / (v2 - v1)) * h);
      if (e === 2) return edge(2 * (k + nx), x0 + ((r - v3) / (v2 - v3)) * h, y0 + h);
      return edge(2 * k + 1, x0, y0 + ((r - v0) / (v3 - v0)) * h);
    };
    for (let j = 0; j < ny - 1; j++) {
      const y0 = oy + (j + 0.5) * h;
      for (let i = 0; i < nx - 1; i++) {
        const k = j * nx + i;
        const v0 = F[k], v1 = F[k + 1], v3 = F[k + nx], v2 = F[k + nx + 1];
        const code = (v0 >= r ? 1 : 0) | (v1 >= r ? 2 : 0) | (v2 >= r ? 4 : 0) | (v3 >= r ? 8 : 0);
        if (code === 0 || code === 15) continue;
        const x0 = ox + (i + 0.5) * h;
        let pairs = CASES[code];
        if (!pairs) {
          const hi = (v0 + v1 + v2 + v3) / 4 >= r;
          if (code === 5) pairs = hi ? [[0, 1], [2, 3]] : [[3, 0], [1, 2]];
          else pairs = hi ? [[3, 0], [1, 2]] : [[0, 1], [2, 3]];
        }
        for (const [ea, eb] of pairs) {
          const a = edgeAt(ea, k, v0, v1, v2, v3, x0, y0);
          const b = edgeAt(eb, k, v0, v1, v2, v3, x0, y0);
          const s = segA.length;
          segA.push(a); segB.push(b);
          link(a, s); link(b, s);
        }
      }
    }
    const used = new Uint8Array(segA.length);
    const loops = [];
    for (let s0 = 0; s0 < segA.length; s0++) {
      if (used[s0]) continue;
      const loop = [];
      let cur = s0, from = segA[s0];
      for (;;) {
        used[cur] = 1;
        loop.push([ex[from], ey[from]]);
        const to = segA[cur] === from ? segB[cur] : segA[cur];
        const lst = at.get(to);
        let nxt = -1;
        for (const q of lst) if (q !== cur) nxt = q;
        if (nxt < 0 || used[nxt]) break;
        cur = nxt; from = to;
      }
      if (loop.length >= 3) loops.push(loop);
    }
    return loops;
  }

  function makeSampler(G, F) {
    const { nx, ny, ox, oy, h } = G;
    return {
      near(x, y) {
        const i = Math.floor((x - ox) / h), j = Math.floor((y - oy) / h);
        if (i < 0 || j < 0 || i >= nx || j >= ny) return -1e3;
        return F[j * nx + i];
      },
      bilinear(x, y) {
        const fx = (x - ox) / h - 0.5, fy = (y - oy) / h - 0.5;
        const i = Math.floor(fx), j = Math.floor(fy);
        if (i < 0 || j < 0 || i >= nx - 1 || j >= ny - 1) return -1e3;
        const tx = fx - i, ty = fy - j, k = j * nx + i;
        return (F[k] * (1 - tx) + F[k + 1] * tx) * (1 - ty) + (F[k + nx] * (1 - tx) + F[k + nx + 1] * tx) * ty;
      },
    };
  }

  // Offset loops at distance r inside the mowable area, simplified and oriented
  // so the mowable side is on the left of travel.
  function offsetLoops(ctx, r) {
    const { G, F, sampler } = ctx;
    const h = G.h;
    const tol = Math.max(0.05, 0.6 * h);
    const out = [];
    for (const raw of contourLoops(G, F, r)) {
      let loop = simplifyClosed(raw, tol);
      if (loop.length < 3) continue;
      if (Math.abs(polyArea(loop)) < 0.05) continue;
      let bi = 0, bl = -1;
      for (let i = 0; i < loop.length; i++) {
        const q = loop[(i + 1) % loop.length];
        const l = Math.hypot(q[0] - loop[i][0], q[1] - loop[i][1]);
        if (l > bl) { bl = l; bi = i; }
      }
      const a = loop[bi], b = loop[(bi + 1) % loop.length];
      const mx = (a[0] + b[0]) / 2, my = (a[1] + b[1]) / 2;
      const nxl = -(b[1] - a[1]) / bl, nyl = (b[0] - a[0]) / bl;
      if (sampler.bilinear(mx + nxl * 0.6 * h, my + nyl * 0.6 * h) < r) loop = loop.reverse();
      out.push(loop);
    }
    return out;
  }

  /* ---------- transit: shortest paths inside the lawn ---------- */

  class Heap {
    constructor() { this.k = []; this.v = []; }
    get size() { return this.k.length; }
    push(key, val) {
      const k = this.k, v = this.v;
      let i = k.length;
      k.push(key); v.push(val);
      while (i > 0) {
        const p = (i - 1) >> 1;
        if (k[p] <= key) break;
        k[i] = k[p]; v[i] = v[p]; i = p;
      }
      k[i] = key; v[i] = val;
    }
    pop() {
      const k = this.k, v = this.v;
      const top = v[0];
      const lk = k.pop(), lv = v.pop();
      const n = k.length;
      if (n > 0) {
        let i = 0;
        for (;;) {
          let c = 2 * i + 1;
          if (c >= n) break;
          if (c + 1 < n && k[c + 1] < k[c]) c++;
          if (k[c] >= lk) break;
          k[i] = k[c]; v[i] = v[c]; i = c;
        }
        k[i] = lk; v[i] = lv;
      }
      return top;
    }
  }

  function euclidTransit() {
    return {
      exact: false,
      dist: (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1]),
      path: (a, b) => [a, b],
    };
  }

  function gridTransit(ctx) {
    const { G, F, w, sampler } = ctx;
    const h = G.h;
    const los_thr = w / 2 - 0.75 * h;
    const f = Math.max(1, Math.round(0.25 / h));
    const hc = f * h;
    const cnx = Math.ceil(G.nx / f), cny = Math.ceil(G.ny / f);
    const feas = new Uint8Array(cnx * cny);
    for (let cj = 0; cj < cny; cj++) {
      for (let ci = 0; ci < cnx; ci++) {
        const fi = Math.min(G.nx - 1, ci * f + (f >> 1)), fj = Math.min(G.ny - 1, cj * f + (f >> 1));
        feas[cj * cnx + ci] = F[fj * G.nx + fi] >= w / 2 - 0.6 * hc ? 1 : 0;
      }
    }
    const center = (idx) => {
      const ci = idx % cnx, cj = (idx / cnx) | 0;
      return [G.ox + (ci * f + f / 2) * h, G.oy + (cj * f + f / 2) * h];
    };
    const cache = new Map();

    const los = (a, b) => {
      const d = Math.hypot(a[0] - b[0], a[1] - b[1]);
      const n = Math.max(1, Math.ceil(d / h));
      for (let k = 0; k <= n; k++) {
        const t = k / n;
        if (sampler.near(a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t) < los_thr) return false;
      }
      return true;
    };

    const nodeOf = (p) => {
      const ci0 = clamp(Math.floor((p[0] - G.ox) / hc), 0, cnx - 1);
      const cj0 = clamp(Math.floor((p[1] - G.oy) / hc), 0, cny - 1);
      if (feas[cj0 * cnx + ci0]) return cj0 * cnx + ci0;
      for (let rr = 1; rr <= 8; rr++) {
        let best = -1, bd = Infinity;
        for (let dj = -rr; dj <= rr; dj++) {
          for (let di = -rr; di <= rr; di++) {
            if (Math.max(Math.abs(di), Math.abs(dj)) !== rr) continue;
            const ci = ci0 + di, cj = cj0 + dj;
            if (ci < 0 || cj < 0 || ci >= cnx || cj >= cny || !feas[cj * cnx + ci]) continue;
            const c = center(cj * cnx + ci);
            const d = Math.hypot(c[0] - p[0], c[1] - p[1]);
            if (d < bd) { bd = d; best = cj * cnx + ci; }
          }
        }
        if (best >= 0) return best;
      }
      return -1;
    };

    const field = (src) => {
      let fl = cache.get(src);
      if (fl) return fl;
      const dist = new Float64Array(cnx * cny).fill(INF);
      const pred = new Int32Array(cnx * cny).fill(-1);
      const heap = new Heap();
      dist[src] = 0;
      heap.push(0, src);
      const SQ2 = Math.SQRT2 * hc;
      while (heap.size) {
        const dk = heap.k[0];
        const u = heap.pop();
        if (dk > dist[u]) continue;
        const ui = u % cnx, uj = (u / cnx) | 0;
        for (let dj = -1; dj <= 1; dj++) {
          for (let di = -1; di <= 1; di++) {
            if (!di && !dj) continue;
            const vi = ui + di, vj = uj + dj;
            if (vi < 0 || vj < 0 || vi >= cnx || vj >= cny) continue;
            const v = vj * cnx + vi;
            if (!feas[v]) continue;
            if (di && dj && (!feas[uj * cnx + vi] || !feas[vj * cnx + ui])) continue;
            const nd = dk + (di && dj ? SQ2 : hc);
            if (nd < dist[v]) { dist[v] = nd; pred[v] = u; heap.push(nd, v); }
          }
        }
      }
      fl = { dist, pred };
      if (cache.size > 80) cache.delete(cache.keys().next().value);
      cache.set(src, fl);
      return fl;
    };

    return {
      exact: true,
      los,
      dist(a, b) {
        const d0 = Math.hypot(a[0] - b[0], a[1] - b[1]);
        if (d0 < 1e-9 || los(a, b)) return d0;
        const sn = nodeOf(a), tn = nodeOf(b);
        if (sn < 0 || tn < 0) return d0 * 1.5;
        const d = field(sn).dist[tn];
        if (d >= INF) return d0 * 4 + 100;
        const ca = center(sn), cb = center(tn);
        return d + Math.hypot(a[0] - ca[0], a[1] - ca[1]) + Math.hypot(b[0] - cb[0], b[1] - cb[1]);
      },
      path(a, b) {
        if (Math.hypot(a[0] - b[0], a[1] - b[1]) < 1e-9) return [a];
        if (los(a, b)) return [a, b];
        const sn = nodeOf(a), tn = nodeOf(b);
        if (sn < 0 || tn < 0) return [a, b];
        const fl = field(sn);
        if (fl.dist[tn] >= INF) return [a, b];
        const nodes = [];
        for (let c = tn; c >= 0; c = fl.pred[c]) nodes.push(center(c));
        nodes.reverse();
        const raw = [a, ...nodes, b];
        const out = [raw[0]];
        let anchor = 0;
        while (anchor < raw.length - 1) {
          let nextI = anchor + 1;
          for (let j = raw.length - 1; j > anchor + 1; j--) {
            if (los(raw[anchor], raw[j])) { nextI = j; break; }
          }
          out.push(raw[nextI]);
          anchor = nextI;
        }
        return out;
      },
    };
  }

  /* ---------- stripes and boustrophedon cells ---------- */

  // Parallel stripes at a compass bearing. Stripe lines are spread evenly between the
  // extremes of the stripe region so the spacing never exceeds the chosen overlap.
  // Stripes are sampled generously (they may run up to the lap centre line); redundant
  // ends are trimmed later by trimStripes, once the real coverage is known.
  function sampleStripes(ctx, bearing) {
    const { G, sampler, s, w, tSample, anchorPts, samplePts } = ctx;
    const h = G.h;
    const theta = (90 - bearing) * DEG;
    const ux = Math.cos(theta), uy = Math.sin(theta), nxv = -uy, nyv = ux;
    let nmin = Infinity, nmax = -Infinity, tmin = Infinity, tmax = -Infinity;
    for (const [x, y] of anchorPts) {
      const nn = x * nxv + y * nyv;
      if (nn < nmin) nmin = nn;
      if (nn > nmax) nmax = nn;
    }
    for (const [x, y] of samplePts) {
      const tt = x * ux + y * uy;
      if (tt < tmin) tmin = tt;
      if (tt > tmax) tmax = tt;
    }
    tmin -= h; tmax += h;
    const E = nmax - nmin;
    let count = 1, step = 0, c0 = (nmin + nmax) / 2;
    if (E >= 0.25 * s) {
      count = Math.ceil(E / s - 1e-9) + 1;
      step = E / (count - 1);
      c0 = nmin;
    }
    const minRun = Math.max(0.25 * w, 3 * h);
    const thr = tSample - 0.4 * h;
    const stripes = [];
    for (let j = 0; j < count; j++) {
      const c = c0 + j * step;
      const bx = c * nxv, by = c * nyv;
      const segs = [];
      let t0 = null, tp = null;
      for (let t = tmin; t <= tmax; t += h) {
        if (sampler.near(bx + t * ux, by + t * uy) >= thr) {
          if (t0 === null) t0 = t;
          tp = t;
        } else if (t0 !== null) {
          if (tp - t0 >= minRun) segs.push({ j, t0, t1: tp, c, id: -1 });
          t0 = null;
        }
      }
      if (t0 !== null && tp - t0 >= minRun) segs.push({ j, t0, t1: tp, c, id: -1 });
      stripes.push(segs);
    }
    return { bearing, ux, uy, nx: nxv, ny: nyv, stripes, count };
  }

  // Group stripe segments into boustrophedon cells: chains of segments in consecutive
  // stripes that connect one-to-one. Obstacles split and merge chains.
  function chainStripes(st, w) {
    const { stripes, count } = st;
    const all = [];
    for (const arr of stripes) for (const sg of arr) { sg.id = all.length; all.push(sg); }
    const up = all.map(() => []), down = all.map(() => []);
    const ovMin = 0.5 * w;
    for (let j = 0; j + 1 < count; j++) {
      for (const a of stripes[j]) {
        for (const b of stripes[j + 1]) {
          if (Math.min(a.t1, b.t1) - Math.max(a.t0, b.t0) >= ovMin) { up[a.id].push(b.id); down[b.id].push(a.id); }
        }
      }
    }
    const nextL = new Int32Array(all.length).fill(-1), hasPrev = new Uint8Array(all.length);
    for (const a of all) {
      if (up[a.id].length === 1) {
        const b = up[a.id][0];
        if (down[b].length === 1) { nextL[a.id] = b; hasPrev[b] = 1; }
      }
    }
    const cells = [];
    for (const a of all) {
      if (hasPrev[a.id]) continue;
      const chain = [];
      for (let cur = a.id; cur >= 0; cur = nextL[cur]) chain.push(all[cur]);
      cells.push(chain);
    }
    st.cells = cells;
    st.segCount = all.length;
    return st;
  }

  function buildStripes(ctx, bearing) {
    return chainStripes(sampleStripes(ctx, bearing), ctx.w);
  }

  // Shorten stripe ends while the deck's leading edge only covers ground that the laps or
  // neighbouring stripes already mowed. Keeps full coverage, removes wasted travel.
  function trimStripes(ctx, st, lapPieces) {
    const { G, w, coverable } = ctx;
    const { nx, ny, ox, oy, h } = G;
    const half = w / 2;
    const step = 2 * h;
    const minLen = 0.25 * w;
    const segs = [];
    for (const arr of st.stripes) for (const sg of arr) segs.push(sg);
    const asPieces = segs.map((sg) => ({ type: 'stripe', pts: [segPt(st, sg, sg.t0), segPt(st, sg, sg.t1)] }));
    const { cov } = stampCoverage(ctx, lapPieces.concat(asPieces), st.ux, st.uy);

    const trimEnd = (sg, atEnd) => {
      while (sg.t1 - sg.t0 > minLen + step) {
        const e = atEnd ? sg.t1 : sg.t0;
        const lo = atEnd ? e + half - step : e - half;
        const hi = atEnd ? e + half : e - half + step;
        const corners = [[lo, sg.c - half], [lo, sg.c + half], [hi, sg.c - half], [hi, sg.c + half]]
          .map(([t, n]) => [t * st.ux + n * st.nx, t * st.uy + n * st.ny]);
        const xs = corners.map((q) => q[0]), ys = corners.map((q) => q[1]);
        const i0 = Math.max(0, Math.floor((Math.min(...xs) - ox) / h)), i1 = Math.min(nx - 1, Math.floor((Math.max(...xs) - ox) / h));
        const j0 = Math.max(0, Math.floor((Math.min(...ys) - oy) / h)), j1 = Math.min(ny - 1, Math.floor((Math.max(...ys) - oy) / h));
        const hit = [];
        let ok = true;
        for (let j = j0; j <= j1 && ok; j++) {
          const cy = oy + (j + 0.5) * h;
          for (let i = i0; i <= i1; i++) {
            const cx = ox + (i + 0.5) * h;
            const tc = cx * st.ux + cy * st.uy, nc = cx * st.nx + cy * st.ny;
            if (Math.abs(nc - sg.c) > half) continue;
            if (atEnd ? !(tc > lo && tc <= hi) : !(tc >= lo && tc < hi)) continue;
            const idx = j * nx + i;
            if (!coverable[idx]) continue;
            if (cov[idx] < 2) { ok = false; break; }
            hit.push(idx);
          }
        }
        if (!ok) break;
        for (const idx of hit) cov[idx]--;
        if (atEnd) sg.t1 -= step; else sg.t0 += step;
      }
    };
    for (const sg of segs) { trimEnd(sg, true); trimEnd(sg, false); }
    st.stripes = st.stripes.map((arr) => arr.filter((sg) => sg.t1 - sg.t0 >= minLen));
    return chainStripes(st, w);
  }

  function segPt(st, sg, t) {
    return [sg.c * st.nx + t * st.ux, sg.c * st.ny + t * st.uy];
  }

  function cellVariants(st, chain, speed, turnSec) {
    const out = [];
    for (const fromFirst of [true, false]) {
      if (!fromFirst && chain.length === 1) continue;
      for (const fwd0 of [true, false]) {
        const segs = fromFirst ? chain : chain.slice().reverse();
        let len = 0, fwd = fwd0, prevEnd = null, entry = null;
        for (let i = 0; i < segs.length; i++) {
          const sg = segs[i];
          const a = segPt(st, sg, fwd ? sg.t0 : sg.t1), b = segPt(st, sg, fwd ? sg.t1 : sg.t0);
          len += Math.hypot(b[0] - a[0], b[1] - a[1]);
          if (i === 0) entry = a; else len += Math.hypot(a[0] - prevEnd[0], a[1] - prevEnd[1]);
          prevEnd = b;
          fwd = !fwd;
        }
        out.push({
          fromFirst, fwd0, entry, exit: prevEnd, len, segs,
          time: len / speed + (segs.length - 1) * turnSec,
        });
      }
    }
    return out;
  }

  // Choose cell order, entry side and direction. Returns node indices in order.
  function solveTour(nodes, startPos, tr, speed, turnSec) {
    const NV = nodes.length;
    const nCells = nodes.reduce((m, n) => Math.max(m, n.cell + 1), 0);
    const transitCost = (a, b) => {
      const d = tr.dist(a, b);
      return d / speed + (d > 0.4 ? 0.75 * turnSec : 0);
    };
    const T = [];
    for (let a = 0; a < NV; a++) {
      const row = new Float64Array(NV);
      for (let b = 0; b < NV; b++) row[b] = nodes[a].cell === nodes[b].cell ? INF : transitCost(nodes[a].exit, nodes[b].entry);
      T.push(row);
    }
    const S = new Float64Array(NV);
    for (let b = 0; b < NV; b++) S[b] = startPos ? transitCost(startPos, nodes[b].entry) : 0;

    if (nCells <= 11) {
      const full = (1 << nCells) - 1;
      const dp = new Float64Array((full + 1) * NV).fill(Infinity);
      const par = new Int32Array((full + 1) * NV).fill(-1);
      for (let b = 0; b < NV; b++) dp[(1 << nodes[b].cell) * NV + b] = S[b] + nodes[b].time;
      for (let mask = 1; mask <= full; mask++) {
        for (let a = 0; a < NV; a++) {
          const cur = dp[mask * NV + a];
          if (cur === Infinity) continue;
          for (let b = 0; b < NV; b++) {
            const bc = 1 << nodes[b].cell;
            if (mask & bc) continue;
            const cand = cur + T[a][b] + nodes[b].time;
            const idx = (mask | bc) * NV + b;
            if (cand < dp[idx]) { dp[idx] = cand; par[idx] = a; }
          }
        }
      }
      let best = Infinity, bi = -1;
      for (let a = 0; a < NV; a++) if (dp[full * NV + a] < best) { best = dp[full * NV + a]; bi = a; }
      const order = [];
      let mask = full, cur = bi;
      while (cur >= 0) {
        order.push(cur);
        const p = par[mask * NV + cur];
        mask ^= 1 << nodes[cur].cell;
        cur = p;
      }
      return { order: order.reverse(), total: best };
    }

    // Greedy nearest-neighbour with several starting nodes.
    const starts = [];
    if (startPos) {
      let bi = 0;
      for (let b = 1; b < NV; b++) if (S[b] + nodes[b].time < S[bi] + nodes[bi].time) bi = b;
      starts.push(bi);
    } else {
      const byLen = nodes.map((n, i) => i).sort((p, q) => nodes[q].time - nodes[p].time);
      for (const i of byLen.slice(0, 16)) starts.push(i);
    }
    let bestTour = null;
    for (const s0 of starts) {
      const seen = new Uint8Array(nCells);
      const order = [s0];
      seen[nodes[s0].cell] = 1;
      let total = S[s0] + nodes[s0].time, cur = s0;
      for (let step = 1; step < nCells; step++) {
        let bb = -1, bc = Infinity;
        for (let b = 0; b < NV; b++) {
          if (seen[nodes[b].cell]) continue;
          const c = T[cur][b] + nodes[b].time;
          if (c < bc) { bc = c; bb = b; }
        }
        order.push(bb); seen[nodes[bb].cell] = 1; total += bc; cur = bb;
      }
      if (!bestTour || total < bestTour.total) bestTour = { order, total };
    }
    return bestTour;
  }

  function evalAngle(ctx, bearing, startPos, tr, prebuilt) {
    const st = prebuilt || buildStripes(ctx, bearing);
    if (!st.cells.length) return { st, total: Infinity };
    const nodes = [];
    st.cells.forEach((chain, ci) => {
      for (const v of cellVariants(st, chain, ctx.speed, ctx.turnSec)) nodes.push(Object.assign(v, { cell: ci }));
    });
    const trUse = tr.exact && nodes.length > 120 ? euclidTransit() : tr;
    const tour = solveTour(nodes, startPos, trUse, ctx.speed, ctx.turnSec);
    return { st, nodes, tour, total: tour.total };
  }

  /* ---------- assembling the route ---------- */

  function pathMetrics(pts) {
    let len = 0, turn = 0, ph = null, px = null, py = null;
    for (const p of pts) {
      if (px !== null) {
        const dx = p[0] - px, dy = p[1] - py, l = Math.hypot(dx, dy);
        if (l < 1e-4) continue;
        len += l;
        const hd = Math.atan2(dy, dx);
        if (ph !== null) {
          let d = hd - ph;
          while (d > Math.PI) d -= 2 * Math.PI;
          while (d < -Math.PI) d += 2 * Math.PI;
          turn += Math.abs(d);
        }
        ph = hd;
      }
      px = p[0]; py = p[1];
    }
    return { len, turn };
  }

  function lapTour(ctx, loops, routeStart, tr) {
    const pieces = [];
    let cur = routeStart || ctx.lawn[0];
    let first = !routeStart;
    const left = loops.slice();
    while (left.length) {
      let bi = -1, bd = Infinity, bv = 0;
      for (let li = 0; li < left.length; li++) {
        const lp = left[li];
        let vi = 0, vd = Infinity;
        for (let i = 0; i < lp.length; i++) {
          const d = Math.hypot(lp[i][0] - cur[0], lp[i][1] - cur[1]);
          if (d < vd) { vd = d; vi = i; }
        }
        const cost = first ? vd : tr.dist(cur, lp[vi]);
        if (cost < bd) { bd = cost; bi = li; bv = vi; }
      }
      const lp = left.splice(bi, 1)[0];
      const entry = lp[bv];
      if (!first || routeStart) {
        const tp = tr.path(cur, entry);
        if (tp.length > 1) pieces.push({ type: 'transit', pts: tp });
      }
      first = false;
      const rot = lp.slice(bv).concat(lp.slice(0, bv));
      rot.push(rot[0]);
      pieces.push({ type: 'lap', pts: rot });
      cur = entry;
    }
    return { pieces, end: loops.length ? cur : routeStart };
  }

  function stripePieces(ctx, ev, startPos, tr) {
    const pieces = [];
    let cur = startPos;
    for (const ni of ev.tour.order) {
      const node = ev.nodes[ni];
      if (cur) {
        const tp = tr.path(cur, node.entry);
        if (tp.length > 1) pieces.push({ type: 'transit', pts: tp });
      }
      let fwd = node.fwd0, prevEnd = null;
      for (const sg of node.segs) {
        const a = segPt(ev.st, sg, fwd ? sg.t0 : sg.t1), b = segPt(ev.st, sg, fwd ? sg.t1 : sg.t0);
        if (prevEnd) pieces.push({ type: 'turn', pts: [prevEnd, a] });
        pieces.push({ type: 'stripe', pts: [a, b] });
        prevEnd = b;
        fwd = !fwd;
      }
      cur = node.exit;
    }
    return { pieces, end: cur };
  }

  // Mark every grid cell whose centre lies under the deck. The deck is a w x w square,
  // so each pass reaches half a width past its ends. Overlap and gap figures come from here.
  function stampCoverage(ctx, pieces, ux, uy) {
    const { G, w } = ctx;
    const { nx, ny, ox, oy, h } = G;
    const cov = new Uint8Array(nx * ny), dir = new Uint8Array(nx * ny), last = new Int32Array(nx * ny);
    const half = w / 2;
    let pass = 0;
    for (const pc of pieces) {
      if (pc.type !== 'lap' && pc.type !== 'stripe') continue;
      pass++;
      for (let q = 0; q + 1 < pc.pts.length; q++) {
        const a = pc.pts[q], b = pc.pts[q + 1];
        const dx = b[0] - a[0], dy = b[1] - a[1], L = Math.hypot(dx, dy);
        if (L < 1e-9) continue;
        const hx = dx / L, hy = dy / L;
        const dval = hx * ux + hy * uy >= 0 ? 1 : 2;
        const qx = -hy * half, qy = hx * half;
        const ax = a[0] - hx * half, ay = a[1] - hy * half, bx = b[0] + hx * half, by = b[1] + hy * half;
        const minx = Math.min(ax + qx, ax - qx, bx + qx, bx - qx), maxx = Math.max(ax + qx, ax - qx, bx + qx, bx - qx);
        const miny = Math.min(ay + qy, ay - qy, by + qy, by - qy), maxy = Math.max(ay + qy, ay - qy, by + qy, by - qy);
        const i0 = Math.max(0, Math.floor((minx - ox) / h)), i1 = Math.min(nx - 1, Math.floor((maxx - ox) / h));
        const j0 = Math.max(0, Math.floor((miny - oy) / h)), j1 = Math.min(ny - 1, Math.floor((maxy - oy) / h));
        for (let j = j0; j <= j1; j++) {
          const ry = oy + (j + 0.5) * h - a[1];
          for (let i = i0; i <= i1; i++) {
            const rx = ox + (i + 0.5) * h - a[0];
            const along = rx * hx + ry * hy, perp = -rx * hy + ry * hx;
            if (along < -half || along > L + half || perp < -half || perp > half) continue;
            const idx = j * nx + i;
            if (last[idx] !== pass) {
              last[idx] = pass;
              if (cov[idx] < 255) cov[idx]++;
              dir[idx] = dval;
            }
          }
        }
      }
    }
    return { cov, dir };
  }

  function bearingLabel(b) {
    const names = ['N–S', 'NNE–SSW', 'NE–SW', 'ENE–WSW', 'E–W', 'ESE–WNW', 'SE–NW', 'SSE–NNW'];
    const i = Math.round((((b % 180) + 180) % 180) / 22.5) % 8;
    return names[i];
  }

  /* ---------- public entry point ---------- */

  async function plan(opts, hooks) {
    hooks = hooks || {};
    const report = (f, m) => { if (hooks.onProgress) hooks.onProgress(f, m); };
    const cancelled = () => hooks.cancel && hooks.cancel.cancelled;
    const fail = (error) => ({ ok: false, error });
    const t00 = now();
    const lg = (m) => { if (hooks.log) hooks.log(m, now() - t00); };

    const lawnLL = opts.lawn || [];
    if (lawnLL.length < 3) return fail('Outline the lawn first. It needs at least three corners.');
    const lat0 = lawnLL.reduce((a, p) => a + p[0], 0) / lawnLL.length;
    const lng0 = lawnLL.reduce((a, p) => a + p[1], 0) / lawnLL.length;
    const proj = projection(lat0, lng0);
    const lawn = lawnLL.map((p) => proj.toXY(p[0], p[1]));
    if (Math.abs(polyArea(lawn)) < 2) return fail('That outline is too small to plan. Check the corners.');
    const holes = (opts.obstacles || []).filter((o) => o && o.length >= 3).map((o) => o.map((p) => proj.toXY(p[0], p[1])));

    const w = clamp(opts.deckWidthM || 0.53, 0.2, 3);
    const overlap = clamp(opts.overlap == null ? 0.1 : opts.overlap, 0, 0.5);
    const s = w * (1 - overlap);
    const laps = clamp(Math.round(opts.laps == null ? 1 : opts.laps), 0, 4);
    const speed = opts.speedMps || 1.2;
    const turnSec = opts.turnSec == null ? 4 : opts.turnSec;
    const routeStart = opts.start ? proj.toXY(opts.start[0], opts.start[1]) : null;

    report(0.02, 'Rasterising the lawn');
    await tick();
    const G = makeGrid(lawn, holes, w);
    lg('grid');
    const F = signedField(G);
    lg('field');
    const sampler = makeSampler(G, F);
    // The deck is modelled as a w x w square. Stripe lines are laid out starting one
    // spacing inside the last lap (tAnchor), so the first stripe overlaps the lap by the
    // chosen overlap. They may be sampled up to the lap centre line (tSample) so tilted
    // edges leave no wedge, and redundant ends are trimmed afterwards.
    const tAnchor = w / 2 + laps * s;
    const tSample = laps > 0 ? w / 2 + (laps - 1) * s + 0.5 * w * overlap : w / 2;
    const ctx = { G, F, sampler, w, s, tAnchor, tSample, speed, turnSec, lawn, laps };

    let mowableCells = 0, feasibleCells = 0;
    const N0 = F.length;
    const feasMask = new Uint8Array(N0);
    for (let i = 0; i < N0; i++) {
      if (G.mask[i]) mowableCells++;
      if (F[i] >= w / 2) { feasibleCells++; feasMask[i] = 1; }
    }
    if (feasibleCells < 4) {
      return fail('The deck is wider than this lawn can fit. Try a narrower deck or redraw the outline.');
    }
    // Cells the deck can actually reach: within half a width of a feasible centre position.
    const dFe = edtSq(feasMask, G.nx, G.ny);
    ctx.coverable = new Uint8Array(N0);
    let coverableN = 0;
    for (let i = 0; i < N0; i++) {
      if (G.mask[i] && Math.sqrt(dFe[i]) * G.h <= w / 2 + 0.75 * G.h) { ctx.coverable[i] = 1; coverableN++; }
    }

    const anchorLoops = offsetLoops(ctx, tAnchor);
    ctx.anchorPts = [].concat(...anchorLoops);
    ctx.samplePts = tSample === tAnchor ? ctx.anchorPts : [].concat(...offsetLoops(ctx, tSample));
    lg('region loops');
    const lapLoops = [];
    for (let i = 0; i < laps; i++) lapLoops.push(...offsetLoops(ctx, w / 2 + i * s));

    report(0.08, 'Planning perimeter laps');
    await tick();
    lg('lap loops');
    const trExact = gridTransit(ctx);
    lg('transit built');
    const trEuc = euclidTransit();
    const lapsRes = lapTour(ctx, lapLoops, routeStart, trExact);
    lg('lap tour');
    const stripeStart = lapsRes.end || routeStart || null;

    const hasStripes = ctx.anchorPts.length >= 3;
    const curve = [];
    const score = (c) => c.time * (c.refined ? 1.003 : 1);
    let chosen = null;
    const fixed = opts.bearing == null ? null : ((Math.round(opts.bearing) % 180) + 180) % 180;

    if (hasStripes) {
      const evals = new Map();
      const evalCached = (b, tr, key) => {
        const k = key + b;
        if (!evals.has(k)) evals.set(k, evalAngle(ctx, b, stripeStart, tr));
        return evals.get(k);
      };
      const coarse = [];
      for (let b = 0; b < 180; b += 5) coarse.push(b);
      for (let i = 0; i < coarse.length; i++) {
        if (cancelled()) return fail('cancelled');
        const b = coarse[i];
        const ev = evalCached(b, trEuc, 'e');
        curve.push({ bearing: b, time: ev.total });
        report(0.1 + 0.6 * ((i + 1) / coarse.length), 'Trying stripe angles');
        await tick();
      }
      const bestCoarse = curve.reduce((m, c) => (c.time < m.time ? c : m), curve[0]);
      for (const d of [-4, -3, -2, -1, 1, 2, 3, 4]) {
        const b = (bestCoarse.bearing + d + 180) % 180;
        const ev = evalCached(b, trEuc, 'e');
        curve.push({ bearing: b, time: ev.total, refined: true });
      }
      curve.sort((a, b) => a.bearing - b.bearing);
      await tick();

      const finalists = fixed != null
        ? [fixed]
        : curve.slice().sort((a, b) => score(a) - score(b)).slice(0, 3).map((c) => c.bearing);
      let bestExact = null, bestScore = Infinity;
      for (let i = 0; i < finalists.length; i++) {
        if (cancelled()) return fail('cancelled');
        report(0.72 + 0.2 * (i / finalists.length), 'Checking routes around obstacles');
        await tick();
        const ev = evalCached(finalists[i], trExact, 'x');
        const sc = ev.total * (finalists[i] % 5 === 0 ? 1 : 1.003);
        if (sc < bestScore) { bestScore = sc; bestExact = ev; }
      }
      chosen = bestExact;
      if (fixed != null && !curve.some((c) => c.bearing === fixed)) curve.push({ bearing: fixed, time: chosen.total, refined: true });
    }

    report(0.94, 'Building the route');
    await tick();
    let pieces = lapsRes.pieces.slice();
    let st = null;
    if (chosen && chosen.tour && isFinite(chosen.total)) {
      trimStripes(ctx, chosen.st, lapsRes.pieces);
      chosen = evalAngle(ctx, chosen.st.bearing, stripeStart, trExact, chosen.st);
    }
    if (chosen && chosen.tour && isFinite(chosen.total)) {
      const sp = stripePieces(ctx, chosen, stripeStart, trExact);
      pieces = pieces.concat(sp.pieces);
      st = chosen.st;
    }
    if (!pieces.some((p) => p.type === 'lap' || p.type === 'stripe')) {
      return fail('Nothing to mow. The lawn may be narrower than the deck.');
    }

    const flat = [];
    for (const pc of pieces) for (const p of pc.pts) flat.push(p);
    const pm = pathMetrics(flat);
    let mowLen = 0, transitLen = 0, stripeLen = 0, lapLen = 0, stripeCount = 0;
    for (const pc of pieces) {
      const l = pathMetrics(pc.pts).len;
      if (pc.type === 'transit') transitLen += l;
      else mowLen += l;
      if (pc.type === 'stripe') { stripeLen += l; stripeCount++; }
      if (pc.type === 'lap') lapLen += l;
    }
    const halfTurns = pm.turn / Math.PI;
    const timeSec = pm.len / speed + halfTurns * turnSec;

    // Verify by stamping the deck over the route.
    report(0.97, 'Checking coverage');
    await tick();
    const ux = st ? st.ux : 1, uy = st ? st.uy : 0;
    const { cov, dir } = stampCoverage(ctx, pieces, ux, uy);
    const N = G.nx * G.ny;
    let covered = 0, extra = 0;
    for (let i = 0; i < N; i++) {
      if (ctx.coverable[i] && cov[i] > 0) { covered++; extra += cov[i] - 1; }
    }

    const h2 = G.h * G.h;
    let obstacleArea = 0;
    for (const hp of holes) obstacleArea += Math.abs(polyArea(hp));
    const bestCurve = curve.length ? curve.reduce((m, c) => (c.time < m.time ? c : m), curve[0]) : null;
    const worstCurve = curve.length ? curve.reduce((m, c) => (c.time > m.time ? c : m), curve[0]) : null;
    const usedBearing = st ? st.bearing : null;
    const ll = (p) => proj.toLL(p[0], p[1]);
    const sw = proj.toLL(G.ox, G.oy), ne = proj.toLL(G.ox + G.nx * G.h, G.oy + G.ny * G.h);

    report(1, 'Done');
    return {
      ok: true,
      bearing: usedBearing,
      bearingLabel: usedBearing == null ? null : bearingLabel(usedBearing),
      route: { pieces: pieces.map((pc) => ({ type: pc.type, ll: pc.pts.map(ll) })) },
      curve: curve.map((c) => ({ bearing: c.bearing, timeSec: c.time, refined: !!c.refined })),
      stats: {
        lawnAreaM2: Math.abs(polyArea(lawn)),
        obstacleAreaM2: obstacleArea,
        mowableAreaM2: mowableCells * h2,
        deckWidthM: w,
        overlap,
        laps,
        stripeCount,
        cellCount: st ? st.cells.length : 0,
        cellSizes: st ? st.cells.map((c) => c.length) : [],
        mowDistM: mowLen,
        transitDistM: transitLen,
        lapDistM: lapLen,
        stripeDistM: stripeLen,
        totalDistM: pm.len,
        turns: halfTurns,
        timeSec,
        coverableM2: coverableN * h2,
        coverage: coverableN ? covered / coverableN : 0,
        doubleCoverage: covered ? extra / covered : 0,
        worstAngleSavingPct: bestCurve && worstCurve && worstCurve.time > 0 && isFinite(worstCurve.time)
          ? (1 - bestCurve.time / worstCurve.time) * 100 : 0,
        computeMs: now() - t00,
        gridCell: G.h,
      },
      overlay: {
        nx: G.nx, ny: G.ny, h: G.h,
        mask: G.mask, cov, dir, coverable: ctx.coverable,
        bounds: [sw, ne],
      },
      _ctx: ctx,
    };
  }

  /* ---------- several separate lawns ---------- */

  // Plan each lawn on its own (each gets its own best stripe angle), visiting them
  // nearest-first from the start point and driving straight between them.
  // opts is as for plan(), but with lawns: [{ name, pts }] instead of lawn.
  async function planLawns(opts, hooks) {
    hooks = hooks || {};
    const lawns = (opts.lawns || []).filter((l) => l && l.pts && l.pts.length >= 3);
    if (!lawns.length) return { ok: false, error: 'Outline the lawn first. It needs at least three corners.' };
    if (lawns.length === 1) return plan(Object.assign({}, opts, { lawn: lawns[0].pts }), hooks);

    const t00 = now();
    const proj = projection(lawns[0].pts[0][0], lawns[0].pts[0][1]);
    const xy = (p) => proj.toXY(p[0], p[1]);
    const distTo = (p, lawn) => {
      const q = xy(p), poly = lawn.pts.map(xy);
      if (pointInPoly(q[0], q[1], poly)) return 0;
      return Math.min(...poly.map((v) => Math.hypot(v[0] - q[0], v[1] - q[1])));
    };

    // Each lawn is planned from where the previous one ended; plan() drives in from that
    // point and counts the drive in its own distance and time.
    const left = lawns.slice();
    const parts = [];
    const pieces = [];
    let cur = opts.start || null;
    while (left.length) {
      let bi = 0;
      if (cur) {
        let bd = Infinity;
        left.forEach((l, i) => { const d = distTo(cur, l); if (d < bd) { bd = d; bi = i; } });
      }
      const lawn = left.splice(bi, 1)[0];
      const k = parts.length, n = lawns.length;
      const sub = await plan(Object.assign({}, opts, { lawn: lawn.pts, start: cur }), {
        cancel: hooks.cancel,
        log: hooks.log,
        onProgress: (f, m) => { if (hooks.onProgress) hooks.onProgress((k + f) / n, lawn.name + ': ' + m); },
      });
      if (!sub.ok) return sub.error === 'cancelled' ? sub : Object.assign({}, sub, { error: lawn.name + ': ' + sub.error });
      const subPieces = sub.route.pieces;
      pieces.push(...subPieces);
      const lastPc = subPieces[subPieces.length - 1];
      cur = lastPc.ll[lastPc.ll.length - 1];
      parts.push(Object.assign(sub, { name: lawn.name }));
    }

    const sum = (f) => parts.reduce((a, p) => a + f(p.stats), 0);
    const coverableM2 = sum((s) => s.coverableM2);
    const coveredM2 = parts.reduce((a, p) => a + p.stats.coverage * p.stats.coverableM2, 0);
    const doubleM2 = parts.reduce((a, p) => a + p.stats.doubleCoverage * p.stats.coverage * p.stats.coverableM2, 0);
    const best = parts.reduce((a, p) => a + (p.curve.length ? Math.min(...p.curve.map((c) => c.timeSec)) : 0), 0);
    const worst = parts.reduce((a, p) => a + (p.curve.length ? Math.max(...p.curve.map((c) => c.timeSec)) : 0), 0);
    const bearings = parts.map((p) => p.bearing);
    const same = bearings.every((b) => b === bearings[0]);
    return {
      ok: true,
      bearing: same ? bearings[0] : null,
      bearingLabel: same && bearings[0] != null ? bearingLabel(bearings[0]) : null,
      parts: parts.map((p) => ({ name: p.name, bearing: p.bearing, bearingLabel: p.bearingLabel, timeSec: p.stats.timeSec })),
      route: { pieces },
      curve: [],
      stats: {
        lawnAreaM2: sum((s) => s.lawnAreaM2),
        obstacleAreaM2: sum((s) => s.obstacleAreaM2),
        mowableAreaM2: sum((s) => s.mowableAreaM2),
        coverableM2,
        deckWidthM: parts[0].stats.deckWidthM,
        overlap: parts[0].stats.overlap,
        laps: parts[0].stats.laps,
        stripeCount: sum((s) => s.stripeCount),
        mowDistM: sum((s) => s.mowDistM),
        transitDistM: sum((s) => s.transitDistM),
        lapDistM: sum((s) => s.lapDistM),
        stripeDistM: sum((s) => s.stripeDistM),
        totalDistM: sum((s) => s.totalDistM),
        turns: sum((s) => s.turns),
        timeSec: sum((s) => s.timeSec),
        coverage: coverableM2 ? coveredM2 / coverableM2 : 0,
        doubleCoverage: coveredM2 ? doubleM2 / coveredM2 : 0,
        worstAngleSavingPct: worst > 0 && isFinite(worst) ? (1 - best / worst) * 100 : 0,
        computeMs: now() - t00,
      },
      overlays: parts.map((p) => p.overlay),
    };
  }

  /* Convenience: lat/lng polygon from local metre offsets (used by samples and tests). */
  function fromLocal(lat0, lng0, pts) {
    const p = projection(lat0, lng0);
    return pts.map(([x, y]) => p.toLL(x, y));
  }

  function circleLL(lat0, lng0, cx, cy, r, n) {
    const pts = [];
    for (let i = 0; i < (n || 28); i++) {
      const a = (i / (n || 28)) * Math.PI * 2;
      pts.push([cx + r * Math.cos(a), cy + r * Math.sin(a)]);
    }
    return fromLocal(lat0, lng0, pts);
  }

  return {
    plan, planLawns, projection, polyArea, pointInPoly, fromLocal, circleLL, bearingLabel,
    _internals: { lapTour, makeGrid, signedField, makeSampler, offsetLoops, gridTransit, contourLoops },
  };
});
