// ==UserScript==
// @name         tiki
// @namespace    https://bloxd.io/
// @version      3.6.0
// @description  idk
// @match        *://bloxd.io/*
// @match        *://*.bloxd.io/*
// @run-at       document-start
// @grant        none
// ==/UserScript==

(() => {
  'use strict';
  if (window.__bloxdShaderLab) { console.warn('[Shader Lab] Another Shader Lab script is already running, disable the old one.'); return; }
  const GL2 = window.WebGL2RenderingContext;
  if (!GL2) return;

  const KEY = 'bloxdShaderLab.v2';
  const DEFAULTS = { enabled: true, time: 11, rays: 0.6, water: 0.75, weather: 'clear', wxPower: 0.8, shadow: 1 };
  const S = Object.assign({}, DEFAULTS);
  try { Object.assign(S, JSON.parse(localStorage.getItem(KEY) || '{}')); } catch (e) {}
  const save = () => { try { localStorage.setItem(KEY, JSON.stringify({ enabled: S.enabled, time: S.time, rays: S.rays, water: S.water, weather: S.weather, wxPower: S.wxPower, shadow: S.shadow })); } catch (e) {} };

  const BOOT = 'bloxdShaderLab.boot';
  let bootMarked = false;
  let bootCount = 0;
  try {
    bootCount = parseInt(localStorage.getItem(BOOT) || '0', 10) || 0;
    if (bootCount >= 3) S.enabled = false;
    localStorage.setItem(BOOT, String(bootCount + 1));
  } catch (e) {}

  if (S.weather === 'storm') S.weather = 'rain';
  if (['clear', 'rain'].indexOf(S.weather) < 0) S.weather = 'clear';

  const P = GL2.prototype;
  const N = {};
  const ST = new WeakMap();
  const PROGS = new Map();
  const LOCN = new WeakMap();
  const MATRE = /view|proj|world|model|vp|mvp|transform|matrix/i;
  const UBO_TARGET = 35345;
  const UBO_MAX = 65536;
  const stats = { ubo: 0 };
  const shaderLog = [];
  let gameGL = null;
  let statusText = '';
  let dbgMode = 0;

  const stOf = (gl) => {
    let s = ST.get(gl);
    if (!s) {
      s = { logicalDraw: null, actualDraw: null, curProg: null, managed: false, frameStarted: false,
            drew: false, failed: false, fbo: null, colorTex: null, depthTex: null, w: 0, h: 0,
            prog: null, U: null, vao: null, postCount: 0, lastCheckPost: -1,
            matOk: false, vp: null, ivp: null, cam: [0, 0, 0], how: null,
            shProg: null, shU: null, shFbo: null, shTex: null, shW: 0, shH: 0,
            snapFbo: null, snapTex: null, snapValid: false, segDraws: 0, bestDraws: 0, clears: 0, lastClears: 0,
            gs: { caps: {}, depthMask: true, depthFunc: 513, clearDepth: 1, vp: [0, 0, 1, 1] },
            frameId: 0, boot: false, lsFbo: null, lsTex: null, lsScratchFbo: null, lsSizeS: 2048, lsSizeD: 2048,
            lsExtent: 64, lsRange: 160, lsA: null, lsLastCam: null, lsCur: 1, lsPrev: 2, lsEpochT: 0,
            lsF: null, lsOn: false, lsUse: false, lsBroken: false, replayOK: false,
            lsElig: 0, lsDone: 0, lsSkip: 0, lsStat: 0, lsDyn: 0, lsShifts: 0, lsResets: 0,
            lsDirty: false, lsDirtyT: 0, lsDirtyClears: 0 };
      ST.set(gl, s);
    }
    return s;
  };

  function isGame(gl) {
    if (gameGL) return gl === gameGL;
    const c = gl.canvas;
    if (c instanceof HTMLCanvasElement && c.width > 300 && c.height > 200) { gameGL = gl; bootstrapGL(gl, stOf(gl)); return true; }
    return false;
  }

  function mul(a, b) {
    const o = new Float32Array(16);
    for (let c = 0; c < 4; c++) for (let r = 0; r < 4; r++) {
      let s = 0;
      for (let k = 0; k < 4; k++) s += a[k * 4 + r] * b[c * 4 + k];
      o[c * 4 + r] = s;
    }
    return o;
  }

  function inv4(m) {
    const A = new Float64Array(32);
    for (let r = 0; r < 4; r++) { for (let c = 0; c < 4; c++) A[r * 8 + c] = m[r * 4 + c]; A[r * 8 + 4 + r] = 1; }
    for (let i = 0; i < 4; i++) {
      let p = i, mx = Math.abs(A[i * 8 + i]);
      for (let r = i + 1; r < 4; r++) { const v = Math.abs(A[r * 8 + i]); if (v > mx) { mx = v; p = r; } }
      if (mx < 1e-12) return null;
      if (p !== i) for (let c = 0; c < 8; c++) { const t = A[i * 8 + c]; A[i * 8 + c] = A[p * 8 + c]; A[p * 8 + c] = t; }
      const d = A[i * 8 + i];
      for (let c = 0; c < 8; c++) A[i * 8 + c] /= d;
      for (let r = 0; r < 4; r++) {
        if (r === i) continue;
        const f = A[r * 8 + i];
        if (f !== 0) for (let c = 0; c < 8; c++) A[r * 8 + c] -= f * A[i * 8 + c];
      }
    }
    const o = new Float32Array(16);
    for (let r = 0; r < 4; r++) for (let c = 0; c < 4; c++) o[r * 4 + c] = A[r * 8 + 4 + c];
    return o;
  }

  function findVP(m) {
    const names = Object.keys(m);
    const find = (re, ex) => names.find((n) => re.test(n) && !(ex && ex.test(n)));
    let n = find(/^(u_?)?view_?proj(ection)?(_?matrix)?$/i, /inv|prev|light|shadow/i);
    if (n) return { vp: m[n], how: n };
    n = find(/viewproj/i, /world|model|inv|prev|light|shadow/i);
    if (n) return { vp: m[n], how: n };
    const v = find(/^(u_?)?view(_?matrix)?$/i, /inv|prev|light|shadow/i);
    const p = find(/^(u_?)?proj(ection)?(_?matrix)?$/i, /inv|prev|light|shadow/i);
    if (v && p) return { vp: mul(m[p], m[v]), how: p + ' * ' + v };
    const wvp = find(/(world|model)_?view_?proj/i, /inv|prev/i);
    const w = find(/^(u_?)?(world|model)(_?matrix)?$/i, /inv|prev|view/i);
    if (wvp && w) { const iw = inv4(m[w]); if (iw) return { vp: mul(m[wvp], iw), how: wvp + ' * inverse(' + w + ')' }; }
    const pk = names.filter((k) => isPersp(m[k]));
    const vk = names.filter((k) => isRigid(m[k]));
    if (pk.length && vk.length) return { vp: mul(m[pk[0]], m[vk[0]]), how: pk[0] + ' * ' + vk[0] };
    return null;
  }

  function isPersp(v) {
    return Math.abs(v[3]) < 1e-4 && Math.abs(v[7]) < 1e-4 && Math.abs(v[11] + 1) < 1e-3 && Math.abs(v[15]) < 1e-4 &&
      Math.abs(v[1]) < 1e-4 && Math.abs(v[2]) < 1e-4 && Math.abs(v[4]) < 1e-4 && Math.abs(v[6]) < 1e-4 && v[0] > 0 && v[5] > 0;
  }

  function isRigid(v) {
    if (Math.abs(v[3]) > 1e-4 || Math.abs(v[7]) > 1e-4 || Math.abs(v[11]) > 1e-4 || Math.abs(v[15] - 1) > 1e-4) return false;
    for (let c = 0; c < 3; c++) {
      const l = Math.hypot(v[c * 4], v[c * 4 + 1], v[c * 4 + 2]);
      if (Math.abs(l - 1) > 0.02) return false;
    }
    const d01 = v[0] * v[4] + v[1] * v[5] + v[2] * v[6];
    const d02 = v[0] * v[8] + v[1] * v[9] + v[2] * v[10];
    const d12 = v[4] * v[8] + v[5] * v[9] + v[6] * v[10];
    return Math.abs(d01) < 0.02 && Math.abs(d02) < 0.02 && Math.abs(d12) < 0.02;
  }

  const UB = new WeakMap();
  const UBUF = new WeakMap();
  const UVER = new WeakMap();
  const CLONES = new WeakMap();
  const PLOC = new WeakMap();
  const BUFINFO = new WeakMap();
  const MESH_MIN = 1024;
  const ubOf = (gl) => {
    let u = UB.get(gl);
    if (!u) { u = { cur: null, bind: [] }; UB.set(gl, u); }
    return u;
  };
  const toF32 = (d, so, len) => {
    let v = d instanceof ArrayBuffer ? new Uint8Array(d) : d;
    if (so !== undefined && so !== null && v.subarray) v = v.subarray(so, len !== undefined && len > 0 ? so + len : undefined);
    return new Float32Array(v.buffer.slice(v.byteOffset, v.byteOffset + (v.byteLength & ~3)));
  };

  function noteMeshWrite(gl, target, bytes, isSub) {
    if (gl !== gameGL) return;
    const s = ST.get(gl);
    if (!s) return;
    const buf = N.getParameter.call(gl, target === 34962 ? 34964 : 34965);
    if (!buf) return;
    let bi = BUFINFO.get(buf);
    const fresh = !bi;
    if (!bi) { bi = { last: -10, streak: 0, dyn: false }; BUFINFO.set(buf, bi); }
    if (s.frameId - bi.last <= 2) bi.streak++; else bi.streak = 0;
    bi.last = s.frameId;
    if (bi.streak >= 4) bi.dyn = true;
    if (bi.dyn) return;
    if (!isSub && fresh) return;
    s.lsDirty = true;
  }

  function blocksOf(gl, p, pi) {
    if (pi.blocks) return pi.blocks;
    const list = [];
    const n = gl.getProgramParameter(p, 35382) || 0;
    for (let i = 0; i < n; i++) {
      const idx = gl.getActiveUniformBlockParameter(p, i, 35395);
      const offs = gl.getActiveUniforms(p, idx, 35387);
      const u = {};
      for (let j = 0; j < idx.length; j++) {
        const info = gl.getActiveUniform(p, idx[j]);
        if (!info || info.type !== 35676 || info.size > 1) continue;
        u[info.name.replace(/^.*\./, '').replace(/\[0\]$/, '')] = offs[j] / 4;
      }
      list.push({ index: i, u });
    }
    pi.blocks = list;
    return list;
  }

  function uboMats(gl, p, pi) {
    const out = Object.create(null);
    const ub = UB.get(gl);
    if (!ub) return out;
    let blocks;
    try { blocks = blocksOf(gl, p, pi); } catch (e) { return out; }
    for (const blk of blocks) {
      let binding;
      try { binding = gl.getActiveUniformBlockParameter(p, blk.index, 35391); } catch (e) { continue; }
      const bd = ub.bind[binding];
      const data = bd && UBUF.get(bd.buf);
      if (!data) continue;
      const base = bd.off / 4;
      for (const name in blk.u) {
        const o = base + blk.u[name];
        if (o + 16 <= data.length) out[name] = data.slice(o, o + 16);
      }
    }
    return out;
  }

  function computeMatrices(gl, s) {
    const list = [...PROGS.entries()].filter(([, pi]) => pi.draws > 0).sort((a, b) => b[1].draws - a[1].draws);
    for (const pi of PROGS.values()) {
      pi.avg = pi.avg === undefined ? pi.draws : pi.avg * 0.8 + pi.draws * 0.2;
      pi.draws = 0;
    }
    s.matOk = false;
    for (const [prog, pi] of list) {
      const merged = Object.assign({}, pi.mats, uboMats(gl, prog, pi));
      const r = findVP(merged);
      if (!r) continue;
      const iv = inv4(r.vp);
      if (!iv) continue;
      s.vp = r.vp; s.ivp = iv;
      const v = [0, 0, -1, 1], o = [0, 0, 0, 0];
      for (let rr = 0; rr < 4; rr++) for (let c = 0; c < 4; c++) o[rr] += iv[c * 4 + rr] * v[c];
      s.cam = [o[0] / o[3], o[1] / o[3], o[2] / o[3]];
      s.matOk = isFinite(s.cam[0] + s.cam[1] + s.cam[2]);
      s.how = r.how;
      if (s.matOk) break;
    }
    statusText = s.matOk ? '' : 'noMatrix';
  }

  function panicOff(name, err) {
    console.error('[Shader Lab] Error in hook ' + name + ', shader disabled:', err);
    const s = gameGL && ST.get(gameGL);
    if (s) failRuntime(gameGL, s, err);
  }

  function hook(name, make) {
    const o = P[name];
    if (!o) return;
    N[name] = o;
    const f = make(o);
    P[name] = function () {
      try { return f.apply(this, arguments); }
      catch (err) { panicOff(name, err); return o.apply(this, arguments); }
    };
  }

  hook('bindFramebuffer', (o) => function (t, fb) {
    const s = stOf(this);
    const drawT = (t === 36160 || t === 36009);
    if (drawT) s.logicalDraw = fb;
    if (gameGL === this && s.managed && fb === null && (drawT || t === 36008)) fb = s.fbo;
    if (drawT) s.actualDraw = fb;
    return o.call(this, t, fb);
  });

  hook('getParameter', (o) => function (p) {
    if ((p === 36006 || p === 36010) && gameGL === this) {
      const s = ST.get(this);
      if (s && s.managed && s.actualDraw === s.fbo) return null;
    }
    return o.apply(this, arguments);
  });

  hook('useProgram', (o) => function (p) { stOf(this).curProg = p; return o.call(this, p); });
  hook('enable', (o) => function (c) { stOf(this).gs.caps[c] = true; return o.call(this, c); });
  hook('disable', (o) => function (c) { stOf(this).gs.caps[c] = false; return o.call(this, c); });
  hook('depthMask', (o) => function (m) { stOf(this).gs.depthMask = !!m; return o.call(this, m); });
  hook('depthFunc', (o) => function (f) { stOf(this).gs.depthFunc = f; return o.call(this, f); });
  hook('clearDepth', (o) => function (d) { stOf(this).gs.clearDepth = d; return o.call(this, d); });
  hook('viewport', (o) => function (x, y, w, h) { stOf(this).gs.vp = [x, y, w, h]; return o.call(this, x, y, w, h); });

  hook('getUniformLocation', (o) => function (p, n) {
    const l = o.call(this, p, n);
    if (l) {
      LOCN.set(l, n);
      let m = PLOC.get(p);
      if (!m) { m = {}; PLOC.set(p, m); }
      m[n] = l;
    }
    return l;
  });

  const TMPM = new Float32Array(16);
  const LOCTRY = new WeakMap();
  const SEEDED = new WeakSet();

  function resolveName(gl, prog, loc, val) {
    const tries = LOCTRY.get(loc) || 0;
    if (tries >= 6) return null;
    LOCTRY.set(loc, tries + 1);
    let pi = PROGS.get(prog);
    if (!pi) { pi = { mats: Object.create(null), draws: 0, total: 0, blocks: null }; PROGS.set(prog, pi); }
    if (!pi.mat4) {
      pi.mat4 = [];
      pi.claimed = new Set();
      const cnt = gl.getProgramParameter(prog, 35718) || 0;
      for (let i = 0; i < cnt; i++) {
        const info = gl.getActiveUniform(prog, i);
        if (info && info.type === 35676 && info.size === 1) pi.mat4.push(info.name);
      }
    }
    let hit = null, n = 0;
    for (const name of pi.mat4) {
      if (pi.claimed.has(name)) continue;
      const l = N.getUniformLocation.call(gl, prog, name);
      if (!l) continue;
      const cv = gl.getUniform(prog, l);
      let same = true;
      for (let i = 0; i < 16; i++) if (Math.abs(cv[i] - val[i]) > 1e-6 * (1 + Math.abs(val[i]))) { same = false; break; }
      if (same) { hit = name; n++; }
    }
    if (n === 1) { pi.claimed.add(hit); LOCN.set(loc, hit); return hit; }
    return null;
  }

  hook('uniformMatrix4fv', (o) => function (loc, tr, v, so) {
    const r = o.apply(this, arguments);
    if ((gameGL === this || !gameGL) && loc && v) {
      const s = ST.get(this);
      const off = so || 0;
      if (s && s.curProg && v.length - off >= 16) {
        let n = LOCN.get(loc);
        let pi = PROGS.get(s.curProg);
        const a = n && pi ? pi.mats[n] : null;
        const dst = a || TMPM;
        if (tr) { for (let rr = 0; rr < 4; rr++) for (let c = 0; c < 4; c++) dst[c * 4 + rr] = v[off + rr * 4 + c]; }
        else { for (let i = 0; i < 16; i++) dst[i] = v[off + i]; }
        if (!n) n = resolveName(this, s.curProg, loc, TMPM);
        if (n) {
          if (!pi) { pi = { mats: Object.create(null), draws: 0, total: 0, blocks: null }; PROGS.set(s.curProg, pi); }
          if (!a) pi.mats[n] = new Float32Array(TMPM);
        }
      }
    }
    return r;
  });

  hook('bindBuffer', (o) => function (t, b) {
    if (t === UBO_TARGET) ubOf(this).cur = b;
    return o.call(this, t, b);
  });

  hook('bindBufferBase', (o) => function (t, i, b) {
    if (t === UBO_TARGET) { const u = ubOf(this); ensureUbuf(this, b); u.cur = b; u.bind[i] = { buf: b, off: 0 }; }
    return o.call(this, t, i, b);
  });

  hook('bindBufferRange', (o) => function (t, i, b, off, size) {
    if (t === UBO_TARGET) { const u = ubOf(this); ensureUbuf(this, b); u.cur = b; u.bind[i] = { buf: b, off: off || 0, size: size }; }
    return o.call(this, t, i, b, off, size);
  });

  hook('bufferData', (o) => function (t, d, u, so, len) {
    if (t === UBO_TARGET) {
      const ub = ubOf(this);
      if (ub.cur && d) {
        stats.ubo++;
        UVER.set(ub.cur, (UVER.get(ub.cur) || 0) + 1);
        if (typeof d === 'number') {
          if (d <= UBO_MAX) UBUF.set(ub.cur, new Float32Array(Math.ceil(d / 4)));
        } else if (d.byteLength <= UBO_MAX) {
          UBUF.set(ub.cur, toF32(d, so, len));
        }
      }
    } else if ((t === 34962 || t === 34963) && d) {
      const bytes = typeof d === 'number' ? d : (d.byteLength || 0);
      if (bytes >= MESH_MIN) noteMeshWrite(this, t, bytes, false);
    }
    return o.apply(this, arguments);
  });

  hook('bufferSubData', (o) => function (t, off, d, so, len) {
    if (t === UBO_TARGET) {
      const ub = ubOf(this);
      if (ub.cur && d && off % 4 === 0 && off < UBO_MAX) {
        stats.ubo++;
        ensureUbuf(this, ub.cur);
        UVER.set(ub.cur, (UVER.get(ub.cur) || 0) + 1);
        const f = toF32(d, so, len);
        let arr = UBUF.get(ub.cur);
        const need = off / 4 + f.length;
        if (!arr || arr.length < need) {
          const nw = new Float32Array(need);
          if (arr) nw.set(arr);
          arr = nw;
          UBUF.set(ub.cur, arr);
        }
        arr.set(f, off / 4);
      }
    } else if ((t === 34962 || t === 34963) && d) {
      const bytes = d.byteLength || 0;
      if (bytes >= MESH_MIN) noteMeshWrite(this, t, bytes, true);
    }
    return o.apply(this, arguments);
  });

  hook('deleteBuffer', (o) => function (b) {
    const bi = b && BUFINFO.get(b);
    if (bi && !bi.dyn && gameGL === this) {
      const s = ST.get(this);
      if (s) s.lsDirty = true;
    }
    return o.call(this, b);
  });

  hook('shaderSource', (o) => function (sh, src) {
    if (shaderLog.length < 300) shaderLog.push(String(src));
    return o.apply(this, arguments);
  });

  function prepDraw(gl) {
    if (!isGame(gl)) return;
    const s = stOf(gl);
    if (s.logicalDraw !== null) return;
    if (!s.frameStarted) begin(gl, s);
    s.drew = true;
    s.segDraws++;
    if (s.curProg) {
      let pi = PROGS.get(s.curProg);
      if (!pi) { pi = { mats: Object.create(null), draws: 0, total: 0, blocks: null }; PROGS.set(s.curProg, pi); }
      pi.draws++; pi.total++;
    }
  }
  for (const fn of ['drawElements', 'drawArrays', 'drawElementsInstanced', 'drawArraysInstanced', 'drawRangeElements']) {
    hook(fn, (o) => function () {
      prepDraw(this);
      const r = o.apply(this, arguments);
      replayDraw(this, fn, arguments);
      return r;
    });
  }

  function prepClear(gl) {
    if (!isGame(gl)) return;
    const s = stOf(gl);
    if (s.logicalDraw !== null) return;
    if (!s.frameStarted) begin(gl, s);
  }
  const clearIsDepth = {
    clear: (a) => (a[0] & 256) !== 0,
    clearBufferfv: (a) => a[0] === 6145,
    clearBufferiv: () => false,
    clearBufferuiv: () => false,
    clearBufferfi: () => true,
  };
  for (const fn of Object.keys(clearIsDepth)) {
    hook(fn, (o) => function () {
      prepClear(this);
      if (clearIsDepth[fn](arguments)) { noteDepthClear(this); endSegment(this, false); }
      return o.apply(this, arguments);
    });
  }

  function snapshotDepth(gl, s) {
    const sc = gl.isEnabled(3089);
    if (sc) gl.disable(3089);
    N.bindFramebuffer.call(gl, 36008, s.fbo);
    N.bindFramebuffer.call(gl, 36009, s.snapFbo);
    gl.blitFramebuffer(0, 0, s.w, s.h, 0, 0, s.w, s.h, 256, 9728);
    N.bindFramebuffer.call(gl, 36009, s.fbo);
    if (sc) gl.enable(3089);
    s.snapValid = true;
  }

  function endSegment(gl, force) {
    if (!isGame(gl)) return;
    const s = ST.get(gl);
    if (!s || !s.managed || !s.snapFbo) return;
    if (!force && s.logicalDraw !== null) return;
    s.clears++;
    if (s.segDraws > s.bestDraws) {
      snapshotDepth(gl, s);
      s.bestDraws = s.segDraws;
    }
    s.segDraws = 0;
  }

  function begin(gl, s) {
    s.frameStarted = true;
    queueMicrotask(() => { try { if (gameGL) post(gameGL); } catch (e) {} });
    s.segDraws = 0;
    s.bestDraws = 0;
    s.snapValid = false;
    s.lastClears = s.clears;
    s.clears = 0;
    if (S.enabled && !s.failed) {
      try { ensureProgram(gl, s); ensureTargets(gl, s); }
      catch (e) { failRuntime(gl, s, e); return; }
      s.managed = true;
      s.frameId++;
      s.lsElig = 0; s.lsDone = 0; s.lsSkip = 0; s.lsStat = 0; s.lsDyn = 0; s.replayOK = true; s.lsOn = false;
      try { syncGs(gl, s); beginShadow(gl, s); }
      catch (e) { s.lsBroken = true; s.lsOn = false; console.error('[Shader Lab] Shadow map error, falling back to screen-space shadows:', e); }
      N.bindFramebuffer.call(gl, 36160, s.fbo);
      s.actualDraw = s.fbo;
    } else if (s.managed) {
      s.managed = false;
      N.bindFramebuffer.call(gl, 36160, null);
      s.actualDraw = null;
    }
  }

  function failRuntime(gl, s, err) {
    console.error('[Shader Lab] Error, shader disabled:', err);
    s.failed = true;
    statusText = 'error';
    if (s.managed) {
      s.managed = false;
      try { N.bindFramebuffer.call(gl, 36160, s.logicalDraw); s.actualDraw = s.logicalDraw; } catch (e) {}
    }
  }

  function ensureTargets(gl, s) {
    const W = gl.drawingBufferWidth, H = gl.drawingBufferHeight;
    if (s.fbo && s.w === W && s.h === H) return;
    const prevTex = gl.getParameter(gl.TEXTURE_BINDING_2D);
    if (s.fbo) { gl.deleteFramebuffer(s.fbo); gl.deleteTexture(s.colorTex); gl.deleteTexture(s.depthTex); }
    if (s.snapFbo) { gl.deleteFramebuffer(s.snapFbo); gl.deleteTexture(s.snapTex); s.snapFbo = null; s.snapTex = null; }
    if (s.shFbo) { gl.deleteFramebuffer(s.shFbo); gl.deleteTexture(s.shTex); s.shFbo = null; s.shTex = null; }
    s.colorTex = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, s.colorTex);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, W, H, 0, gl.RGBA, gl.UNSIGNED_BYTE, null);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    s.depthTex = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, s.depthTex);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.DEPTH24_STENCIL8, W, H, 0, gl.DEPTH_STENCIL, gl.UNSIGNED_INT_24_8, null);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.bindTexture(gl.TEXTURE_2D, prevTex);
    s.fbo = gl.createFramebuffer();
    N.bindFramebuffer.call(gl, 36160, s.fbo);
    gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, s.colorTex, 0);
    gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.DEPTH_STENCIL_ATTACHMENT, gl.TEXTURE_2D, s.depthTex, 0);
    if (gl.checkFramebufferStatus(gl.FRAMEBUFFER) !== gl.FRAMEBUFFER_COMPLETE) throw new Error('Framebuffer incomplete');
    const pt = gl.getParameter(gl.TEXTURE_BINDING_2D);
    s.snapTex = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, s.snapTex);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.DEPTH24_STENCIL8, W, H, 0, gl.DEPTH_STENCIL, gl.UNSIGNED_INT_24_8, null);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.bindTexture(gl.TEXTURE_2D, pt);
    s.snapFbo = gl.createFramebuffer();
    N.bindFramebuffer.call(gl, 36160, s.snapFbo);
    gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.DEPTH_STENCIL_ATTACHMENT, gl.TEXTURE_2D, s.snapTex, 0);
    N.bindFramebuffer.call(gl, 36160, s.fbo);
    const pt2 = gl.getParameter(gl.TEXTURE_BINDING_2D);
    s.shTex = gl.createTexture();
    s.shW = Math.max(1, W >> 1);
    s.shH = Math.max(1, H >> 1);
    gl.bindTexture(gl.TEXTURE_2D, s.shTex);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, s.shW, s.shH, 0, gl.RGBA, gl.UNSIGNED_BYTE, null);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.bindTexture(gl.TEXTURE_2D, pt2);
    s.shFbo = gl.createFramebuffer();
    N.bindFramebuffer.call(gl, 36160, s.shFbo);
    gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, s.shTex, 0);
    if (gl.checkFramebufferStatus(gl.FRAMEBUFFER) !== gl.FRAMEBUFFER_COMPLETE) throw new Error('Shadow framebuffer incomplete');
    N.bindFramebuffer.call(gl, 36160, s.fbo);
    s.w = W; s.h = H;
  }

  const VERT = `#version 300 es
out vec2 vUv;
void main(){
  vec2 p = vec2(float((gl_VertexID << 1) & 2), float(gl_VertexID & 2));
  vUv = p;
  gl_Position = vec4(p * 2.0 - 1.0, 0.0, 1.0);
}`.trim();

  const FRAG = `#version 300 es
precision highp float;
precision highp int;
precision highp sampler2D;
uniform sampler2D uColor;
uniform sampler2D uDepth;
uniform sampler2D uShadow;
uniform sampler2D uLsDepth;
uniform sampler2D uLsDepthP;
uniform sampler2D uLsDepthD;
uniform mat4 uVP;
uniform mat4 uInvVP;
uniform vec3 uCam;
uniform vec2 uRes;
uniform float uMatOk;
uniform float uTime;
uniform float uRays;
uniform float uAnim;
uniform float uDbg;
uniform float uWater;
uniform float uRain;
uniform float uStorm;
uniform mat4 uLsVP;
uniform vec3 uLsInfo;
uniform float uLsOn;
uniform float uShadowK;
in vec2 vUv;
out vec4 fragColor;
const float PI = 3.14159265;

float luma(vec3 c){ return dot(c, vec3(0.2126, 0.7152, 0.0722)); }
float hash12(vec2 p){ vec3 p3 = fract(vec3(p.xyx) * 0.1031); p3 += dot(p3, p3.yzx + 33.33); return fract((p3.x + p3.y) * p3.z); }
float depthAt(vec2 uv){ return textureLod(uDepth, uv, 0.0).r; }
vec3 colAt(vec2 uv){ return textureLod(uColor, uv, 0.0).rgb; }
vec3 worldAt(vec2 uv, float d){
  vec4 w = uInvVP * vec4(uv * 2.0 - 1.0, d * 2.0 - 1.0, 1.0);
  return w.xyz / w.w;
}

float shadowMapOcc(vec3 P, vec3 N, float ndl){
  float texW = uLsInfo.x;
  float sinT = sqrt(max(0.0, 1.0 - ndl * ndl));
  vec3 Po = P + N * (texW * 1.5 + 0.02);
  vec4 lc = uLsVP * vec4(Po, 1.0);
  vec3 ndc = lc.xyz / lc.w;
  vec2 uv = ndc.xy * 0.5 + 0.5;
  float z = ndc.z * 0.5 + 0.5;
  float edge = max(abs(ndc.x), abs(ndc.y));
  if (edge > 0.98 || z < 0.0 || z > 1.0) return 0.0;
  float bias = (0.012 + texW * (0.4 + 1.6 * min(sinT / max(ndl, 0.25), 3.0))) / uLsInfo.y;
  vec2 size = vec2(textureSize(uLsDepth, 0));
  vec2 tc = uv * size - 0.5;
  vec2 base = floor(tc);
  vec2 fr = fract(tc);
  vec2 inv = 1.0 / size;
  float o00 = 0.0, o10 = 0.0, o01 = 0.0, o11 = 0.0;
  vec2 q00 = (base + 0.5) * inv;
  float d00 = min(min(textureLod(uLsDepth, q00, 0.0).r, textureLod(uLsDepthP, q00, 0.0).r), textureLod(uLsDepthD, q00, 0.0).r);
  vec2 q10 = q00 + vec2(inv.x, 0.0);
  float d10 = min(min(textureLod(uLsDepth, q10, 0.0).r, textureLod(uLsDepthP, q10, 0.0).r), textureLod(uLsDepthD, q10, 0.0).r);
  vec2 q01 = q00 + vec2(0.0, inv.y);
  float d01 = min(min(textureLod(uLsDepth, q01, 0.0).r, textureLod(uLsDepthP, q01, 0.0).r), textureLod(uLsDepthD, q01, 0.0).r);
  vec2 q11 = q00 + inv;
  float d11 = min(min(textureLod(uLsDepth, q11, 0.0).r, textureLod(uLsDepthP, q11, 0.0).r), textureLod(uLsDepthD, q11, 0.0).r);
  o00 = step(d00 + bias, z);
  o10 = step(d10 + bias, z);
  o01 = step(d01 + bias, z);
  o11 = step(d11 + bias, z);
  float occ = mix(mix(o00, o10, fr.x), mix(o01, o11, fr.x), fr.y);
  occ = smoothstep(0.30, 0.70, occ);
  float fade = 1.0 - smoothstep(0.80, 0.98, edge);
  return occ * fade;
}

float shadowBlur(vec2 uv, float dist){
  vec2 px = 1.0 / uRes;
  float acc = 0.0, wsum = 0.0;
  for (int i = 0; i < 9; i++) {
    float fi = float(i);
    float ang = fi * 2.399963;
    float r = sqrt((fi + 0.5) / 9.0) * 2.8;
    vec2 suv = uv + vec2(cos(ang), sin(ang)) * r * px;
    vec4 t = textureLod(uShadow, suv, 0.0);
    float ds = depthAt(suv);
    float dd = distance(uCam, worldAt(suv, ds)) - dist;
    float w = t.g * exp(-dd * dd / (0.04 + dist * 0.012)) * exp(-r * r / 5.0);
    acc += t.r * w;
    wsum += w;
  }
  return wsum > 1e-4 ? acc / wsum : 0.0;
}

float vnoise(vec2 p){
  vec2 i = floor(p), f = fract(p);
  f = f * f * (3.0 - 2.0 * f);
  float a = hash12(i), b = hash12(i + vec2(1.0, 0.0)), c = hash12(i + vec2(0.0, 1.0)), d = hash12(i + vec2(1.0, 1.0));
  return mix(mix(a, b, f.x), mix(c, d, f.x), f.y);
}
float fbm(vec2 p){
  float v = 0.0, a = 0.5;
  for (int i = 0; i < 5; i++) { v += a * vnoise(p); p = p * 2.03 + 17.1; a *= 0.5; }
  return v;
}

vec3 skyCol(vec3 dir, vec3 game, float e, vec3 body, bool isDay){
  float h = clamp(dir.y, 0.0, 1.0);
  float sd = max(dot(dir, body), 0.0);
  float dayW = smoothstep(0.02, 0.40, e);
  float duskW = smoothstep(-0.28, 0.0, e);
  float gameW = smoothstep(0.08, 0.42, e);

  vec3 night = mix(vec3(0.035, 0.055, 0.13), vec3(0.008, 0.012, 0.04), pow(h, 0.5));
  vec2 sp = dir.xz / (abs(dir.y) + 0.25) * 90.0;
  vec2 cell = floor(sp);
  float star = step(0.9965, hash12(cell)) * smoothstep(0.02, 0.25, dir.y);
  star *= (0.5 + 0.5 * hash12(cell + 7.0)) * (0.75 + 0.25 * sin(uAnim * 2.0 + hash12(cell + 3.0) * 30.0));
  night += vec3(star);

  vec3 dusk = mix(vec3(1.0, 0.48, 0.22), vec3(0.16, 0.20, 0.42), pow(h, 0.45));
  dusk += vec3(1.0, 0.55, 0.25) * pow(sd, 6.0) * 0.6;
  vec3 dayC = mix(vec3(0.74, 0.86, 1.0), vec3(0.22, 0.46, 0.92), pow(h, 0.55));
  dayC += vec3(1.0, 0.9, 0.7) * pow(sd, 8.0) * 0.18;

  vec3 s = mix(night, dusk, duskW);
  s = mix(s, dayC, dayW);

  float ch = smoothstep(0.02, 0.22, dir.y);
  vec2 cp = dir.xz / (dir.y + 0.18) * 1.6 + vec2(uAnim * 0.012, uAnim * 0.004);
  float cn = fbm(cp);
  float cd = smoothstep(0.48, 0.78, cn) * ch;
  float shade = mix(1.0, 0.78, smoothstep(0.55, 0.9, cn));
  vec3 cDay = vec3(1.0) * shade;
  vec3 cDusk = mix(vec3(1.0, 0.55, 0.35), vec3(0.75, 0.50, 0.60), h) * shade;
  vec3 cNight = vec3(0.10, 0.12, 0.20) * shade + vec3(0.25, 0.30, 0.45) * pow(sd, 6.0) * (isDay ? 0.0 : 1.0);
  vec3 cloudCol = mix(cNight, cDusk, duskW);
  cloudCol = mix(cloudCol, cDay, dayW);
  s = mix(s, cloudCol, cd * 0.92);

  vec3 outc = mix(s, game, gameW);

  vec3 rt = normalize(cross(vec3(0.0, 1.0, 0.0), body));
  vec3 upv = cross(body, rt);
  vec2 bp = vec2(dot(dir, rt), dot(dir, upv));
  float front = step(0.0, dot(dir, body));
  float rad = length(bp);
  float clear = 1.0 - cd * 0.75 * (1.0 - gameW);

  if (isDay) {
    float disc = (1.0 - smoothstep(0.045, 0.052, rad)) * front;
    float ring = smoothstep(0.045, 0.054, rad) * (1.0 - smoothstep(0.054, 0.10, rad)) * front;
    outc += vec3(1.0, 0.95, 0.75) * 2.5 * disc * clear;
    outc += vec3(1.0, 0.58, 0.22) * ring * 0.7 * clear;
    outc += vec3(1.0, 0.8, 0.5) * (pow(sd, 16.0) * 0.45 + pow(sd, 6.0) * 0.1);
  } else {
    float d1 = rad - 0.05;
    float d2 = length(bp - vec2(0.03, 0.012)) - 0.046;
    float cres = (1.0 - smoothstep(-0.002, 0.002, max(d1, -d2))) * front;
    outc = mix(outc, vec3(0.95, 0.97, 1.0) * 1.6, cres * clear);
    outc += vec3(0.5, 0.6, 1.0) * pow(sd, 60.0) * 0.15;
  }
  return outc;
}

float sceneDiff(vec3 S, out vec2 suv){
  suv = vec2(0.0);
  vec4 cs = uVP * vec4(S, 1.0);
  if (cs.w <= 0.0001) return -1000.0;
  vec2 ndc = cs.xy / cs.w;
  if (abs(ndc.x) >= 1.0 || abs(ndc.y) >= 1.0) return -1000.0;
  suv = ndc * 0.5 + 0.5;
  float sd = depthAt(suv);
  if (sd > 0.99995) return -500.0;
  vec3 Q = worldAt(suv, sd);
  return distance(uCam, S) - distance(uCam, Q);
}

vec3 waterShade(vec3 Pw, float e, vec3 body, bool isDay, float expo, float strength, out float k){
  vec3 V = normalize(Pw - uCam);
  float amp = 0.05 + 0.10 * uRain;
  vec2 rp = Pw.xz * 1.7 + uAnim * vec2(0.6, 0.4);
  float n1 = vnoise(rp) - 0.5;
  float n2 = vnoise(rp * 1.9 + 5.0 + uAnim * 0.3) - 0.5;
  vec3 Nw = normalize(vec3(n1 * amp, 1.0, n2 * amp));
  vec3 Rf = reflect(V, Nw);
  Rf.y = abs(Rf.y);
  vec3 o = Pw + Nw * 0.06;
  vec2 hitUv = vec2(0.0);
  bool found = false;
  const int NW = 32;
  float jit = hash12(gl_FragCoord.xy);
  float prev = 0.0;
  for (int i = 0; i < NW; i++) {
    float t = (float(i) + jit) / float(NW);
    float rd = 0.12 + t * t * 50.0;
    vec2 suv;
    float df = sceneDiff(o + Rf * rd, suv);
    if (df < -900.0) break;
    if (df > -400.0) {
      float thick = 0.6 + rd * 0.1;
      if (df > 0.02 && df < thick) {
        float lo = prev;
        float hi = rd;
        hitUv = suv;
        for (int j = 0; j < 4; j++) {
          float mid = 0.5 * (lo + hi);
          vec2 mu;
          float dm = sceneDiff(o + Rf * mid, mu);
          if (dm < -400.0) break;
          if (dm > 0.0) { hi = mid; hitUv = mu; } else { lo = mid; }
        }
        found = true;
        break;
      }
    }
    prev = rd;
  }
  float dayF2 = smoothstep(-0.10, 0.28, e);
  vec3 refl;
  if (found) {
    refl = colAt(hitUv) * expo;
  } else {
    refl = skyCol(Rf, vec3(0.5, 0.7, 1.0), e, body, isDay);
    vec3 rc = vec3(0.50, 0.54, 0.60) * mix(0.30, 1.0, dayF2);
    refl = mix(refl, rc, uRain * 0.93);
    if (isDay) {
      float sp = pow(max(dot(Rf, body), 0.0), 400.0) * (1.0 - clamp(uRain, 0.0, 1.0));
      refl += vec3(1.0, 0.9, 0.7) * sp * 4.0;
    }
  }
  float fres = 0.04 + 0.96 * pow(1.0 - clamp(dot(-V, Nw), 0.0, 1.0), 5.0);
  k = clamp(0.12 + 0.88 * fres, 0.0, 0.85) * strength;
  return refl;
}

float rainLayer(vec2 uv, float scale, float speed){
  vec2 p = uv * vec2(uRes.x / uRes.y, 1.0);
  p.x += p.y * 0.18;
  vec2 g = vec2(p.x * scale, p.y * scale * 0.09 + uAnim * speed);
  vec2 id = floor(g);
  vec2 f = fract(g);
  float on = step(0.86, hash12(id));
  float ox = 0.2 + 0.6 * hash12(id + 7.0);
  float line = 1.0 - smoothstep(0.0, 0.07, abs(f.x - ox));
  float tail = smoothstep(0.0, 0.05, f.y) * (1.0 - smoothstep(0.05, 0.8, f.y));
  return on * line * tail;
}

float rainRipple(vec2 xz){
  vec2 g = xz / 0.55;
  vec2 id = floor(g);
  vec2 f = fract(g);
  float h = hash12(id + 21.0);
  float on = step(0.45, h);
  vec2 c = vec2(0.25 + 0.5 * hash12(id + 3.0), 0.25 + 0.5 * hash12(id + 9.0));
  float T = 0.9 + 0.8 * hash12(id + 5.0);
  float ph = fract(uAnim / T + h * 7.0);
  float R = ph * 0.30;
  float d = abs(length(f - c) - R);
  float ring = (1.0 - smoothstep(0.0, 0.035, d)) * (1.0 - ph) * (1.0 - ph);
  return on * ring;
}

float rainLayerW(vec3 dir, float distLimit, float cs, int nSteps, float dmin, float fw, float dmax, float lenScale, float dens){
  vec2 hd = dir.xz;
  float s = length(hd);
  if (s < 1e-3) return 0.0;
  vec2 h = hd / s;
  float slope = dir.y / s;
  vec2 o = uCam.xz;
  vec2 p = o / cs;
  vec2 cell = floor(p);
  vec2 sg = vec2(h.x >= 0.0 ? 1.0 : -1.0, h.y >= 0.0 ? 1.0 : -1.0);
  vec2 tD = 1.0 / max(abs(h), vec2(1e-4));
  vec2 tM = vec2(h.x >= 0.0 ? cell.x + 1.0 - p.x : p.x - cell.x, h.y >= 0.0 ? cell.y + 1.0 - p.y : p.y - cell.y) * tD;
  float pa = 1.4 / uRes.y;
  float lim = min(dmax, distLimit);
  const float PER = 16.0;
  vec2 wind = vec2(0.10, 0.04) * (1.0 + 0.8 * uStorm);
  float acc = 0.0;
  float tPrev = 0.0;
  for (int i = 0; i < 40; i++) {
    if (i >= nSteps || tPrev * cs > lim) break;
    float h1 = hash12(cell + 11.7);
    if (h1 < dens) {
      float h2 = hash12(cell + 37.1);
      float h3 = hash12(cell + 73.9);
      float h4 = hash12(cell + 5.3);
      float h5 = hash12(cell + 91.7);
      float h6 = hash12(cell + 29.3);
      vec2 rel = (cell + vec2(0.15 + 0.7 * h2, 0.15 + 0.7 * h3)) * cs - o;
      float u = dot(rel, h);
      if (u > dmin && u < lim) {
        float perp = abs(rel.x * h.y - rel.y * h.x);
        float w = 0.008 + pa * u * 0.9;
        if (perp < w + 0.2) {
          float sp = 8.5 + 4.5 * h4;
          float dlen = (0.55 + 0.9 * h5) * lenScale;
          float yr = uCam.y + slope * u;
          float yd0 = h6 * PER - mod(sp * uAnim, PER);
          float yd = yr + mod(yd0 - yr + 0.5 * PER, PER) - 0.5 * PER;
          float tt = (yr - yd) / dlen;
          if (tt > -0.05 && tt < 1.0) {
            vec2 rel2 = rel - wind * (yr - yd);
            float perp2 = abs(rel2.x * h.y - rel2.y * h.x);
            float cov = smoothstep(-0.05, 0.03, tt) * (1.0 - smoothstep(0.7, 1.0, tt)) * (1.0 - 0.5 * tt);
            float a = (1.0 - smoothstep(0.0, w, perp2)) * cov;
            a *= clamp(0.012 / w, 0.2, 1.0);
            a *= smoothstep(dmin, dmin + fw, u) * (1.0 - smoothstep(dmax * 0.8, dmax, u)) * exp(-u * 0.02);
            acc += a * (0.6 + 0.4 * hash12(cell + 53.3));
          }
        }
      }
    }
    tPrev = min(tM.x, tM.y);
    if (tM.x < tM.y) { cell.x += sg.x; tM.x += tD.x; } else { cell.y += sg.y; tM.y += tD.y; }
  }
  return acc;
}

float rainVolume(vec3 dir, float distLimit){
  float k = clamp(uRain, 0.0, 1.0);
  float r = rainLayerW(dir, distLimit, 0.5, 26, 0.3, 0.7, 18.0, 1.0, k * 0.8);
  r += rainLayerW(dir, distLimit, 2.0, 22, 14.0, 4.0, 60.0, 2.4, k * 0.9);
  return r * 0.7;
}

void main(){
  vec2 px = 1.0 / uRes;
  vec3 c = colAt(vUv);
  vec3 c0 = c;
  float d = depthAt(vUv);
  bool isSky = d > 0.99995;
  float waterK = 0.0;
  vec3 waterRef = vec3(0.0);
  float dbgWater = 0.0;
  float rainWet = 0.0;
  float rippleV = 0.0;
  float puddleK = 0.0;
  vec3 puddleRef = vec3(0.0);
  float dbgOccl = 0.0;
  float dbgDirect = 0.72;
  vec3 dbgN = vec3(0.5);

  float nt = mod(uTime - 6.0, 24.0);
  bool isDay = nt < 12.0;
  float a = (isDay ? nt : nt - 12.0) / 12.0 * PI;
  float e = isDay ? sin(a) : -sin(a);
  vec3 body = normalize(vec3(-cos(a), sin(a) + 0.02, 0.35));
  vec3 L = normalize(vec3(-cos(a), max(sin(a), 0.14), 0.35));
  float dayF = smoothstep(-0.10, 0.28, e);
  vec3 sunCol = mix(vec3(0.55, 0.68, 1.10),
                    mix(vec3(1.30, 0.72, 0.42), vec3(1.05, 1.00, 0.92), smoothstep(0.10, 0.55, e)),
                    smoothstep(-0.10, 0.15, e));
  vec3 ambCol = mix(vec3(0.55, 0.68, 1.10), vec3(0.88, 0.94, 1.06), dayF);
  float expo = mix(0.42, 1.0, dayF);
  expo *= 1.0 - 0.28 * uRain - 0.15 * uStorm;
  float wxDist = 60.0;

  vec2 sunUV = vec2(0.5);
  float sunVis = 0.0;
  if (uMatOk > 0.5) {
    vec4 cs = uVP * vec4(body, 0.0);
    if (cs.w > 0.0001) { sunUV = cs.xy / cs.w * 0.5 + 0.5; sunVis = 1.0; }
  } else {
    sunUV = vec2(0.5) + vec2(-cos(a) * 0.40, 0.06 + 0.42 * sin(a));
    sunVis = 1.0;
  }

  if (isSky) {
    if (uMatOk > 0.5) {
      vec3 n0 = worldAt(vUv, 0.0);
      vec3 n1 = worldAt(vUv, 0.9);
      c = skyCol(normalize(n1 - n0), c, e, body, isDay);
    } else {
      c *= mix(ambCol, sunCol, 0.72) * expo;
    }
  } else {
    float direct = 0.72;
    if (uMatOk > 0.5) {
      vec3 Pw = worldAt(vUv, d);
      float dist = distance(uCam, Pw);
      wxDist = dist;
      float dl = depthAt(vUv - vec2(px.x, 0.0));
      float dr = depthAt(vUv + vec2(px.x, 0.0));
      float du = depthAt(vUv + vec2(0.0, px.y));
      float dd = depthAt(vUv - vec2(0.0, px.y));
      vec3 Pl = worldAt(vUv - vec2(px.x, 0.0), dl);
      vec3 Pr = worldAt(vUv + vec2(px.x, 0.0), dr);
      vec3 Pu = worldAt(vUv + vec2(0.0, px.y), du);
      vec3 Pd = worldAt(vUv - vec2(0.0, px.y), dd);
      vec3 gx = abs(d - dr) < abs(d - dl) ? (Pr - Pw) : (Pw - Pl);
      vec3 gy = abs(d - du) < abs(d - dd) ? (Pu - Pw) : (Pw - Pd);
      vec3 cr = cross(gx, gy);
      float cl = length(cr);
      vec3 Nn = cl > 1e-9 ? cr / cl : vec3(0.0, 1.0, 0.0);
      if (dot(Nn, uCam - Pw) < 0.0) Nn = -Nn;
      if ((uWater > 0.001 || uDbg > 3.5) && Nn.y > 0.85 && c0.b > c0.r * 1.3 && c0.b > c0.g * 1.35 && c0.b > 0.22) {
        dbgWater = 1.0;
        if (uWater > 0.001) waterRef = waterShade(Pw, e, body, isDay, expo, uWater, waterK);
      }
      if (uRain > 0.001 && Nn.y > 0.85) {
        float wn = vnoise(Pw.xz * 0.55 + 3.0);
        rippleV = rainRipple(Pw.xz) * uRain;
        rainWet = uRain * (0.5 + 0.5 * wn);
        float pm = smoothstep(0.60, 0.68, wn) * uRain;
        if (pm > 0.01 && dbgWater < 0.5) {
          puddleRef = waterShade(Pw, e, body, isDay, expo, 0.85, puddleK);
          puddleK *= pm;
        }
      }
      if (dist < 160.0) {
        float ndl = dot(Nn, L);
        float occl = 0.0;
        if (uLsOn > 0.5) { if (ndl > 0.02) occl = shadowMapOcc(Pw, Nn, ndl); }
        else if (ndl > 0.02) occl = shadowBlur(vUv, dist);
        occl *= uShadowK;
        float dv = clamp(ndl, 0.0, 1.0) * (1.0 - occl);
        dbgOccl = occl;
        dbgN = Nn * 0.5 + 0.5;
        float fade = smoothstep(0.4, 1.0, dist) * (1.0 - smoothstep(50.0, 110.0, dist));
        direct = mix(0.72, dv, fade);
        dbgDirect = direct;
      }
    }
    float sunI = mix(0.35, 1.0, smoothstep(-0.05, 0.30, e)) * (1.0 - 0.8 * clamp(uRain, 0.0, 1.0));
    float amb = 0.5;
    float litv = amb + (1.0 - amb) * direct * sunI;
    float fullv = amb + (1.0 - amb) * sunI;
    c *= mix(1.0, litv / fullv, 0.9);
    vec3 tint = mix(ambCol, sunCol, clamp(direct, 0.0, 1.0));
    c *= tint / max(tint.r, max(tint.g, tint.b)) * expo;
    if (waterK > 0.0) c = mix(c, waterRef, waterK);
    if (rainWet > 0.0) {
      c *= 1.0 - 0.28 * rainWet;
      c += vec3(0.70, 0.78, 0.90) * rippleV * 0.35;
      if (puddleK > 0.0) c = mix(c, puddleRef, puddleK);
    }
  }

  if (uRain > 0.001) {
    float dEye = isSky ? 400.0 : wxDist;
    vec3 rainCol = vec3(0.50, 0.54, 0.60) * mix(0.30, 1.0, dayF) * (1.0 - 0.25 * uStorm);
    vec3 rdir = vec3(0.0, 1.0, 0.0);
    if (uMatOk > 0.5) rdir = normalize(worldAt(vUv, 0.9) - worldAt(vUv, 0.0));
    float lm = luma(c);
    c = mix(c, vec3(lm), uRain * 0.5);
    c *= 1.0 - uRain * 0.30;
    if (isSky) {
      float ov = 0.75 + 0.5 * fbm(rdir.xz / (abs(rdir.y) + 0.3) * 1.2 + vec2(uAnim * 0.02, 0.0));
      c = mix(c, rainCol * ov, uRain * 0.95);
    } else {
      c = mix(c, rainCol, 1.0 - exp(-dEye * 0.014 * uRain));
    }
    float rs;
    if (uMatOk > 0.5) {
      rs = rainVolume(rdir, dEye);
    } else {
      rs = rainLayer(vUv, 90.0, 3.2) + rainLayer(vUv + 0.13, 150.0, 4.5) * 0.7 + rainLayer(vUv + 0.31, 55.0, 2.4) * 0.9;
    }
    c += vec3(0.75, 0.82, 0.95) * mix(0.35, 1.0, dayF) * rs * uRain * 0.9;
  }
  if (uStorm > 0.001) {
    float fid = floor(uAnim * 0.22);
    float ft = fract(uAnim * 0.22);
    float ev = step(0.7, hash12(vec2(fid, 1.7)));
    float fl = ev * exp(-ft * 18.0) * (0.65 + 0.35 * sin(ft * 90.0));
    c += vec3(0.75, 0.82, 1.0) * fl * uStorm * 0.7;
  }

  float rayK = uRays * (1.0 - clamp(uRain, 0.0, 1.0));
  float dayVis = smoothstep(-0.02, 0.12, e);
  if (rayK > 0.001 && dayVis > 0.0 && sunVis > 0.5) {
    const int NR = 16;
    vec2 dv2 = (sunUV - vUv) / float(NR);
    vec2 p = vUv + dv2 * hash12(gl_FragCoord.xy + 3.0);
    float w = 1.0, acc = 0.0, wsum = 0.0;
    for (int i = 0; i < NR; i++) {
      p += dv2;
      float ok = step(0.99995, depthAt(p));
      acc += ok * w; wsum += w; w *= 0.91;
    }
    float rays = acc / wsum;
    float off = max(abs(sunUV.x - 0.5), abs(sunUV.y - 0.5)) * 2.0;
    rays *= 1.0 - smoothstep(1.2, 2.4, off);
    float fall = exp(-2.2 * length((vUv - sunUV) * vec2(uRes.x / uRes.y, 1.0)));
    rays *= 0.25 + 0.75 * fall;
    c += rays * rayK * dayVis * sunCol * 0.9;
  }

  float l = luma(c);
  c = mix(vec3(l), c, 1.08);
  vec2 q = vUv - 0.5;
  c *= clamp(1.0 - dot(q, q) * 0.45, 0.0, 1.0);
  c += (hash12(gl_FragCoord.xy) - 0.5) / 255.0;
  if (uDbg > 0.5) {
    if (uDbg < 1.5) c = isSky ? vec3(1.0, 0.0, 0.0) : vec3(0.0, 0.6, 0.0);
    else if (uDbg < 2.5) c = dbgN;
    else if (uDbg < 3.5) c = vec3(dbgOccl, dbgDirect, uMatOk);
    else c = vec3(dbgWater);
  }
  fragColor = vec4(c, 1.0);
}`.trim();


  const SH_FRAG = `#version 300 es
precision highp float;
precision highp int;
precision highp sampler2D;
uniform sampler2D uDepth;
uniform mat4 uVP;
uniform mat4 uInvVP;
uniform vec3 uCam;
uniform vec2 uRes;
uniform float uMatOk;
uniform float uTime;
in vec2 vUv;
out vec4 fragColor;
const float PI = 3.14159265;

float ign(vec2 p){ return fract(52.9829189 * fract(dot(p, vec2(0.06711056, 0.00583715)))); }
float depthAt(vec2 uv){ return textureLod(uDepth, uv, 0.0).r; }
vec3 worldAt(vec2 uv, float d){
  vec4 w = uInvVP * vec4(uv * 2.0 - 1.0, d * 2.0 - 1.0, 1.0);
  return w.xyz / w.w;
}

float shadowRay(vec3 P, vec3 N, vec3 L, float jit){
  vec3 o = P + N * 0.04 + L * 0.04;
  float best = 0.0;
  const int NS = 18;
  float maxD = 20.0;
  for (int i = 0; i < NS; i++) {
    float t = (float(i) + jit) / float(NS);
    float rd = 0.12 + t * t * maxD;
    vec3 S = o + L * rd;
    vec4 cs = uVP * vec4(S, 1.0);
    if (cs.w <= 0.0001) break;
    vec2 ndc = cs.xy / cs.w;
    if (abs(ndc.x) >= 1.0 || abs(ndc.y) >= 1.0) break;
    vec2 suv = ndc * 0.5 + 0.5;
    float sd = depthAt(suv);
    if (sd > 0.99995) continue;
    vec3 Q = worldAt(suv, sd);
    float diff = distance(uCam, S) - distance(uCam, Q);
    float thick = 1.6 + rd * 0.12;
    float occ = smoothstep(0.04, 0.22, diff) * (1.0 - smoothstep(thick * 0.8, thick, diff));
    best = max(best, occ);
    if (best > 0.99) break;
  }
  return best;
}

void main(){
  float d = depthAt(vUv);
  if (uMatOk < 0.5 || d > 0.99995) { fragColor = vec4(0.0); return; }
  vec2 px = 1.0 / uRes;
  float nt = mod(uTime - 6.0, 24.0);
  bool isDay = nt < 12.0;
  float a = (isDay ? nt : nt - 12.0) / 12.0 * PI;
  vec3 L = normalize(vec3(-cos(a), max(sin(a), 0.14), 0.35));
  vec3 Pw = worldAt(vUv, d);
  float dist = distance(uCam, Pw);
  float dl = depthAt(vUv - vec2(px.x, 0.0));
  float dr = depthAt(vUv + vec2(px.x, 0.0));
  float du = depthAt(vUv + vec2(0.0, px.y));
  float dd = depthAt(vUv - vec2(0.0, px.y));
  vec3 Pl = worldAt(vUv - vec2(px.x, 0.0), dl);
  vec3 Pr = worldAt(vUv + vec2(px.x, 0.0), dr);
  vec3 Pu = worldAt(vUv + vec2(0.0, px.y), du);
  vec3 Pd = worldAt(vUv - vec2(0.0, px.y), dd);
  vec3 gx = abs(d - dr) < abs(d - dl) ? (Pr - Pw) : (Pw - Pl);
  vec3 gy = abs(d - du) < abs(d - dd) ? (Pu - Pw) : (Pw - Pd);
  vec3 cr = cross(gx, gy);
  float cl = length(cr);
  vec3 Nn = cl > 1e-9 ? cr / cl : vec3(0.0, 1.0, 0.0);
  if (dot(Nn, uCam - Pw) < 0.0) Nn = -Nn;
  float occl = 0.0;
  if (dist < 160.0) {
    float ndl = dot(Nn, L);
    if (ndl > 0.02) occl = shadowRay(Pw, Nn, L, ign(gl_FragCoord.xy));
  }
  fragColor = vec4(occl, 1.0, 0.0, 1.0);
}`.trim();

  function compile(gl, type, src) {
    const sh = gl.createShader(type);
    N.shaderSource.call(gl, sh, src);
    gl.compileShader(sh);
    if (!gl.getShaderParameter(sh, gl.COMPILE_STATUS)) throw new Error(gl.getShaderInfoLog(sh));
    return sh;
  }

  function ensureProgram(gl, s) {
    if (s.prog) return;
    const p = gl.createProgram();
    gl.attachShader(p, compile(gl, gl.VERTEX_SHADER, VERT));
    gl.attachShader(p, compile(gl, gl.FRAGMENT_SHADER, FRAG));
    gl.linkProgram(p);
    if (!gl.getProgramParameter(p, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(p));
    s.prog = p;
    s.U = {};
    for (const n of ['uColor', 'uDepth', 'uVP', 'uInvVP', 'uCam', 'uRes', 'uMatOk', 'uTime', 'uRays', 'uAnim', 'uDbg', 'uShadow', 'uWater', 'uRain', 'uStorm', 'uLsDepth', 'uLsDepthP', 'uLsDepthD', 'uLsVP', 'uLsInfo', 'uLsOn', 'uShadowK']) {
      s.U[n] = N.getUniformLocation.call(gl, p, n);
    }
    s.vao = gl.createVertexArray();
    const q = gl.createProgram();
    gl.attachShader(q, compile(gl, gl.VERTEX_SHADER, VERT));
    gl.attachShader(q, compile(gl, gl.FRAGMENT_SHADER, SH_FRAG));
    gl.linkProgram(q);
    if (!gl.getProgramParameter(q, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(q));
    s.shProg = q;
    s.shU = {};
    for (const n of ['uDepth', 'uVP', 'uInvVP', 'uCam', 'uRes', 'uMatOk', 'uTime']) {
      s.shU[n] = N.getUniformLocation.call(gl, q, n);
    }
  }

  function seedUbo(gl, b) {
    SEEDED.add(b);
    const prev = gl.getParameter(36662);
    N.bindBuffer.call(gl, 36662, b);
    let sz = 0;
    try {
      sz = gl.getBufferParameter(36662, 34660) || 0;
      if (sz > 0 && sz <= UBO_MAX) {
        const arr = new Float32Array(sz >> 2);
        gl.getBufferSubData(36662, 0, arr);
        UBUF.set(b, arr);
        UVER.set(b, (UVER.get(b) || 0) + 1);
      }
    } catch (e) {}
    N.bindBuffer.call(gl, 36662, prev);
    return sz;
  }

  function ensureUbuf(gl, b) {
    if (b && !UBUF.has(b) && !SEEDED.has(b)) seedUbo(gl, b);
  }

  function bootstrapGL(gl, s) {
    if (s.boot) return;
    s.boot = true;
    try {
      s.curProg = gl.getParameter(35725);
      const fb = gl.getParameter(36006);
      s.logicalDraw = fb;
      s.actualDraw = fb;
      const ub = ubOf(gl);
      ub.cur = gl.getParameter(35368);
      const n = Math.min(gl.getParameter(35375) || 0, 96);
      for (let i = 0; i < n; i++) {
        const b = gl.getIndexedParameter(35368, i);
        if (!b) continue;
        const off = gl.getIndexedParameter(35369, i) || 0;
        const size = gl.getIndexedParameter(35370, i) || 0;
        const bs = SEEDED.has(b) ? 0 : seedUbo(gl, b);
        ub.bind[i] = { buf: b, off, size: size > 0 && !(off === 0 && bs > 0 && size >= bs) ? size : undefined };
      }
      if (ub.cur) ensureUbuf(gl, ub.cur);
    } catch (e) {
      console.warn('[Shader Lab] GL state bootstrap failed:', e);
    }
  }

  function v3norm(v) { const l = Math.hypot(v[0], v[1], v[2]) || 1; return [v[0] / l, v[1] / l, v[2] / l]; }
  function v3cross(a, b) { return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]; }
  function v3dot(a, b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }

  function sunDirFor(time) {
    const nt = ((time - 6) % 24 + 24) % 24;
    const isDay = nt < 12;
    const a = (isDay ? nt : nt - 12) / 12 * Math.PI;
    return v3norm([-Math.cos(a), Math.max(Math.sin(a), 0.14), 0.35]);
  }

  const TRACK_CAPS = [2929, 3042, 2884, 3089, 32823];
  const EPOCH_MS = 20000;
  const SNAP_G = 16;

  function syncGs(gl, s) {
    const g = s.gs;
    for (const c of TRACK_CAPS) g.caps[c] = gl.isEnabled(c);
    g.depthMask = !!gl.getParameter(2930);
    g.depthFunc = gl.getParameter(2932);
    g.clearDepth = gl.getParameter(2931);
    const v = gl.getParameter(2978);
    g.vp = [v[0], v[1], v[2], v[3]];
  }

  function rowsToMat(rows) {
    const m = new Float32Array(16);
    for (let r = 0; r < 4; r++) for (let c = 0; c < 4; c++) m[c * 4 + r] = rows[r][c];
    return m;
  }

  function makeAnchor(cam, key) {
    const L = sunDirFor(S.time);
    const f = [-L[0], -L[1], -L[2]];
    const up = Math.abs(f[1]) > 0.99 ? [0, 0, 1] : [0, 1, 0];
    const r = v3norm(v3cross(f, up));
    const u = v3cross(r, f);
    return {
      key, r, u, f,
      a: Math.round(v3dot(cam, r) / SNAP_G) * SNAP_G,
      b: Math.round(v3dot(cam, u) / SNAP_G) * SNAP_G,
      tt: Math.round(v3dot(cam, f) / 32) * 32,
    };
  }

  function lightFrame(s) {
    const A = s.lsA;
    const E = s.lsExtent, R = s.lsRange;
    const view = rowsToMat([[A.r[0], A.r[1], A.r[2], -A.a], [A.u[0], A.u[1], A.u[2], -A.b], [-A.f[0], -A.f[1], -A.f[2], A.tt], [0, 0, 0, 1]]);
    const proj = rowsToMat([[1 / E, 0, 0, 0], [0, 1 / E, 0, 0], [0, 0, -1 / R, 0], [0, 0, 0, 1]]);
    return { view, proj, vp: mul(proj, view), texel: 2 * E / s.lsSizeS, range: 2 * R };
  }

  function makeDepthTarget(gl, size) {
    const tex = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, tex);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.DEPTH_COMPONENT24, size, size, 0, gl.DEPTH_COMPONENT, gl.UNSIGNED_INT, null);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    const fbo = gl.createFramebuffer();
    N.bindFramebuffer.call(gl, 36160, fbo);
    gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.TEXTURE_2D, tex, 0);
    gl.drawBuffers([gl.NONE]);
    gl.readBuffer(gl.NONE);
    if (gl.checkFramebufferStatus(gl.FRAMEBUFFER) !== gl.FRAMEBUFFER_COMPLETE) throw new Error('Shadow map framebuffer incomplete');
    return { tex, fbo };
  }

  function ensureShadowTargets(gl, s) {
    if (s.lsFbo) return;
    const prevTex = gl.getParameter(gl.TEXTURE_BINDING_2D);
    const d = makeDepthTarget(gl, s.lsSizeD);
    const a = makeDepthTarget(gl, s.lsSizeS);
    const b = makeDepthTarget(gl, s.lsSizeS);
    const c = makeDepthTarget(gl, s.lsSizeS);
    gl.bindTexture(gl.TEXTURE_2D, prevTex);
    s.lsTex = [d.tex, a.tex, b.tex];
    s.lsScratchFbo = c.fbo;
    s.lsFbo = [d.fbo, a.fbo, b.fbo];
  }

  function clearDepthFbo(gl, fbo, size) {
    N.bindFramebuffer.call(gl, 36160, fbo);
    N.viewport.call(gl, 0, 0, size, size);
    N.clear.call(gl, 256);
  }

  function shiftMap(gl, s, idx, dx, dy) {
    const Z = s.lsSizeS;
    N.bindFramebuffer.call(gl, 36008, s.lsFbo[idx]);
    N.bindFramebuffer.call(gl, 36009, s.lsScratchFbo);
    gl.blitFramebuffer(0, 0, Z, Z, 0, 0, Z, Z, 256, 9728);
    clearDepthFbo(gl, s.lsFbo[idx], Z);
    const sx0 = Math.max(0, dx), sx1 = Math.min(Z, Z + dx);
    const sy0 = Math.max(0, dy), sy1 = Math.min(Z, Z + dy);
    if (sx1 > sx0 && sy1 > sy0) {
      N.bindFramebuffer.call(gl, 36008, s.lsScratchFbo);
      N.bindFramebuffer.call(gl, 36009, s.lsFbo[idx]);
      gl.blitFramebuffer(sx0, sy0, sx1, sy1, sx0 - dx, sy0 - dy, sx1 - dx, sy1 - dy, 256, 9728);
    }
  }

  function beginShadow(gl, s) {
    s.lsOn = false;
    if (S.shadow <= 0.001 || s.lsBroken || !s.matOk) return;
    ensureShadowTargets(gl, s);
    const cam = s.cam;
    const key = Math.round(S.time * 20);
    const lc = s.lsLastCam;
    s.lsLastCam = [cam[0], cam[1], cam[2]];
    let A = s.lsA;
    let reset = false;
    const camRel = Math.abs(cam[0]) + Math.abs(cam[1]) + Math.abs(cam[2]) < 1e-3;
    if (!A || A.key !== key || camRel || (lc && Math.hypot(cam[0] - lc[0], cam[1] - lc[1], cam[2] - lc[2]) > 3)) {
      A = s.lsA = makeAnchor(cam, key);
      reset = true;
    }
    let sdx = 0, sdy = 0;
    if (!reset) {
      const ca = v3dot(cam, A.r), cb = v3dot(cam, A.u), ct = v3dot(cam, A.f);
      if (Math.abs(ct - A.tt) > 60) {
        A = s.lsA = makeAnchor(cam, key);
        reset = true;
      } else if (Math.abs(ca - A.a) > 24 || Math.abs(cb - A.b) > 24) {
        const na = Math.round(ca / SNAP_G) * SNAP_G;
        const nb = Math.round(cb / SNAP_G) * SNAP_G;
        const T = 2 * s.lsExtent / s.lsSizeS;
        sdx = Math.round((na - A.a) / T);
        sdy = Math.round((nb - A.b) / T);
        A.a = na;
        A.b = nb;
      }
    }
    const g = s.gs;
    const now = performance.now();
    if (g.caps[3089]) N.disable.call(gl, 3089);
    N.depthMask.call(gl, true);
    N.clearDepth.call(gl, 1);
    if (reset) {
      s.lsResets++;
      s.lsEpochT = now;
      s.lsCur = 1;
      s.lsPrev = 2;
      s.lsDirty = false;
      clearDepthFbo(gl, s.lsFbo[1], s.lsSizeS);
      clearDepthFbo(gl, s.lsFbo[2], s.lsSizeS);
    } else {
      if (sdx || sdy) {
        s.lsShifts++;
        shiftMap(gl, s, 1, sdx, sdy);
        shiftMap(gl, s, 2, sdx, sdy);
      }
      if (s.lsDirty && now - s.lsDirtyT > 120) {
        s.lsDirty = false;
        s.lsDirtyT = now;
        s.lsDirtyClears++;
        clearDepthFbo(gl, s.lsFbo[1], s.lsSizeS);
        clearDepthFbo(gl, s.lsFbo[2], s.lsSizeS);
        s.lsEpochT = now;
      }
      if (now - s.lsEpochT > EPOCH_MS) {
        const tmp = s.lsCur;
        s.lsCur = s.lsPrev;
        s.lsPrev = tmp;
        clearDepthFbo(gl, s.lsFbo[s.lsCur], s.lsSizeS);
        s.lsEpochT = now;
      }
    }
    clearDepthFbo(gl, s.lsFbo[0], s.lsSizeD);
    N.depthMask.call(gl, g.depthMask);
    N.clearDepth.call(gl, g.clearDepth);
    if (g.caps[3089]) N.enable.call(gl, 3089);
    N.viewport.call(gl, g.vp[0], g.vp[1], g.vp[2], g.vp[3]);
    s.lsF = lightFrame(s);
    s.lsOn = true;
  }

  function noteDepthClear(gl) {
    if (gl !== gameGL) return;
    const s = ST.get(gl);
    if (s && s.logicalDraw === null && s.segDraws >= 10) s.replayOK = false;
  }

  function findRoles(m) {
    const names = Object.keys(m);
    const find = (re, ex) => names.find((n) => re.test(n) && !(ex && ex.test(n)));
    const r = {};
    const vp = find(/^(u_?)?view_?proj(ection)?(_?matrix)?$/i, /inv|prev|light|shadow/i) || find(/viewproj/i, /world|model|inv|prev|light|shadow/i);
    if (vp) r.vp = vp;
    const view = find(/^(u_?)?view(_?matrix)?$/i, /inv|prev|light|shadow/i);
    const proj = find(/^(u_?)?proj(ection)?(_?matrix)?$/i, /inv|prev|light|shadow/i);
    if (view && proj) { r.view = view; r.proj = proj; }
    const wvp = find(/(world|model)_?view_?proj/i, /inv|prev/i);
    const world = find(/^(u_?)?(world|model)(_?matrix)?$/i, /inv|prev|view/i);
    if (wvp && world) { r.wvp = wvp; r.world = world; }
    if (r.vp || r.view || r.wvp) return r;
    const pk = names.filter((k) => isPersp(m[k]));
    const vk = names.filter((k) => isRigid(m[k]) && !/world|model|inv|prev/i.test(k));
    if (pk.length && vk.length) return { view: vk[0], proj: pk[0] };
    return null;
  }

  function buildPlan(gl, prog, pi) {
    const src = Object.create(null);
    const vals = Object.create(null);
    for (const n in pi.mats) { src[n] = { t: 'u' }; vals[n] = pi.mats[n]; }
    let blocks = [];
    try { blocks = blocksOf(gl, prog, pi); } catch (e) {}
    for (const blk of blocks) {
      let binding;
      try { binding = gl.getActiveUniformBlockParameter(prog, blk.index, 35391); } catch (e) { continue; }
      for (const name in blk.u) src[name] = { t: 'b', binding, o: blk.u[name] };
    }
    const um = uboMats(gl, prog, pi);
    for (const n in um) vals[n] = um[n];
    const roles = findRoles(vals);
    if (!roles) return null;
    let locs = PLOC.get(prog);
    if (!locs) { locs = {}; PLOC.set(prog, locs); }
    const patches = [];
    const add = (role, name, world) => {
      const sc = src[name];
      if (!sc) return false;
      if (sc.t === 'u') {
        if (!locs[name]) locs[name] = N.getUniformLocation.call(gl, prog, name);
        if (!locs[name]) return false;
        if (role === 'wvp' && !(src[world] && src[world].t === 'u')) return false;
        patches.push({ role, t: 'u', name, loc: locs[name], world });
        return true;
      }
      if (role === 'wvp') return false;
      patches.push({ role, t: 'b', name, binding: sc.binding, o: sc.o });
      return true;
    };
    let ok = 0;
    if (roles.vp && add('vp', roles.vp)) ok++;
    if (roles.view) {
      const n0 = patches.length;
      if (add('view', roles.view) && add('proj', roles.proj)) ok++;
      else patches.length = n0;
    }
    if (roles.wvp && add('wvp', roles.wvp, roles.world)) ok++;
    if (!ok) return null;
    const bindings = [];
    for (const p of patches) if (p.t === 'b' && bindings.indexOf(p.binding) < 0) bindings.push(p.binding);
    return { patches, bindings };
  }

  function lightMat(F, role) {
    return role === 'vp' ? F.vp : role === 'view' ? F.view : F.proj;
  }

  function shadowClone(gl, s, bd, list) {
    const data = UBUF.get(bd.buf);
    if (!data) return null;
    const ver = UVER.get(bd.buf) || 0;
    let e = CLONES.get(bd.buf);
    if (!e) { e = { buf: gl.createBuffer(), ver: -1, frame: -1, done: new Set(), cpy: null }; CLONES.set(bd.buf, e); }
    const need = Math.max(data.length, ((bd.off || 0) + (bd.size || 0)) / 4);
    let dirty = false;
    if (e.ver !== ver || e.frame !== s.frameId || !e.cpy || e.cpy.length !== need) {
      e.cpy = new Float32Array(need);
      e.cpy.set(data);
      e.done.clear();
      e.ver = ver;
      e.frame = s.frameId;
      dirty = true;
    }
    for (const p of list) {
      const key = p.role + ':' + p.o;
      if (e.done.has(key)) continue;
      const off = (bd.off || 0) / 4 + p.o;
      if (off + 16 > e.cpy.length) return null;
      e.cpy.set(lightMat(s.lsF, p.role), off);
      e.done.add(key);
      dirty = true;
    }
    if (dirty) {
      N.bindBuffer.call(gl, 36663, e.buf);
      N.bufferData.call(gl, 36663, e.cpy, 35048);
      N.bindBuffer.call(gl, 36663, null);
    }
    return e;
  }

  function bindUbo(gl, b, buf, off, size) {
    if (size !== undefined) N.bindBufferRange.call(gl, UBO_TARGET, b, buf, off || 0, size);
    else N.bindBufferBase.call(gl, UBO_TARGET, b, buf);
  }

  function replayDraw(gl, fn, args) {
    if (gl !== gameGL) return;
    const s = ST.get(gl);
    if (!s || !s.lsOn || !s.replayOK || !s.managed || s.logicalDraw !== null) return;
    const g = s.gs;
    if (!g.caps[2929] || !g.depthMask || g.caps[3042]) return;
    const prog = s.curProg;
    if (!prog) return;
    s.lsElig++;
    const pi = PROGS.get(prog);
    if (!pi) return;
    if (pi.plan === undefined || (pi.plan === null && s.frameId - pi.planFrame > 20)) {
      pi.plan = buildPlan(gl, prog, pi);
      pi.planFrame = s.frameId;
    }
    const plan = pi.plan;
    if (!plan) { s.lsSkip++; return; }
    const isStat = (pi.avg || 0) >= 12;
    const ti = isStat ? s.lsCur : 0;
    const tsz = ti === 0 ? s.lsSizeD : s.lsSizeS;
    const F = s.lsF;
    const ub = UB.get(gl);
    const bds = [];
    let switched = false;
    try {
      for (const b of plan.bindings) {
        const bd = ub && ub.bind[b];
        if (!bd || !bd.buf) { s.lsSkip++; return; }
        const list = plan.patches.filter((p) => p.t === 'b' && p.binding === b);
        const e = shadowClone(gl, s, bd, list);
        if (!e) { s.lsSkip++; return; }
        bds.push({ b, bd, e });
      }
      switched = true;
      N.bindFramebuffer.call(gl, 36160, s.lsFbo[ti]);
      N.viewport.call(gl, 0, 0, tsz, tsz);
      if (g.caps[2884]) N.disable.call(gl, 2884);
      if (g.caps[3089]) N.disable.call(gl, 3089);
      N.depthFunc.call(gl, 515);
      N.enable.call(gl, 32823);
      gl.polygonOffset(1.5, 2);
      for (const p of plan.patches) {
        if (p.t !== 'u') continue;
        const val = p.role === 'wvp' ? mul(F.vp, pi.mats[p.world]) : lightMat(F, p.role);
        N.uniformMatrix4fv.call(gl, p.loc, false, val);
      }
      for (const x of bds) bindUbo(gl, x.b, x.e.buf, x.bd.off, x.bd.size);
      N[fn].apply(gl, args);
      s.lsDone++;
      if (isStat) s.lsStat++; else s.lsDyn++;
    } catch (err) {
      s.lsBroken = true;
      console.error('[Shader Lab] Shadow replay error, falling back to screen-space shadows:', err);
    } finally {
      if (switched) {
        try {
          N.bindFramebuffer.call(gl, 36160, s.actualDraw);
          N.viewport.call(gl, g.vp[0], g.vp[1], g.vp[2], g.vp[3]);
          if (g.caps[2884]) N.enable.call(gl, 2884);
          if (g.caps[3089]) N.enable.call(gl, 3089);
          if (!g.caps[32823]) N.disable.call(gl, 32823);
          N.depthFunc.call(gl, g.depthFunc);
          for (const p of plan.patches) if (p.t === 'u') N.uniformMatrix4fv.call(gl, p.loc, false, pi.mats[p.name]);
          for (const x of bds) bindUbo(gl, x.b, x.bd.buf, x.bd.off, x.bd.size);
          if (bds.length) N.bindBuffer.call(gl, UBO_TARGET, ub.cur);
        } catch (e2) {}
      }
    }
  }

  const CAPS = [2929, 3042, 2884, 3089, 2960];
  const WX = { rain: 0, storm: 0, t: 0 };

  function runPass(gl, s) {
    endSegment(gl, true);
    computeMatrices(gl, s);

    const vao = gl.getParameter(gl.VERTEX_ARRAY_BINDING);
    const at = gl.getParameter(gl.ACTIVE_TEXTURE);
    gl.activeTexture(gl.TEXTURE0); const t0 = gl.getParameter(gl.TEXTURE_BINDING_2D);
    gl.activeTexture(gl.TEXTURE1); const t1 = gl.getParameter(gl.TEXTURE_BINDING_2D);
    gl.activeTexture(gl.TEXTURE2); const t2 = gl.getParameter(gl.TEXTURE_BINDING_2D);
    gl.activeTexture(gl.TEXTURE3); const t3 = gl.getParameter(gl.TEXTURE_BINDING_2D);
    gl.activeTexture(gl.TEXTURE4); const t4 = gl.getParameter(gl.TEXTURE_BINDING_2D);
    gl.activeTexture(gl.TEXTURE5); const t5 = gl.getParameter(gl.TEXTURE_BINDING_2D);
    const vp = gl.getParameter(gl.VIEWPORT); const vx = vp[0], vy = vp[1], vw = vp[2], vh = vp[3];
    const cm = gl.getParameter(gl.COLOR_WRITEMASK);
    const en = CAPS.map((cap) => gl.isEnabled(cap));

    const depthUse = s.snapValid ? s.snapTex : s.depthTex;
    const useSM = !!(s.lsOn && s.lsF && s.lsElig >= 8 && s.lsDone >= s.lsElig * 0.6);
    s.lsUse = useSM;
    if (s.matOk && !useSM && S.shadow > 0.001) {
      N.bindFramebuffer.call(gl, 36160, s.shFbo);
      gl.viewport(0, 0, s.shW, s.shH);
      for (const cap of CAPS) gl.disable(cap);
      gl.colorMask(true, true, true, true);
      N.useProgram.call(gl, s.shProg);
      gl.bindVertexArray(s.vao);
      gl.activeTexture(gl.TEXTURE1); gl.bindTexture(gl.TEXTURE_2D, depthUse);
      const H = s.shU;
      gl.uniform1i(H.uDepth, 1);
      gl.uniform2f(H.uRes, s.w, s.h);
      gl.uniform1f(H.uTime, S.time);
      gl.uniform1f(H.uMatOk, 1);
      N.uniformMatrix4fv.call(gl, H.uVP, false, s.vp);
      N.uniformMatrix4fv.call(gl, H.uInvVP, false, s.ivp);
      gl.uniform3f(H.uCam, s.cam[0], s.cam[1], s.cam[2]);
      N.drawArrays.call(gl, gl.TRIANGLES, 0, 3);
    }

    N.bindFramebuffer.call(gl, 36160, null);
    gl.viewport(0, 0, s.w, s.h);
    for (const cap of CAPS) gl.disable(cap);
    gl.colorMask(true, true, true, true);
    N.useProgram.call(gl, s.prog);
    gl.bindVertexArray(s.vao);
    gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, s.colorTex);
    gl.activeTexture(gl.TEXTURE1); gl.bindTexture(gl.TEXTURE_2D, depthUse);
    gl.activeTexture(gl.TEXTURE2); gl.bindTexture(gl.TEXTURE_2D, s.shTex);
    gl.activeTexture(gl.TEXTURE3); gl.bindTexture(gl.TEXTURE_2D, s.lsTex ? s.lsTex[s.lsCur] : s.depthTex);
    gl.activeTexture(gl.TEXTURE4); gl.bindTexture(gl.TEXTURE_2D, s.lsTex ? s.lsTex[s.lsPrev] : s.depthTex);
    gl.activeTexture(gl.TEXTURE5); gl.bindTexture(gl.TEXTURE_2D, s.lsTex ? s.lsTex[0] : s.depthTex);

    const wnow = performance.now();
    const wdt = Math.min(0.1, (wnow - (WX.t || wnow)) / 1000);
    WX.t = wnow;
    const wp = S.wxPower;
    const trg = S.weather === 'rain' ? wp : 0;
    const tst = trg;
    const wk = 1 - Math.exp(-wdt * 0.8);
    WX.rain += (trg - WX.rain) * wk;
    WX.storm += (tst - WX.storm) * wk;

    const U = s.U;
    gl.uniform1i(U.uColor, 0);
    gl.uniform1i(U.uDepth, 1);
    gl.uniform1i(U.uShadow, 2);
    gl.uniform1i(U.uLsDepth, 3);
    gl.uniform1i(U.uLsDepthP, 4);
    gl.uniform1i(U.uLsDepthD, 5);
    gl.uniform2f(U.uRes, s.w, s.h);
    gl.uniform1f(U.uTime, S.time);
    gl.uniform1f(U.uRays, S.rays);
    gl.uniform1f(U.uAnim, performance.now() / 1000);
    gl.uniform1f(U.uDbg, dbgMode);
    gl.uniform1f(U.uWater, S.water);
    gl.uniform1f(U.uRain, WX.rain);
    gl.uniform1f(U.uStorm, WX.storm);
    gl.uniform1f(U.uMatOk, s.matOk ? 1 : 0);
    gl.uniform1f(U.uShadowK, S.shadow);
    gl.uniform1f(U.uLsOn, useSM ? 1 : 0);
    if (useSM) {
      N.uniformMatrix4fv.call(gl, U.uLsVP, false, s.lsF.vp);
      gl.uniform3f(U.uLsInfo, s.lsF.texel, s.lsF.range, 0);
    }
    if (s.matOk) {
      N.uniformMatrix4fv.call(gl, U.uVP, false, s.vp);
      N.uniformMatrix4fv.call(gl, U.uInvVP, false, s.ivp);
      gl.uniform3f(U.uCam, s.cam[0], s.cam[1], s.cam[2]);
    } else {
      const id = new Float32Array([1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);
      N.uniformMatrix4fv.call(gl, U.uVP, false, id);
      N.uniformMatrix4fv.call(gl, U.uInvVP, false, id);
      gl.uniform3f(U.uCam, 0, 0, 0);
    }
    N.drawArrays.call(gl, gl.TRIANGLES, 0, 3);

    N.bindFramebuffer.call(gl, 36160, s.actualDraw);
    gl.activeTexture(gl.TEXTURE5); gl.bindTexture(gl.TEXTURE_2D, t5);
    gl.activeTexture(gl.TEXTURE4); gl.bindTexture(gl.TEXTURE_2D, t4);
    gl.activeTexture(gl.TEXTURE3); gl.bindTexture(gl.TEXTURE_2D, t3);
    gl.activeTexture(gl.TEXTURE2); gl.bindTexture(gl.TEXTURE_2D, t2);
    gl.activeTexture(gl.TEXTURE1); gl.bindTexture(gl.TEXTURE_2D, t1);
    gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, t0);
    gl.activeTexture(at);
    gl.bindVertexArray(vao);
    N.useProgram.call(gl, s.curProg);
    gl.viewport(vx, vy, vw, vh);
    gl.colorMask(cm[0], cm[1], cm[2], cm[3]);
    CAPS.forEach((cap, i) => { if (en[i]) gl.enable(cap); else gl.disable(cap); });
  }

  function post(gl) {
    const s = ST.get(gl);
    if (!s) return;
    s.frameStarted = false;
    if (!s.managed || !s.drew || s.failed) { s.drew = false; return; }
    s.drew = false;
    s.postCount++;
    if (!bootMarked && s.postCount >= 60) { bootMarked = true; try { localStorage.setItem(BOOT, '0'); } catch (e) {} }
    try { runPass(gl, s); } catch (e) { failRuntime(gl, s, e); }
  }

  const raf = window.requestAnimationFrame.bind(window);
  window.requestAnimationFrame = function (cb) {
    return raf(function (t) {
      try { cb(t); } finally { try { if (gameGL) post(gameGL); } catch (e) {} }
    });
  };

  setInterval(() => {
    if (!gameGL) return;
    const s = ST.get(gameGL);
    if (!s || !s.managed) return;
    if (s.drew && s.postCount === s.lastCheckPost) failRuntime(gameGL, s, new Error('Post-process pass is not running (rAF)'));
    s.lastCheckPost = s.postCount;
  }, 1500);

  let panel = null;
  const ui = {};
  const fmtTime = (v) => {
    const h = Math.floor(v) % 24, m = Math.floor((v - Math.floor(v)) * 60);
    return String(h).padStart(2, '0') + ':' + String(m).padStart(2, '0');
  };

  function syncUi() {
    if (!panel) return;
    ui.btn.classList.toggle('on', S.enabled);
    ui.time.value = S.time; ui.timeVal.textContent = fmtTime(S.time);
    ui.rays.value = S.rays; ui.raysVal.textContent = Number(S.rays).toFixed(2);
    ui.shadow.value = S.shadow; ui.shadowVal.textContent = Number(S.shadow).toFixed(2);
    ui.water.value = S.water; ui.waterVal.textContent = Number(S.water).toFixed(2);
    ui.wxp.value = S.wxPower; ui.wxpVal.textContent = Number(S.wxPower).toFixed(2);
    ui.wxBtns.forEach((b) => b.classList.toggle('on', b.getAttribute('data-w') === S.weather));
    const s = gameGL && ST.get(gameGL);
    const ok = !!s && !s.failed && statusText !== 'error' && (s.postCount > 0 || !S.enabled);
    ui.dot.style.background = ok ? '#2ecc71' : '#e02f2f';
  }

  const smooth = (a, b, x) => { const t = Math.min(1, Math.max(0, (x - a) / (b - a))); return t * t * (3 - 2 * t); };
  const mixc = (a, b, k) => [a[0] + (b[0] - a[0]) * k, a[1] + (b[1] - a[1]) * k, a[2] + (b[2] - a[2]) * k];
  const rgb = (c, a) => 'rgba(' + Math.round(c[0]) + ',' + Math.round(c[1]) + ',' + Math.round(c[2]) + ',' + (a === undefined ? 1 : a) + ')';
  const PSTARS = (() => {
    let x = 12345;
    const r = () => { x = (x * 1664525 + 1013904223) >>> 0; return x / 4294967296; };
    return Array.from({ length: 48 }, () => ({ x: r(), y: r() * 0.8, s: 0.6 + r() * 1.1, p: r() * 6.28 }));
  })();
  const PCLOUDS = [
    { x: 0.05, y: 0.62, s: 1.0, v: 7 }, { x: 0.38, y: 0.32, s: 0.7, v: 5 }, { x: 0.62, y: 0.70, s: 1.25, v: 9 },
    { x: 0.85, y: 0.42, s: 0.85, v: 6 }, { x: 0.22, y: 0.85, s: 0.9, v: 8 },
  ];

  function drawPanel(t) {
    const cv = ui.cv, g = ui.cx;
    const W = panel.clientWidth, H = panel.clientHeight;
    if (!g || !W || !H) return;
    const dpr = Math.min(2, window.devicePixelRatio || 1);
    if (cv.width !== Math.round(W * dpr) || cv.height !== Math.round(H * dpr)) {
      cv.width = Math.round(W * dpr);
      cv.height = Math.round(H * dpr);
    }
    g.setTransform(dpr, 0, 0, dpr, 0, 0);
    const nt = (((S.time - 6) % 24) + 24) % 24;
    const isDay = nt < 12;
    const a = (isDay ? nt : nt - 12) / 12 * Math.PI;
    const e = isDay ? Math.sin(a) : -Math.sin(a);
    const dayW = smooth(0.02, 0.4, e);
    const duskW = smooth(-0.28, 0, e);
    const top = mixc(mixc([2, 3, 10], [41, 51, 107], duskW), [56, 117, 235], dayW);
    const bot = mixc(mixc([9, 14, 33], [255, 122, 56], duskW), [189, 219, 255], dayW);
    const grad = g.createLinearGradient(0, 0, 0, H);
    grad.addColorStop(0, rgb(top));
    grad.addColorStop(1, rgb(bot));
    g.fillStyle = grad;
    g.fillRect(0, 0, W, H);

    const starA = smooth(0.05, 0.35, -e);
    if (starA > 0.01) {
      for (const st of PSTARS) {
        const tw = 0.65 + 0.35 * Math.sin(t / 700 + st.p);
        g.fillStyle = 'rgba(255,255,255,' + (starA * tw).toFixed(3) + ')';
        g.beginPath();
        g.arc(st.x * W, st.y * H, st.s, 0, 6.2832);
        g.fill();
      }
    }

    const bx = W * (0.5 - Math.cos(a) * 0.4);
    const by = H * (0.9 - 0.72 * Math.sin(a));
    if (isDay) {
      const al = Math.min(1, 0.25 + e * 3);
      const rg = g.createRadialGradient(bx, by, 2, bx, by, 40);
      rg.addColorStop(0, 'rgba(255,235,170,' + (0.6 * al).toFixed(3) + ')');
      rg.addColorStop(1, 'rgba(255,235,170,0)');
      g.fillStyle = rg;
      g.fillRect(bx - 40, by - 40, 80, 80);
      g.fillStyle = 'rgba(255,246,205,' + al.toFixed(3) + ')';
      g.beginPath();
      g.arc(bx, by, 11, 0, 6.2832);
      g.fill();
      g.strokeStyle = 'rgba(255,170,90,' + (0.75 * al).toFixed(3) + ')';
      g.lineWidth = 2.2;
      g.beginPath();
      g.arc(bx, by, 12.2, 0, 6.2832);
      g.stroke();
    } else {
      const al = Math.min(1, 0.3 - e * 3);
      const R = 11;
      const rg = g.createRadialGradient(bx, by, 2, bx, by, 34);
      rg.addColorStop(0, 'rgba(170,190,255,' + (0.25 * al).toFixed(3) + ')');
      rg.addColorStop(1, 'rgba(170,190,255,0)');
      g.fillStyle = rg;
      g.fillRect(bx - 34, by - 34, 68, 68);
      g.save();
      g.beginPath();
      g.rect(0, 0, W, H);
      g.moveTo(bx + R * 0.5 + R * 0.88, by - R * 0.2);
      g.arc(bx + R * 0.5, by - R * 0.2, R * 0.88, 0, 6.2832);
      g.clip('evenodd');
      g.beginPath();
      g.arc(bx, by, R, 0, 6.2832);
      g.fillStyle = 'rgba(242,246,255,' + al.toFixed(3) + ')';
      g.fill();
      g.restore();
    }

    const cc = mixc(mixc([45, 52, 85], [255, 170, 140], duskW), [255, 255, 255], dayW);
    const ca = 0.2 + 0.7 * duskW;
    g.fillStyle = rgb(cc, ca.toFixed(3));
    const span = W + 120;
    for (const c of PCLOUDS) {
      const x = (((c.x * W + t / 1000 * c.v) % span) + span) % span - 60;
      const y = c.y * H;
      g.beginPath();
      for (const q of [[0, 0, 14], [15, -6, 17], [31, 0, 13], [16, 5, 14]]) {
        g.moveTo(x + (q[0] + q[2]) * c.s, y + q[1] * c.s);
        g.arc(x + q[0] * c.s, y + q[1] * c.s, q[2] * c.s, 0, 6.2832);
      }
      g.fill();
    }

    g.fillStyle = 'rgba(0,0,0,' + (0.12 + 0.1 * dayW).toFixed(3) + ')';
    g.fillRect(0, 0, W, H);
  }

  function panelLoop(t) {
    if (!panel || panel.style.display !== 'block') { ui.anim = false; return; }
    drawPanel(t);
    raf(panelLoop);
  }

  function startPanelLoop() {
    if (ui.anim) return;
    ui.anim = true;
    raf(panelLoop);
  }

  function buildUi() {
    if (panel || !document.body) return;
    const style = document.createElement('style');
    style.textContent = `
      #bsl-panel{position:fixed;top:90px;right:14px;width:260px;z-index:2147483647;
        background:#14161e;color:#eee;font:13px/1.35 system-ui,sans-serif;
        border:1px solid rgba(255,255,255,.15);border-radius:10px;padding:10px 12px;
        box-shadow:0 6px 24px rgba(0,0,0,.5);display:none;user-select:none;overflow:hidden;text-shadow:0 1px 3px rgba(0,0,0,.7)}
      #bsl-panel .top{display:flex;justify-content:space-between;align-items:center;margin-bottom:8px}
      #bsl-panel .top b{font-size:14px}
      #bsl-panel button{color:#fff;border:0;border-radius:6px;padding:5px 10px;cursor:pointer;font-weight:600}
      #bsl-panel .row{margin:9px 0}
      #bsl-panel .lab{display:flex;justify-content:space-between;margin-bottom:3px}
      #bsl-panel input[type=range]{width:100%;margin:0}
      #bsl-panel .sw{position:relative;width:44px;height:24px;padding:0;background:#7d2e2e;border-radius:12px;transition:background .15s}
      #bsl-panel .sw.on{background:#2e7d4f}
      #bsl-panel .sw::after{content:'';position:absolute;top:3px;left:3px;width:18px;height:18px;border-radius:50%;background:#fff;transition:transform .15s}
      #bsl-panel .sw.on::after{transform:translateX(20px)}
      #bsl-panel .wx{display:flex;gap:4px}
      #bsl-panel .wx button{flex:1;padding:4px 0;font-size:12px;background:rgba(255,255,255,.14)}
      #bsl-panel .wx button.on{background:rgba(255,255,255,.42)}
      #bsl-bg{position:absolute;left:0;top:0;width:100%;height:100%;pointer-events:none;z-index:0}
      #bsl-panel .top,#bsl-panel .row{position:relative;z-index:1}
      #bsl-panel .top b i{display:inline-block;width:9px;height:9px;margin-left:7px;border-radius:50%;background:#e02f2f;border:1px solid rgba(255,255,255,.6);vertical-align:middle}
    `;
    document.head.appendChild(style);
    panel = document.createElement('div');
    panel.id = 'bsl-panel';
    const stop = (e) => e.stopPropagation();
    ['keydown', 'keyup', 'keypress', 'wheel'].forEach((ev) => panel.addEventListener(ev, stop));
    panel.innerHTML =
      '<canvas id="bsl-bg"></canvas>' +
      '<div class="top"><b>Shader:)<i id="bsl-dot"></i></b><button id="bsl-btn" class="sw"></button></div>' +
      '<div class="row"><div class="lab"><span>Time</span><span id="bsl-tv"></span></div>' +
      '<input type="range" id="bsl-time" min="0" max="24" step="0.05"></div>' +
      '<div class="row"><div class="lab"><span>Sun light</span><span id="bsl-rv"></span></div>' +
      '<input type="range" id="bsl-rays" min="0" max="1.5" step="0.01"></div>' +
      '<div class="row"><div class="lab"><span>Shadow</span><span id="bsl-sv"></span></div>' +
      '<input type="range" id="bsl-shadow" min="0" max="1" step="0.01"></div>' +
      '<div class="row"><div class="lab"><span>Better Water</span><span id="bsl-wv"></span></div>' +
      '<input type="range" id="bsl-water" min="0" max="1" step="0.01"></div>' +
      '<div class="row"><div class="lab"><span>Weather</span><span id="bsl-wpv"></span></div>' +
      '<div class="wx"><button data-w="clear">Clear</button><button data-w="rain">Rain</button></div>' +
      '<input type="range" id="bsl-wxp" min="0.1" max="1" step="0.01" style="margin-top:6px"></div>';
    document.body.appendChild(panel);
    ui.btn = panel.querySelector('#bsl-btn');
    ui.time = panel.querySelector('#bsl-time'); ui.timeVal = panel.querySelector('#bsl-tv');
    ui.rays = panel.querySelector('#bsl-rays'); ui.raysVal = panel.querySelector('#bsl-rv');
    ui.shadow = panel.querySelector('#bsl-shadow'); ui.shadowVal = panel.querySelector('#bsl-sv');
    ui.dot = panel.querySelector('#bsl-dot');
    ui.water = panel.querySelector('#bsl-water'); ui.waterVal = panel.querySelector('#bsl-wv');
    ui.wxp = panel.querySelector('#bsl-wxp'); ui.wxpVal = panel.querySelector('#bsl-wpv');
    ui.wxBtns = panel.querySelectorAll('.wx button');
    ui.wxBtns.forEach((b) => b.addEventListener('click', () => { S.weather = b.getAttribute('data-w'); save(); syncUi(); }));
    ui.wxp.addEventListener('input', () => { S.wxPower = parseFloat(ui.wxp.value); ui.wxpVal.textContent = S.wxPower.toFixed(2); save(); });
    ui.cv = panel.querySelector('#bsl-bg');
    ui.cx = ui.cv.getContext('2d');
    ui.btn.addEventListener('click', () => { S.enabled = !S.enabled; save(); syncUi(); });
    ui.time.addEventListener('input', () => { S.time = parseFloat(ui.time.value); ui.timeVal.textContent = fmtTime(S.time); save(); });
    ui.water.addEventListener('input', () => { S.water = parseFloat(ui.water.value); ui.waterVal.textContent = S.water.toFixed(2); save(); });
    ui.shadow.addEventListener('input', () => { S.shadow = parseFloat(ui.shadow.value); ui.shadowVal.textContent = S.shadow.toFixed(2); save(); });
    ui.rays.addEventListener('input', () => { S.rays = parseFloat(ui.rays.value); ui.raysVal.textContent = S.rays.toFixed(2); save(); });
    syncUi();
    setInterval(() => { if (panel.style.display === 'block') syncUi(); }, 500);
  }

  function isTyping(e) {
    const t = e.target;
    return t && (t.tagName === 'INPUT' || t.tagName === 'TEXTAREA' || t.isContentEditable);
  }

  window.addEventListener('keydown', (e) => {
    if (e.code !== 'ShiftRight' || e.repeat || isTyping(e)) return;
    buildUi();
    if (!panel) return;
    const open = panel.style.display !== 'block';
    panel.style.display = open ? 'block' : 'none';
    if (open) { syncUi(); startPanelLoop(); try { document.exitPointerLock(); } catch (err) {} }
  }, true);

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', buildUi);
  else buildUi();

  window.__bloxdShaderLab = {
    settings: S,
    debug(n) { dbgMode = Number(n) || 0; return dbgMode; },
    dumpShaders() { console.log(shaderLog.join('\n\n----------------\n\n')); return shaderLog.length; },
    dumpUniforms() {
      const rows = [...PROGS.values()].sort((a, b) => b.total - a.total).slice(0, 12)
        .map((pi) => ({
          totalDraws: pi.total,
          matrices: Object.keys(pi.mats),
          blocks: pi.blocks ? pi.blocks.map((b) => Object.keys(b.u)) : null,
        }));
      console.log(JSON.stringify(rows, null, 2));
      return rows;
    },
    dumpMats() {
      if (!gameGL) return null;
      const rows = [...PROGS.entries()].sort((a, b) => b[1].total - a[1].total).slice(0, 8).map(([prog, pi]) => {
        const m = Object.assign({}, pi.mats, uboMats(gameGL, prog, pi));
        return { draws: pi.total, mats: Object.keys(m).map((k) => k + (isPersp(m[k]) ? ':P' : '') + (isRigid(m[k]) ? ':V' : '')) };
      });
      console.log(JSON.stringify(rows, null, 2));
      return rows;
    },
    dumpPlans() {
      const rows = [...PROGS.values()].sort((a, b) => b.total - a.total).slice(0, 10).map((pi) => ({
        draws: pi.total,
        plan: pi.plan === undefined ? 'notTried' : pi.plan === null ? 'unsupported' : pi.plan.patches.map((p) => p.role + ':' + p.t + ':' + p.name),
      }));
      console.log(JSON.stringify(rows, null, 2));
      return rows;
    },
    info() {
      const s = gameGL && ST.get(gameGL);
      return s ? { managed: s.managed, matrixOk: s.matOk, matrixSource: s.how || null, failed: s.failed, size: [s.w, s.h], enabled: S.enabled, boots: bootCount, uboWrites: stats.ubo, programs: PROGS.size, snap: s.snapValid, snapDraws: s.bestDraws, depthClears: s.lastClears, shadowMap: { active: s.lsUse, eligible: s.lsElig, replayed: s.lsDone, static: s.lsStat, dynamic: s.lsDyn, skipped: s.lsSkip, error: s.lsBroken, shifts: s.lsShifts, resets: s.lsResets, dirtyClears: s.lsDirtyClears } } : null;
    },
  };
})();
