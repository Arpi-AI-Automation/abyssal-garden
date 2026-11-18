// ============================================================================
// gameplay: sharks, air, coins, golden fish, third-grade math
// ============================================================================
// Questions stay at one level for the whole run: times tables through 12×12,
// two-digit addition, and two-digit subtraction that never goes negative.
// A miss or a timeout costs a life. Correct answers score points, with a
// combo for a streak. Sharks, air and the clock all freeze while a question is up.
// Per-frame numbers live in typed arrays. Strings are built only when a
// question opens or the HUD text actually changes.

const NS = 5, STR = 24, NCOIN = 28, NFISH = 8, SCALE = 7.2, SNOUT = 0.52 * SCALE;
const SH = new Float64Array(NS * STR);
const sharkInst = new Float32Array(NS * 8);
const coinInst = new Float32Array(NCOIN * 8);
const goldInst = new Float32Array(NFISH * 8);
const coins = new Float32Array(NCOIN * 4); // x, y, z, alive
const fishS = new Float64Array(NFISH * 8); // x y z yaw spd phase alive flee

// run state
const R = new Float64Array(20);
const SURV = 0, BEST = 1, SCORE = 2, HIGH = 3, AIR = 4, STAM = 5, LIVES = 6, INV = 7;
const COMBO = 8, COINS = 9, FISHN = 10, RUN = 11, OVER = 12, PAUSE = 13, QT = 14, QPTS = 15, NSH = 16, SPRINT = 17;
const AIRMAX = 75, AIRLOW = 20, SIGHT = 32, LOCKNEED = 2.3, GIVEUP = 3.2, DROPD = 40;
const QSEC = 20, COIN_R2 = 1.35, FISH_R2 = 3.2;

let danger = 0, vignette = 0, airWarn = 0;
let kelpMap, shipP, shipQ, kelpHide = 255, kelpBlock = 255;
let wr = 0xC0FFEE;
const wrand = () => { wr = (Math.imul(wr, 1664525) + 1013904223) | 0; return (wr >>> 0) / 4294967296; };
let QX = 0, QY = 0, QZ = 0, SLX = 0, SLY = 0, SLZ = 0;
let qText = '', qAns = 0, qShow = 0, qDead = 0;
let hudAcc = 0, shownScore = -1, shownCombo = -1, shownLives = -1, hudTime = -1;

function el(id) { return typeof document === 'undefined' ? null : document.getElementById(id); }
function qApply(qx, qy, qz, qw, x, y, z) {
  const cx = qy * z - qz * y + qw * x, cy = qz * x - qx * z + qw * y, cz = qx * y - qy * x + qw * z;
  QX = x + 2 * (qy * cz - qz * cy); QY = y + 2 * (qz * cx - qx * cz); QZ = z + 2 * (qx * cy - qy * cx);
}
function toShip(x, y, z) {
  qApply(-shipQ[0], -shipQ[1], -shipQ[2], shipQ[3], x - shipP[0], y - shipP[1], z - shipP[2]);
  SLX = QX; SLY = QY; SLZ = QZ;
}
function kelpAt(x, z) {
  let i = (x - OX) / KGC | 0, j = (z - OZ) / KGC | 0;
  if (i < 0) i = 0; else if (i >= KGW) i = KGW - 1;
  if (j < 0) j = 0; else if (j >= KGW) j = KGW - 1;
  return kelpMap[i + j * KGW];
}
function tuneKelp() {
  const hist = new Uint32Array(256);
  let nz = 0;
  for (let i = 0; i < kelpMap.length; i++) { const v = kelpMap[i]; hist[v]++; if (v) nz++; }
  if (nz < 8) return;
  let acc = 0, p70 = 0, p90 = 0;
  for (let i = 1; i < 256; i++) {
    acc += hist[i];
    if (!p70 && acc >= nz * 0.7) p70 = i;
    if (acc >= nz * 0.9) { p90 = i; break; }
  }
  kelpBlock = p70 || 255;
  kelpHide = p90 > p70 ? p90 : (p70 ? p70 + 1 : 255);
}
function rockAt(x, y, z) {
  const X = (x - OX) / VS - CO, Y = (y - OY) / VS, Z = (z - OZ) / VS - CO;
  if (X < 1 || Y < 1 || Z < 1 || X >= CN * 4 - 2 || Y >= NY - 2 || Z >= CN * 4 - 2) return 1;
  const ix = X | 0, iy = Y | 0, iz = Z | 0, u = X - ix, v = Y - iy, w = Z - iz;
  const s = (px, py, pz) => {
    const b = CI[(px >> 2) + CN * ((py >> 2) + NY / 4 * (pz >> 2))];
    return b > 1 ? CG[b * 64 - 128 + (px & 3) + 4 * (py & 3) + 16 * (pz & 3)] : b * 254 - 127;
  };
  const a = s(ix, iy, iz), b = s(ix, iy + 1, iz), c = s(ix, iy, iz + 1), d = s(ix, iy + 1, iz + 1);
  const e = s(ix + 1, iy, iz), f = s(ix + 1, iy + 1, iz), g = s(ix + 1, iy, iz + 1), h = s(ix + 1, iy + 1, iz + 1);
  const p = a + (e - a) * u, q = b + (f - b) * u, r = c + (g - c) * u, t = d + (h - d) * u;
  return (p + (q - p) * v + (r + (t - r) * v - (p + (q - p) * v)) * w) / 127;
}
function cruiseY(x, z, prefer) {
  let best = prefer, score = 1e9;
  for (let y = -8; y >= -44; y -= 2) {
    const d = rockAt(x, y, z);
    if (d > -0.45) continue;
    const sc = abs(y - prefer) + (d > -0.9 ? 6 : 0);
    if (sc < score) { score = sc; best = y; }
  }
  return best;
}
function wrapAng(a) {
  a = (a + PI) / TAU; a -= floor(a); if (a < 0) a += 1;
  return a * TAU - PI;
}
function inShipBox() { return abs(SLX) < 17.5 && abs(SLY) < 8.2 && abs(SLZ) < 6.4; }
function pushOut(o) {
  for (let k = 0; k < 2; k++) {
    const d = rockAt(SH[o], SH[o + 1], SH[o + 2]);
    if (d < -0.55) return;
    const e = 0.8;
    let gx = rockAt(SH[o] + e, SH[o + 1], SH[o + 2]) - rockAt(SH[o] - e, SH[o + 1], SH[o + 2]);
    let gy = rockAt(SH[o], SH[o + 1] + e, SH[o + 2]) - rockAt(SH[o], SH[o + 1] - e, SH[o + 2]);
    let gz = rockAt(SH[o], SH[o + 1], SH[o + 2] + e) - rockAt(SH[o], SH[o + 1], SH[o + 2] - e);
    const l = hypot(gx, gy, gz) || 1, p = d + 0.7;
    SH[o] -= gx / l * p; SH[o + 1] -= gy / l * p; SH[o + 2] -= gz / l * p;
  }
}
function pushShip(o) {
  toShip(SH[o], SH[o + 1], SH[o + 2]);
  if (!inShipBox()) return;
  const px = 17.5 - abs(SLX), py = 8.2 - abs(SLY), pz = 6.4 - abs(SLZ);
  let lx = 0, ly = 0, lz = 0;
  if (px <= py && px <= pz) lx = (SLX < 0 ? -1 : 1) * (px + 0.4);
  else if (py <= pz) ly = (SLY < 0 ? -1 : 1) * (py + 0.4);
  else lz = (SLZ < 0 ? -1 : 1) * (pz + 0.4);
  qApply(shipQ[0], shipQ[1], shipQ[2], shipQ[3], lx, ly, lz);
  SH[o] += QX; SH[o + 1] += QY; SH[o + 2] += QZ;
}
function aheadBlocked(o, yaw, pit, dist) {
  const cp = cos(pit);
  const x = SH[o] + cp * sin(yaw) * dist, y = SH[o + 1] + sin(pit) * dist, z = SH[o + 2] - cp * cos(yaw) * dist;
  if (rockAt(x, y, z) > -0.35) return 1;
  toShip(x, y, z);
  return inShipBox() ? 1 : 0;
}
function steer(o, tx, ty, tz, spd, turn, dt) {
  let dx = tx - SH[o], dy = ty - SH[o + 1], dz = tz - SH[o + 2];
  const yaw = SH[o + 3], pit = SH[o + 4];
  if (aheadBlocked(o, yaw, pit, 8)) {
    const left = aheadBlocked(o, yaw + 1, pit, 8), right = aheadBlocked(o, yaw - 1, pit, 8);
    const side = left <= right ? 1.15 : -1.15;
    if (left && right && !aheadBlocked(o, yaw, pit + 0.4, 7)) dy += 12;
    dx = sin(yaw + side) * 12; dz = -cos(yaw + side) * 12;
  }
  const ye = wrapAng(atan2(dx, -dz) - yaw), step = turn * dt;
  const dyaw = ye > step ? step : ye < -step ? -step : ye;
  SH[o + 3] = yaw + dyaw;
  let wantPit = atan2(dy, hypot(dx, dz) || 1);
  if (wantPit > 0.42) wantPit = 0.42; else if (wantPit < -0.5) wantPit = -0.5;
  const dp = wantPit - pit, ps = 0.55 * dt;
  SH[o + 4] = pit + (dp > ps ? ps : dp < -ps ? -ps : dp);
  const yv = dt > 1e-4 ? dyaw / dt : 0;
  const wantRol = yv < -2.2 ? -0.5 : yv > 2.2 ? 0.5 : -yv * 0.2;
  SH[o + 5] += (wantRol - SH[o + 5]) * (1 - exp(-dt * 2.6));
  SH[o + 6] += (spd - SH[o + 6]) * (1 - exp(-dt * 2));
  const cy = SH[o + 3], cpit = SH[o + 4], ccp = cos(cpit);
  SH[o] += ccp * sin(cy) * SH[o + 6] * dt;
  SH[o + 1] += sin(cpit) * SH[o + 6] * dt;
  SH[o + 2] -= ccp * cos(cy) * SH[o + 6] * dt;
  const rad = hypot(SH[o], SH[o + 2]);
  if (rad > 130) { const s = 130 / rad; SH[o] *= s; SH[o + 2] *= s; }
  if (SH[o + 1] > -4.2) SH[o + 1] = -4.2; else if (SH[o + 1] < -46) SH[o + 1] = -46;
  pushOut(o); pushShip(o);
}
function placeShark(i, x, y, z, yaw) {
  const o = i * STR;
  SH[o] = x; SH[o + 2] = z; SH[o + 1] = cruiseY(x, z, y); SH[o + 3] = yaw; SH[o + 4] = 0; SH[o + 5] = 0;
  SH[o + 6] = 4.4; SH[o + 7] = wrand() * TAU; SH[o + 8] = 1.1;
  SH[o + 9] = 0; SH[o + 10] = 0; SH[o + 11] = 0; SH[o + 22] = 1;
  const a = wrand() * TAU, r = 14;
  SH[o + 12] = x + cos(a) * r; SH[o + 14] = z + sin(a) * r; SH[o + 13] = SH[o + 1];
  for (let k = 0; k < 3; k++) { pushOut(o); pushShip(o); }
}
function ringSharks(cx, cy, cz, n) {
  for (let i = 0; i < NS; i++) {
    const o = i * STR;
    if (i >= n) { SH[o + 22] = 0; SH[o + 1] = -180; continue; }
    const a = TAU * (i / n) + 0.7;
    const rad = 30 + (i % 2) * 8;
    placeShark(i, cx + cos(a) * rad, cy, cz + sin(a) * rad, a + PI * 0.5);
  }
  R[NSH] = n;
}
function concealed() {
  toShip(F[CX], F[CY], F[CZ]);
  if (shipSection(SLX, SLY, SLZ, false)) return 2;
  return kelpAt(F[CX], F[CZ]) >= kelpHide ? 1 : 0;
}
function canSee(o) {
  const dx = F[CX] - SH[o], dy = F[CY] - SH[o + 1], dz = F[CZ] - SH[o + 2];
  if (dx * dx + dy * dy + dz * dz > SIGHT * SIGHT) return 0;
  if (concealed()) return 0;
  const dist = hypot(dx, dy, dz);
  let steps = dist * 0.45 | 0;
  if (steps < 2) steps = 2; else if (steps > 18) steps = 18;
  for (let i = 1; i < steps; i++) {
    const t = i / steps, x = SH[o] + dx * t, y = SH[o + 1] + dy * t, z = SH[o + 2] + dz * t;
    if (kelpAt(x, z) >= kelpBlock) return 0;
    toShip(x, y, z);
    if (shipSection(SLX, SLY, SLZ, true)) return 0;
  }
  return 1;
}
// the shark is in the swimmer's forward view and swimming toward them
function inFront(o) {
  const dx = SH[o] - F[CX], dy = SH[o + 1] - F[CY], dz = SH[o + 2] - F[CZ];
  const d = hypot(dx, dy, dz) || 1;
  if ((dx * F[FX] + dy * F[FY] + dz * F[FZ]) / d < 0.5) return 0;
  const cp = cos(SH[o + 4]), yw = SH[o + 3];
  const fx = cp * sin(yw), fy = sin(SH[o + 4]), fz = -cp * cos(yw);
  return (-dx * fx + -dy * fy + -dz * fz) / d > 0.2 ? 1 : 0;
}
function reached(o) {
  if (SH[o + 9] !== 1 || SH[o + 11] < LOCKNEED) return 0;
  if (concealed() === 2) return 0;
  if (!inFront(o)) return 0;
  const cp = cos(SH[o + 4]), yw = SH[o + 3];
  const mx = SH[o] + cp * sin(yw) * SNOUT, my = SH[o + 1] + sin(SH[o + 4]) * SNOUT, mz = SH[o + 2] - cp * cos(yw) * SNOUT;
  if (hypot(F[CX] - mx, F[CY] - my, F[CZ] - mz) < 1.7) return 1;
  return hypot(F[CX] - SH[o], F[CY] - SH[o + 1], F[CZ] - SH[o + 2]) < 1.35;
}
function chaseSpd() {
  const t = R[SURV];
  return 10.2 + (t > 80 ? 1.1 : 0) + (t > 160 ? 1.1 : 0) + (t > 240 ? 0.8 : 0);
}
function sharkCount() { return R[SURV] > 220 ? 5 : R[SURV] > 140 ? 4 : R[SURV] > 65 ? 3 : 2; }
function saveScores() {
  try {
    if (R[BEST] > 0) localStorage.abyssalBest = R[BEST];
    if (R[HIGH] > 0) localStorage.abyssalScore = R[HIGH];
  } catch { /* private mode */ }
}
// kind: 0 air, 1 shark, 2 a missed math question. Returns 1 when the run ends.
function loseLife(kind) {
  if (R[OVER] || !R[RUN]) return R[OVER] ? 1 : 0;
  if (kind !== 2 && R[INV] > 0) return 0;
  R[LIVES] -= 1;
  vignette = 0.8;
  R[INV] = 3.2;
  if (kind === 0) R[AIR] = 30;
  for (let i = 0; i < NS; i++) {
    const o = i * STR;
    if (!SH[o + 22]) continue;
    SH[o + 9] = 0; SH[o + 11] = 0; SH[o + 10] = 0;
    const dx = SH[o] - F[CX], dz = SH[o + 2] - F[CZ], d = hypot(dx, dz) || 1;
    if (d < 20) { SH[o] += dx / d * 12; SH[o + 2] += dz / d * 12; }
  }
  if (R[LIVES] <= 0) {
    R[LIVES] = 0; R[OVER] = 1;
    if (R[SURV] > R[BEST]) R[BEST] = R[SURV];
    if (R[SCORE] > R[HIGH]) R[HIGH] = R[SCORE];
    saveScores();
    return 1;
  }
  return 0;
}
function freshRun() {
  R[RUN] = 1; R[SURV] = 0; R[SCORE] = 0; R[COINS] = 0; R[FISHN] = 0; R[COMBO] = 0;
  R[AIR] = AIRMAX; R[STAM] = 1; R[LIVES] = 3; R[INV] = 1.6; R[PAUSE] = 0; R[OVER] = 0; R[SPRINT] = 0;
  danger = 0; vignette = 0; airWarn = 0; qShow = 0; qDead = 0; shownScore = -1; shownCombo = -1; shownLives = -1; hudTime = -1;
  for (let i = 0; i < NCOIN; i++) coins[i * 4 + 3] = 1;
  for (let i = 0; i < NFISH; i++) fishS[i * 8 + 6] = 1;
  ringSharks(F[CX], F[CY], F[CZ], 2);
  const q = el('quiz'); if (q) q.style.display = 'none';
  if (typeof document !== 'undefined') document.body.classList.remove('q');
  gameSync();
}
function scatter() {
  let n = 0;
  for (let j = 0; j < KGW && n < 14; j += 2) for (let i = 0; i < KGW && n < 14; i += 2) {
    if (kelpAt(OX + i * KGC, OZ + j * KGC) < kelpHide * 0.92) continue;
    if (wrand() > 0.4) continue;
    const x = OX + (i + 0.5) * KGC, z = OZ + (j + 0.5) * KGC;
    if (hypot(x - 10, z - 7) < 12 || hypot(x, z) > 115) continue;
    const y = cruiseY(x, z, -24);
    coins[n * 4] = x; coins[n * 4 + 1] = y + 1.4; coins[n * 4 + 2] = z; coins[n * 4 + 3] = 1; n++;
  }
  while (n < 20) {
    const a = wrand() * TAU, r = 6 + wrand() * 16;
    const x = shipP[0] + cos(a) * r, z = shipP[2] + sin(a) * r, y = cruiseY(x, z, -22);
    coins[n * 4] = x; coins[n * 4 + 1] = y + 1; coins[n * 4 + 2] = z; coins[n * 4 + 3] = 1; n++;
  }
  while (n < NCOIN) {
    const a = wrand() * TAU, r = 18 + wrand() * 85;
    const x = cos(a) * r, z = sin(a) * r, y = cruiseY(x, z, -34);
    coins[n * 4] = x; coins[n * 4 + 1] = y + 0.9; coins[n * 4 + 2] = z; coins[n * 4 + 3] = 1; n++;
  }
  for (let i = 0; i < NFISH; i++) {
    const a = TAU * i / NFISH + 0.3, r = 22 + (i % 4) * 12;
    const x = 10 + cos(a) * r, z = 7 + sin(a) * r;
    fishS[i * 8] = x; fishS[i * 8 + 1] = cruiseY(x, z, -20); fishS[i * 8 + 2] = z;
    fishS[i * 8 + 3] = wrand() * TAU; fishS[i * 8 + 4] = 2.2; fishS[i * 8 + 5] = wrand() * TAU; fishS[i * 8 + 6] = 1;
  }
}
// Third grade, and it stays there: 1×1 through 12×12, two-digit add, two-digit subtract that stays ≥ 0.
function makeQ() {
  const k = wrand() * 3 | 0;
  let a, b;
  if (k === 0) {
    a = 2 + (wrand() * 11 | 0); b = 2 + (wrand() * 11 | 0);
    qAns = a * b; qText = a + ' × ' + b;
  } else if (k === 1) {
    a = 10 + (wrand() * 90 | 0); b = 10 + (wrand() * 90 | 0);
    qAns = a + b; qText = a + ' + ' + b;
  } else {
    a = 10 + (wrand() * 90 | 0); b = 10 + (wrand() * 90 | 0);
    if (b > a) { const t = a; a = b; b = t; }
    qAns = a - b; qText = a + ' − ' + b;
  }
}
function showQuiz() {
  const card = el('qq'), note = el('qnote'), ans = el('qin'), tim = el('qt'), title = el('qtitle');
  if (title) title.textContent = 'Math time!';
  if (card) card.textContent = qText;
  if (note) note.textContent = 'Twenty seconds. A right answer scores. A miss costs a heart.';
  if (ans) { ans.value = ''; ans.readOnly = false; }
  if (tim) tim.textContent = String(QSEC);
  const q = el('quiz'); if (q) q.style.display = 'grid';
  if (typeof document !== 'undefined') {
    document.body.className = 'g q';
    if (document.pointerLockElement) document.exitPointerLock();
    if (ans) setTimeout(() => R[PAUSE] && ans.focus(), 30);
  }
}
function hideQuiz() {
  const q = el('quiz'); if (q) q.style.display = 'none';
  if (typeof document !== 'undefined' && !R[OVER]) {
    document.body.className = document.pointerLockElement ? 'g p' : 'g';
  }
}
function showMiss() {
  const note = el('qnote'), ans = el('qin'), title = el('qtitle');
  if (title) title.textContent = 'Nice try!';
  if (note) note.textContent = qText + '  =  ' + qAns;
  if (ans) { ans.value = String(qAns); ans.readOnly = true; }
}
function beginQuiz(points) {
  if (R[PAUSE] || R[OVER]) return;
  makeQ();
  R[PAUSE] = 1; R[QT] = QSEC; R[QPTS] = points; qShow = 0; qDead = 0;
  F[VX] = F[VY] = F[VZ] = 0;
  if (typeof release === 'function') release();
  showQuiz();
}
function digitsOnly(s) {
  let o = '';
  const t = String(s);
  for (let i = 0; i < t.length && o.length < 4; i++) { const c = t.charCodeAt(i); if (c >= 48 && c <= 57) o += t[i]; }
  return o;
}
// '' ignores the key. Digits, backspace/delete and enter (including the numpad) are the only accepts.
function quizAct(key, code) {
  if (key === 'Enter' || code === 'Enter' || code === 'NumpadEnter') return 'ok';
  if (key === 'Backspace' || key === 'Delete') return 'bs';
  if (typeof key === 'string' && key.length === 1) { const c = key.charCodeAt(0); if (c >= 48 && c <= 57) return key; }
  return '';
}
function gameAnswer(raw) {
  if (!R[PAUSE] || qShow > 0) return;
  raw = digitsOnly(raw);
  const n = +raw;
  if (raw !== '' && n === qAns) {
    R[COMBO] += 1;
    R[SCORE] += R[QPTS] * R[COMBO];
    if (R[SCORE] > R[HIGH]) R[HIGH] = R[SCORE];
    R[PAUSE] = 0;
    hideQuiz();
    paintHud(1);
    return;
  }
  R[COMBO] = 0;
  qShow = 1.8;
  qDead = loseLife(2);
  showMiss();
  paintHud(1);
}
function gameQuiz(dt) {
  if (qShow > 0) {
    qShow -= dt;
    const tim = el('qt'); if (tim) tim.textContent = qShow > 0.4 ? 'see it' : '';
    if (qShow <= 0) { R[PAUSE] = 0; hideQuiz(); paintHud(1); return qDead ? 1 : 0; }
    return 0;
  }
  R[QT] -= dt;
  const tim = el('qt');
  if (tim) tim.textContent = String(R[QT] > 0 ? (R[QT] + 0.999 | 0) : 0);
  if (R[QT] <= 0) { R[COMBO] = 0; qShow = 1.8; qDead = loseLife(2); showMiss(); paintHud(1); }
  return 0;
}
function gamePress(k) {
  if (!R[PAUSE] || qShow > 0) return;
  const f = el('qin'); if (!f) { if (k === 'ok') gameAnswer(''); return; }
  if (k === 'bs') f.value = digitsOnly(f.value).slice(0, -1);
  else if (k === 'ok') gameAnswer(f.value);
  else if (typeof k === 'string' && k.length === 1 && k >= '0' && k <= '9' && digitsOnly(f.value).length < 4) f.value = digitsOnly(f.value) + k;
}
function tryPickups() {
  for (let i = 0; i < NCOIN; i++) {
    if (!coins[i * 4 + 3]) continue;
    const dx = coins[i * 4] - F[CX], dy = coins[i * 4 + 1] - F[CY], dz = coins[i * 4 + 2] - F[CZ];
    if (dx * dx + dy * dy + dz * dz < COIN_R2) {
      coins[i * 4 + 3] = 0; R[COINS] += 1; beginQuiz(100); return;
    }
  }
  for (let i = 0; i < NFISH; i++) if (catchFish(i)) return;
}
// true when the swimmer is touching the fish's body, not only its center point
function fishTouch(b) {
  const yw = fishS[b + 3], fx = sin(yw), fz = -cos(yw), half = 1.35;
  const px = F[CX] - fishS[b], py = F[CY] - fishS[b + 1], pz = F[CZ] - fishS[b + 2];
  let along = px * fx + pz * fz;
  if (along > half) along = half; else if (along < -half) along = -half;
  const dx = px - fx * along, dz = pz - fz * along;
  return dx * dx + py * py + dz * dz < FISH_R2;
}
function catchFish(i) {
  const b = i * 8;
  if (!fishS[b + 6] || !fishTouch(b)) return 0;
  fishS[b + 6] = 0; R[FISHN] += 1; beginQuiz(250); return 1;
}
function stepFish(dt) {
  for (let i = 0; i < NFISH; i++) {
    const b = i * 8;
    if (!fishS[b + 6]) continue;
    const dx = fishS[b] - F[CX], dy = fishS[b + 1] - F[CY], dz = fishS[b + 2] - F[CZ];
    const d = hypot(dx, dy, dz);
    if (d < 6 && d > 3.4) fishS[b + 7] = 1.4;
    let spd = 2.1, turn = 0.8;
    if (fishS[b + 7] > 0) { fishS[b + 7] -= dt; spd = 6.2; turn = 2.2; }
    const want = fishS[b + 7] > 0 ? atan2(dx, -dz) : fishS[b + 3] + sin(R[SURV] * 0.3 + fishS[b + 5]) * 0.8;
    const ye = wrapAng(want - fishS[b + 3]), st = turn * dt;
    fishS[b + 3] += ye > st ? st : ye < -st ? -st : ye;
    const yw = fishS[b + 3];
    fishS[b] += sin(yw) * spd * dt;
    fishS[b + 2] -= cos(yw) * spd * dt;
    const y = cruiseY(fishS[b], fishS[b + 2], -22);
    fishS[b + 1] += (y - fishS[b + 1]) * (1 - exp(-dt * 1.5));
    fishS[b + 4] = spd;
  }
}
function stepShark(i, dt, blind) {
  const o = i * STR;
  if (!SH[o + 22]) return 0;
  const dx = F[CX] - SH[o], dy = F[CY] - SH[o + 1], dz = F[CZ] - SH[o + 2];
  const dist = hypot(dx, dy, dz);
  const seen = !blind && R[INV] <= 0 && canSee(o) && dist < SIGHT;
  if (blind) { SH[o + 9] = 0; SH[o + 10] = 0; }
  else if (seen && dist < DROPD) {
    if (SH[o + 9] !== 1) SH[o + 11] = 0;
    SH[o + 9] = 1; SH[o + 10] = 0; SH[o + 11] += dt;
    SH[o + 12] = F[CX]; SH[o + 13] = F[CY]; SH[o + 14] = F[CZ];
  } else if (SH[o + 9]) {
    SH[o + 9] = 2; SH[o + 10] += dt;
    if (SH[o + 10] > GIVEUP || dist > DROPD) SH[o + 9] = 0;
  }
  let tx, ty, tz, spd, turn;
  if (SH[o + 9] === 1) {
    const u = SH[o + 11] / LOCKNEED;
    spd = u < 1 ? 4.8 + (chaseSpd() - 4.8) * u : chaseSpd();
    turn = 1.35;
    if (SH[o + 11] < 1.5) {
      const px = -dz / (dist || 1), pz = dx / (dist || 1);
      tx = F[CX] + px * 9; tz = F[CZ] + pz * 9; ty = F[CY];
    } else { tx = F[CX] + F[VX] * 0.15; ty = F[CY]; tz = F[CZ] + F[VZ] * 0.15; }
  } else if (SH[o + 9] === 2) {
    tx = SH[o + 12]; ty = SH[o + 13]; tz = SH[o + 14]; spd = 6.5; turn = 1.1;
  } else {
    tx = SH[o + 12]; ty = SH[o + 13]; tz = SH[o + 14]; spd = 4.5; turn = 0.85;
    if (hypot(SH[o] - tx, SH[o + 2] - tz) < 7 || hypot(SH[o] - F[CX], SH[o + 2] - F[CZ]) > 50) {
      const dds = hypot(F[CX] - SH[o], F[CZ] - SH[o + 2]);
      if (dds > 48) { tx = F[CX] - (F[CX] - SH[o]) / dds * 24; tz = F[CZ] - (F[CZ] - SH[o + 2]) / dds * 24; }
      else { const a = wrand() * TAU, r = 12 + wrand() * 12; tx = SH[o] + cos(a) * r; tz = SH[o + 2] + sin(a) * r; }
      ty = cruiseY(tx, tz, -26);
      SH[o + 12] = tx; SH[o + 13] = ty; SH[o + 14] = tz;
    }
  }
  steer(o, tx, ty, tz, spd, turn, dt);
  const hz = 0.8 + SH[o + 6] * 0.08;
  SH[o + 8] += (hz - SH[o + 8]) * (1 - exp(-dt * 2));
  if (!blind && R[INV] <= 0 && reached(o)) return 1;
  return 0;
}
function gameSync() {
  for (let i = 0; i < NS; i++) {
    const o = i * STR, b = i * 8;
    sharkInst[b] = SH[o]; sharkInst[b + 1] = SH[o + 1]; sharkInst[b + 2] = SH[o + 2]; sharkInst[b + 3] = SH[o + 3];
    sharkInst[b + 4] = SH[o + 4]; sharkInst[b + 5] = SH[o + 5]; sharkInst[b + 6] = SH[o + 7];
    sharkInst[b + 7] = SH[o + 22] ? (SH[o + 8] > 0.4 ? SH[o + 8] : 0.4) : 0.4;
    if (!SH[o + 22]) sharkInst[b + 1] = -220;
  }
  for (let i = 0; i < NCOIN; i++) {
    const b = i * 8;
    coinInst[b] = coins[i * 4]; coinInst[b + 1] = coins[i * 4 + 1]; coinInst[b + 2] = coins[i * 4 + 2];
    coinInst[b + 4] = coins[i * 4 + 3]; coinInst[b + 5] = i * 1.7;
  }
  for (let i = 0; i < NFISH; i++) {
    const b = i * 8, s = i * 8;
    goldInst[b] = fishS[s]; goldInst[b + 1] = fishS[s + 1]; goldInst[b + 2] = fishS[s + 2]; goldInst[b + 3] = fishS[s + 3];
    goldInst[b + 4] = 0; goldInst[b + 5] = 1.4 + (fishS[s + 7] > 0 ? 1.2 : 0); goldInst[b + 6] = fishS[s + 6] ? 2.3 : 0;
  }
}
function paintHud(dt) {
  hudAcc += dt;
  if (dt < 1 && hudAcc < 0.12) return;
  hudAcc = 0;
  if (typeof document === 'undefined') return;
  const sec = R[SURV] | 0;
  if (sec !== hudTime) { hudTime = sec; const t = el('tc'); if (t && typeof fmt === 'function') t.textContent = fmt(R[SURV]); }
  const sc = R[SCORE] | 0, cb = R[COMBO] | 0;
  if (sc !== shownScore || cb !== shownCombo) {
    shownScore = sc; shownCombo = cb;
    const s = el('sc');
    if (s) s.textContent = sc + (cb > 1 ? '   combo ×' + cb : '');
  }
  const hearts = R[LIVES] | 0;
  if (hearts !== shownLives) {
    shownLives = hearts;
    const h = el('hearts');
    if (h) h.textContent = '♥'.repeat(hearts) + '♡'.repeat(hearts < 3 ? 3 - hearts : 0);
  }
  const ai = el('airi'); if (ai) { ai.style.transform = 'scaleX(' + (R[AIR] / AIRMAX) + ')'; ai.className = R[AIR] < AIRLOW ? 'low' : ''; }
  const st = el('stami'); if (st) st.style.transform = 'scaleX(' + R[STAM] + ')';
}
function gamePaint() {
  const c = el('so');
  if (!c) return;
  const w = innerWidth | 0, h = innerHeight | 0;
  if (w < 2 || h < 2) return;
  if (c.width !== w || c.height !== h) { c.width = w; c.height = h; }
  const g = c.getContext('2d');
  g.clearRect(0, 0, w, h);
  if (!R[RUN] || R[OVER] || (typeof menu !== 'undefined' && menu)) return;
  g.lineWidth = 3; g.lineJoin = 'round';
  for (let i = 0; i < NS; i++) {
    const o = i * STR;
    if (!SH[o + 22]) continue;
    const dx = SH[o] - F[CX], dy = SH[o + 1] - F[CY], dz = SH[o + 2] - F[CZ];
    const dist = hypot(dx, dy, dz);
    if (dist > 70 || dist < 1) continue;
    const f = dx * F[FX] + dy * F[FY] + dz * F[FZ];
    const rgt = dx * F[RX] + dz * F[RZ];
    const up = dx * F[UX] + dy * F[UY] + dz * F[UZ];
    const wide = typeof TANH !== 'undefined' ? TANH : 0.6;
    if (f > 0.8 && abs(rgt) < f * wide * (w / h) * 0.85 && abs(up) < f * wide * 0.85) continue;
    let sx = rgt, sy = -up;
    if (f < 0.3) { sx = rgt || 0.01; }
    const L = hypot(sx, sy) || 1;
    sx /= L; sy /= L;
    const px = w * 0.5 + sx * w * 0.44, py = h * 0.5 + sy * h * 0.4;
    g.save();
    g.translate(px, py); g.rotate(atan2(sy, sx));
    g.fillStyle = SH[o + 9] === 1 ? '#ff8d7a' : '#ffd27a';
    g.beginPath(); g.moveTo(16, 0); g.lineTo(-10, 9); g.lineTo(-10, -9); g.closePath(); g.fill();
    g.restore();
  }
  let best = 1e9, bx = 0, bz = 0, any = 0;
  for (let i = 0; i < NCOIN; i++) {
    if (!coins[i * 4 + 3]) continue;
    const d = hypot(coins[i * 4] - F[CX], coins[i * 4 + 2] - F[CZ]);
    if (d < best) { best = d; bx = coins[i * 4]; bz = coins[i * 4 + 2]; any = 1; }
  }
  const cx = 78, cy = h - 78;
  g.strokeStyle = '#7ff3ff'; g.beginPath(); g.arc(cx, cy, 36, 0, TAU); g.stroke();
  g.fillStyle = '#e8fbff'; g.beginPath(); g.arc(cx, cy, 3, 0, TAU); g.fill();
  if (any) {
    const dx = bx - F[CX], dz = bz - F[CZ];
    const rx = dx * F[RX] + dz * F[RZ], fx = dx * F[FX] + dz * F[FZ];
    const ang = atan2(rx, fx);
    g.strokeStyle = '#ffd56a'; g.lineWidth = 4;
    g.beginPath(); g.moveTo(cx, cy); g.lineTo(cx + sin(ang) * 28, cy - cos(ang) * 28); g.stroke();
  }
}
function gameReady(w) {
  kelpMap = w.kelp; shipP = w.shipP; shipQ = w.shipQ;
  tuneKelp();
  try { R[BEST] = +localStorage.abyssalBest || 0; R[HIGH] = +localStorage.abyssalScore || 0; } catch { /* private mode */ }
  scatter();
  ringSharks(10, -28, 7, 2);
  gameSync();
}
function gameDive() { if (R[OVER] || R[RUN]) return; freshRun(); }
function gameRestart() { freshRun(); }
function gameIdle(dt) {
  const k = 1 - exp(-dt * 3);
  danger += -danger * k; vignette += -vignette * k; airWarn += -airWarn * k;
}
function gamePaused() { return R[PAUSE] > 0; }
function gamePace(held) {
  if (held && R[STAM] > (R[SPRINT] ? 0.02 : 0.2)) R[SPRINT] = 1;
  else R[SPRINT] = 0;
  return R[SPRINT] ? 26 : 7;
}
function gameTick(dt, blind) {
  if (R[PAUSE] || R[OVER]) return 0;
  if (R[INV] > 0) R[INV] -= dt;
  R[SURV] += dt;
  if (R[SURV] > R[BEST]) R[BEST] = R[SURV];
  if (!blind && R[INV] <= 0.2) tryPickups();
  if (R[PAUSE]) { gameSync(); paintHud(dt); return 0; }
  const wantN = sharkCount();
  if (R[NSH] < wantN) {
    const i = R[NSH], a = wrand() * TAU;
    placeShark(i, F[CX] + cos(a) * 34, F[CY], F[CZ] + sin(a) * 34, a + PI);
    R[NSH] = i + 1;
  }
  let hit = 0, wantD = 0, wantV = 0;
  for (let i = 0; i < NS; i++) {
    if (stepShark(i, dt, blind)) hit = 1;
    const o = i * STR;
    if (!SH[o + 22] || SH[o + 9] !== 1) continue;
    const u = clamp((SIGHT - hypot(F[CX] - SH[o], F[CY] - SH[o + 1], F[CZ] - SH[o + 2])) / (SIGHT - 3), 0, 1);
    const shaped = u * (0.25 + 0.75 * u) * (SH[o + 11] < LOCKNEED ? 0.45 : 1);
    if (shaped > wantD) wantD = shaped;
    if (shaped > wantV) wantV = shaped;
  }
  stepFish(dt);
  if (R[SPRINT]) R[STAM] -= dt * 0.32; else R[STAM] += dt * 0.2;
  if (R[STAM] < 0) R[STAM] = 0; else if (R[STAM] > 1) R[STAM] = 1;
  if (F[CY] > -4.2) R[AIR] += dt * 18; else R[AIR] -= dt;
  if (R[AIR] > AIRMAX) R[AIR] = AIRMAX; else if (R[AIR] < 0) R[AIR] = 0;
  airWarn = R[AIR] < AIRLOW ? (AIRLOW - R[AIR]) / AIRLOW : 0;
  const k = 1 - exp(-dt * 4);
  danger += (wantD - danger) * k; vignette += (wantV - vignette) * k;
  paintHud(dt);
  if (!blind && R[INV] <= 0 && !R[PAUSE] && R[AIR] <= 0) { gameSync(); return loseLife(0); }
  if (!blind && hit) { gameSync(); return loseLife(1); }
  if ((R[SURV] | 0) % 8 === 0) saveScores();
  gameSync();
  return 0;
}
