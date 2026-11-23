// ============================================================================
// gameplay: sharks, air, coins, golden fish, turtles, sea monster, math
// ============================================================================
// Questions stay at one level for the whole run: times tables through 12×12,
// two-digit addition, and two-digit subtraction that never goes negative.
// A miss or a timeout costs a life. Correct answers score points, with a
// combo for a streak. A correct golden-fish answer also gives one heart, up to
// MAXH. Sharks, air and the clock all freeze while a question is up.
// Per-frame numbers live in typed arrays. Strings are built only when a
// question opens or the HUD text actually changes.

const NS = 5, STR = 24, NCOIN = 28, NFISH = 8, NTUR = 2, SCALE = 7.2;
const SH = new Float64Array(NS * STR);
const sharkInst = new Float32Array(NS * 8);
const coinInst = new Float32Array(NCOIN * 8);
const goldInst = new Float32Array(NFISH * 8);
const turInst = new Float32Array(NTUR * 8);
const monInst = new Float32Array(8);
const coins = new Float32Array(NCOIN * 4); // x, y, z, alive
const fishS = new Float64Array(NFISH * 8); // x y z yaw spd phase alive flee
const turS = new Float64Array(NTUR * 8); // x y z yaw phase alive respawn kind

// run state
const R = new Float64Array(24);
const SURV = 0, BEST = 1, SCORE = 2, HIGH = 3, AIR = 4, STAM = 5, LIVES = 6, INV = 7;
const COMBO = 8, COINS = 9, FISHN = 10, RUN = 11, OVER = 12, PAUSE = 13, QT = 14, QPTS = 15, NSH = 16, SPRINT = 17;
const QKIND = 18, MON = 19, MONT = 20, MHIT = 21;
const AIRMAX = 75, AIRLOW = 20, SIGHT = 32, LOCKNEED = 2.3, GIVEUP = 3.2, DROPD = 40;
const QSEC = 20, COIN_R2 = 1.35, FISH_R2 = 3.2;
const MAXH = 5, INV_HIT = 2, BITE = 2.2, BITE2 = BITE * BITE, TURT_BACK = 12, TURT_R2 = 3.24;
const MON_AT = 120, MON_RISE = 2.2, MON_HOLD = 1.6, MON_SINK = 1.7, MON_LEN = MON_RISE + MON_HOLD + MON_SINK;

let danger = 0, vignette = 0, airWarn = 0, shake = 0, scare = 0, cue = 0, roar = 0;
let toastT = 0, monX = 0, monY = -400, monZ = 0, monYaw = 0, monStruckAt = -1;
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
  SH[o + 15] = SH[o]; SH[o + 16] = SH[o + 1]; SH[o + 17] = SH[o + 2];
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
// closest-point distance from P to segment AB, squared. No temporaries that escape.
function segDist2(px, py, pz, ax, ay, az, bx, by, bz) {
  const abx = bx - ax, aby = by - ay, abz = bz - az;
  const apx = px - ax, apy = py - ay, apz = pz - az;
  const ab2 = abx * abx + aby * aby + abz * abz || 1;
  let t = (apx * abx + apy * aby + apz * abz) / ab2;
  if (t < 0) t = 0; else if (t > 1) t = 1;
  const dx = apx - abx * t, dy = apy - aby * t, dz = apz - abz * t;
  return dx * dx + dy * dy + dz * dz;
}
// The shark's mouth has to be the part that arrives. Looking away used to cancel the
// bite (the old test demanded the diver stare within about 60°), so a shark that
// was visibly on you often took nothing.
function sharkFaces(o) {
  const dx = F[CX] - SH[o], dy = F[CY] - SH[o + 1], dz = F[CZ] - SH[o + 2];
  const d = hypot(dx, dy, dz);
  if (d < 1.6) return 1;
  const cp = cos(SH[o + 4]), yw = SH[o + 3];
  const fx = cp * sin(yw), fy = sin(SH[o + 4]), fz = -cp * cos(yw);
  return (dx * fx + dy * fy + dz * fz) / d > 0.2 ? 1 : 0;
}
function jawHit(o) {
  const pit = SH[o + 4], yw = SH[o + 3], cp = cos(pit), sp = sin(pit);
  const fx = cp * sin(yw), fy = sp, fz = -cp * cos(yw);
  const nose = 0.58 * SCALE, gill = 0.16 * SCALE;
  const nx = SH[o] + fx * nose, ny = SH[o + 1] + fy * nose, nz = SH[o + 2] + fz * nose;
  const gx = SH[o] + fx * gill, gy = SH[o + 1] + fy * gill, gz = SH[o + 2] + fz * gill;
  if (segDist2(F[CX], F[CY], F[CZ], gx, gy, gz, nx, ny, nz) < BITE2) return 1;
  // the lunge between last frame and this one, so a fast frame cannot step over the diver
  const ox = SH[o + 15] + fx * nose, oy = SH[o + 16] + fy * nose, oz = SH[o + 17] + fz * nose;
  return segDist2(F[CX], F[CY], F[CZ], ox, oy, oz, nx, ny, nz) < BITE2 ? 1 : 0;
}
function biting(o) {
  if (SH[o + 11] < LOCKNEED) return 0;
  const st = SH[o + 9];
  // state 2 is the short search after a sight flicker. A finished lock still connects
  // for a moment; hiding for real (the give-up timer) does not.
  if (st !== 1 && !(st === 2 && SH[o + 10] < 0.55)) return 0;
  if (concealed() === 2) return 0;
  if (!sharkFaces(o)) return 0;
  return jawHit(o);
}
function chaseSpd() {
  const t = R[SURV];
  return 10.2 + (t > 80 ? 1.1 : 0) + (t > 160 ? 1.1 : 0) + (t > 240 ? 0.8 : 0);
}
// Was 2, then 3 after 65 s, 4 after 140 s, 5 after 220 s. Each stage is about 20% lower,
// rounded, and never under 2. 3×0.8 = 2.4 → 2, so the 65 s stage matches the start.
function sharkCount() {
  if (R[SURV] > 220) return 4;
  if (R[SURV] > 140) return 3;
  if (R[SURV] > 65) return 2;
  return 2;
}
function saveScores() {
  try {
    if (R[BEST] > 0) localStorage.abyssalBest = R[BEST];
    if (R[HIGH] > 0) localStorage.abyssalScore = R[HIGH];
  } catch { /* private mode */ }
}
function shoveDiver(bx, by, bz) {
  F[CX] -= bx * 4.2; F[CY] -= by * 1.4; F[CZ] -= bz * 4.2;
  const rad = hypot(F[CX], F[CZ]);
  if (rad > 145) { const s = 145 / rad; F[CX] *= s; F[CZ] *= s; }
  if (F[CY] > -2) F[CY] = -2; else if (F[CY] < -50) F[CY] = -50;
  const into = F[VX] * bx + F[VY] * by + F[VZ] * bz;
  if (into > 0) { F[VX] -= bx * into; F[VY] -= by * into; F[VZ] -= bz * into; }
}
const AWAY = new Float64Array(3);
// Drop the chase and push every nearby shark off the diver. Writes AWAY and returns 1
// when a shark was close enough to shove the diver the other way.
function breakOff() {
  let bx = 0, by = 0, bz = 1, bd = 1e9, found = 0;
  for (let i = 0; i < NS; i++) {
    const o = i * STR;
    if (!SH[o + 22]) continue;
    SH[o + 9] = 0; SH[o + 11] = 0; SH[o + 10] = 0;
    let dx = SH[o] - F[CX], dy = SH[o + 1] - F[CY], dz = SH[o + 2] - F[CZ];
    let d = hypot(dx, dy, dz);
    if (d < 0.4) {
      const cp = cos(SH[o + 4]), yw = SH[o + 3];
      dx = -cp * sin(yw); dy = -sin(SH[o + 4]); dz = cp * cos(yw);
      d = hypot(dx, dy, dz) || 1;
    }
    if (d < 24) { SH[o] += dx / d * 16; SH[o + 1] += dy / d * 5; SH[o + 2] += dz / d * 16; }
    if (d < bd) { bd = d; bx = dx / d; by = dy / d; bz = dz / d; found = 1; }
  }
  if (!(found && bd < 30)) return 0;
  AWAY[0] = bx; AWAY[1] = by; AWAY[2] = bz;
  return 1;
}
// kind: 0 air, 1 shark, 2 a missed math question, 3 the sea monster, 4 the black turtle.
// Anything except a math miss is ignored while invulnerable, so one contact is one heart.
// Returns 1 when the run ends.
function loseLife(kind) {
  if (R[OVER] || !R[RUN]) return R[OVER] ? 1 : 0;
  if (kind !== 2 && R[INV] > 0) return 0;
  R[LIVES] -= 1;
  vignette = 0.85;
  R[INV] = INV_HIT;
  if (kind === 0) R[AIR] = 30;
  if (kind === 1 || kind === 3 || kind === 4) cue = 2;
  if (breakOff() && (kind === 1 || kind === 4)) shoveDiver(AWAY[0], AWAY[1], AWAY[2]);
  if (R[LIVES] <= 0) {
    R[LIVES] = 0; R[OVER] = 1; scare = 0; shake = 0;
    if (R[SURV] > R[BEST]) R[BEST] = R[SURV];
    if (R[SCORE] > R[HIGH]) R[HIGH] = R[SCORE];
    saveScores();
    return 1;
  }
  return 0;
}
function gainHeart() {
  if (R[LIVES] >= MAXH) return 0;
  R[LIVES] += 1;
  return 1;
}
function freshRun() {
  R[RUN] = 1; R[SURV] = 0; R[SCORE] = 0; R[COINS] = 0; R[FISHN] = 0; R[COMBO] = 0;
  R[AIR] = AIRMAX; R[STAM] = 1; R[LIVES] = 3; R[INV] = 1.6; R[PAUSE] = 0; R[OVER] = 0; R[SPRINT] = 0;
  R[QKIND] = 0; R[MON] = 0; R[MONT] = 0; R[MHIT] = 0;
  danger = 0; vignette = 0; airWarn = 0; shake = 0; scare = 0; cue = 0; roar = 0; toastT = 0; monStruckAt = -1;
  qShow = 0; qDead = 0; shownScore = -1; shownCombo = -1; shownLives = -1; hudTime = -1;
  monX = 0; monY = -400; monZ = 0; monYaw = 0;
  for (let i = 0; i < NCOIN; i++) coins[i * 4 + 3] = 1;
  for (let i = 0; i < NFISH; i++) fishS[i * 8 + 6] = 1;
  for (let i = 0; i < NTUR; i++) placeTurtle(i, 0);
  ringSharks(F[CX], F[CY], F[CZ], 2);
  const q = el('quiz'); if (q) q.style.display = 'none';
  if (typeof document !== 'undefined') document.body.classList.remove('q');
  gameClearFx();
  gameSync();
  paintHud(1);
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
  for (let i = 0; i < NTUR; i++) placeTurtle(i, 0);
}
function placeTurtle(i, away) {
  const b = i * 8;
  const ox = away ? F[CX] : 10, oz = away ? F[CZ] : 7;
  let x = ox, z = oz, guard = 0;
  do {
    const a = TAU * (i + 0.5) / NTUR + wrand() * 1.4, r = 28 + wrand() * 48;
    x = ox + cos(a) * r; z = oz + sin(a) * r;
    const rad = hypot(x, z);
    if (rad > 112) { x *= 112 / rad; z *= 112 / rad; }
    guard++;
  } while (guard < 8 && hypot(x - ox, z - oz) < 24);
  turS[b] = x; turS[b + 2] = z; turS[b + 1] = cruiseY(x, z, -16);
  turS[b + 3] = wrand() * TAU; turS[b + 4] = wrand() * TAU;
  turS[b + 5] = 1; turS[b + 6] = 0; turS[b + 7] = i;
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
  if (note) note.textContent = R[QKIND] === 1
    ? 'Twenty seconds. A right answer scores and gives a heart.'
    : 'Twenty seconds. A right answer scores. A miss costs a heart.';
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
function beginQuiz(points, kind) {
  if (R[PAUSE] || R[OVER]) return;
  makeQ();
  R[PAUSE] = 1; R[QT] = QSEC; R[QPTS] = points; R[QKIND] = kind || 0; qShow = 0; qDead = 0;
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
    if (R[QKIND] === 1) {
      if (gainHeart()) { toast('Golden fish! +1 heart'); cue = 1; }
      else toast('Golden fish! Hearts are full');
    }
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
      coins[i * 4 + 3] = 0; R[COINS] += 1; beginQuiz(100, 0); return;
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
  fishS[b + 6] = 0; R[FISHN] += 1; beginQuiz(250, 1); return 1;
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
  SH[o + 15] = SH[o]; SH[o + 16] = SH[o + 1]; SH[o + 17] = SH[o + 2];
  const dx = F[CX] - SH[o], dy = F[CY] - SH[o + 1], dz = F[CZ] - SH[o + 2];
  const dist = hypot(dx, dy, dz);
  // Invulnerability used to drop the shark out of chase. The next seen frame then
  // zeroed the lock, so a shark already on the diver never finished the 2.3 s warning.
  const seen = !blind && canSee(o) && dist < SIGHT;
  if (blind) { SH[o + 9] = 0; SH[o + 10] = 0; }
  else if (seen && dist < DROPD) {
    if (SH[o + 9] === 0) SH[o + 11] = 0;
    SH[o + 9] = 1; SH[o + 10] = 0;
    if (R[INV] <= 0) SH[o + 11] += dt;
    SH[o + 12] = F[CX]; SH[o + 13] = F[CY]; SH[o + 14] = F[CZ];
  } else if (SH[o + 9]) {
    SH[o + 9] = 2; SH[o + 10] += dt;
    if (SH[o + 10] > GIVEUP || dist > DROPD) { SH[o + 9] = 0; SH[o + 11] = 0; }
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
  if (!blind && R[INV] <= 0 && biting(o)) return 1;
  return 0;
}
function turtTouch(b) {
  const yw = turS[b + 3], fx = sin(yw), fz = -cos(yw), half = 2.05;
  const px = F[CX] - turS[b], py = F[CY] - turS[b + 1], pz = F[CZ] - turS[b + 2];
  let along = px * fx + pz * fz;
  if (along > half) along = half; else if (along < -half) along = -half;
  const dx = px - fx * along, dz = pz - fz * along;
  return dx * dx + py * py + dz * dz < TURT_R2;
}
function stepTurtles(dt, blind) {
  let dead = 0;
  for (let i = 0; i < NTUR; i++) {
    const b = i * 8;
    if (turS[b + 5] < 0.5) {
      turS[b + 6] -= dt;
      if (turS[b + 6] <= 0) placeTurtle(i, 1);
      continue;
    }
    const wander = sin(R[SURV] * 0.17 + turS[b + 4]) * 0.55;
    turS[b + 3] += wander * dt;
    const yw = turS[b + 3], spd = 1.55;
    turS[b] += sin(yw) * spd * dt;
    turS[b + 2] -= cos(yw) * spd * dt;
    const rad = hypot(turS[b], turS[b + 2]);
    if (rad > 118) { const s = 118 / rad; turS[b] *= s; turS[b + 2] *= s; turS[b + 3] += 2.2; }
    const y = cruiseY(turS[b], turS[b + 2], -16);
    turS[b + 1] += (y - turS[b + 1]) * (1 - exp(-dt * 0.8));
    if (blind || !turtTouch(b)) continue;
    if (turS[b + 7] < 0.5) {
      turS[b + 5] = 0; turS[b + 6] = TURT_BACK;
      if (gainHeart()) { toast('Green turtle! +1 heart'); cue = 1; }
      else toast('Green turtle! Hearts are full');
    } else if (R[INV] <= 0) {
      turS[b + 5] = 0; turS[b + 6] = TURT_BACK;
      toast('Black turtle! −1 heart');
      if (loseLife(4)) dead = 1;
    }
  }
  return dead;
}
function stepMonster(dt) {
  if (R[MON] === 2) { monY = -400; return 0; }
  if (R[MON] === 0) {
    if (R[SURV] < MON_AT) { monY = -400; return 0; }
    R[MON] = 1; R[MONT] = 0; R[MHIT] = 0; roar = 1;
    const fl = hypot(F[FX], F[FZ]) || 1;
    monX = F[CX] + F[FX] / fl * 16; monZ = F[CZ] + F[FZ] / fl * 16;
    const rad = hypot(monX, monZ);
    if (rad > 120) { monX *= 120 / rad; monZ *= 120 / rad; }
    toast('Something huge is rising!');
  }
  R[MONT] += dt;
  const t = R[MONT];
  const fl = hypot(F[FX], F[FZ]) || 1;
  const tx = F[CX] + F[FX] / fl * 16, tz = F[CZ] + F[FZ] / fl * 16;
  const k = 1 - exp(-dt * 0.85);
  monX += (tx - monX) * k; monZ += (tz - monZ) * k;
  const rad = hypot(monX, monZ);
  if (rad > 120) { monX *= 120 / rad; monZ *= 120 / rad; }
  monYaw = atan2(F[CX] - monX, -(F[CZ] - monZ));
  // One life, through loseLife, once the head has cleared the dark. A blink from a
  // shark or a turtle only delays it — the monster stays until the heart lands.
  const biteBy = MON_RISE + MON_HOLD + 4;
  if (!R[MHIT] && t > 1.45 && t < biteBy && R[INV] <= 0) {
    R[MHIT] = 1; monStruckAt = t;
    toast('Sea monster!');
    if (loseLife(3)) return 1;
  }
  const holdUntil = R[MHIT] ? monStruckAt + 1.15 : biteBy;
  let y;
  if (t < holdUntil) {
    if (!R[MHIT] && t < MON_RISE) {
      let u = t / MON_RISE; u = u * u * (3 - 2 * u);
      y = (F[CY] - 36) + u * 34;
      shake = 0.2 + u * 1.15; scare = u * 0.92;
    } else {
      y = F[CY] - 2; shake = 0.95; scare = 0.95;
    }
  } else {
    const s = (t - holdUntil) / MON_SINK;
    if (s >= 1) { R[MON] = 2; shake = 0; scare = 0; monY = -400; return 0; }
    y = (F[CY] - 2) - s * s * 42;
    shake = (1 - s) * 0.55; scare = (1 - s) * 0.75;
  }
  monY = y;
  return 0;
}
function toast(s) {
  toastT = 2.8;
  const n = el('toast');
  if (n) { n.textContent = s; n.style.opacity = '1'; }
}
function gameClearFx() {
  scare = 0; shake = 0; toastT = 0;
  if (typeof document === 'undefined') return;
  document.body.classList.remove('ifr');
  const s = el('scare'); if (s) s.style.opacity = '0';
  const t = el('toast'); if (t) t.style.opacity = '0';
}
function paintFx(dt) {
  if (toastT > 0) {
    toastT -= dt;
    if (toastT <= 0) { const t = el('toast'); if (t) t.style.opacity = '0'; }
  }
  if (typeof document === 'undefined') return;
  const hot = R[RUN] && !R[OVER] && R[PAUSE] <= 0 && R[INV] > 0.04 && (((R[INV] * 8) | 0) & 1) === 0;
  document.body.classList.toggle('ifr', hot);
  const s = el('scare'); if (s) s.style.opacity = String(scare > 0 ? scare : 0);
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
  for (let i = 0; i < NTUR; i++) {
    const b = i * 8, s = i * 8;
    turInst[b] = turS[s]; turInst[b + 1] = turS[s + 1]; turInst[b + 2] = turS[s + 2]; turInst[b + 3] = turS[s + 3];
    turInst[b + 4] = turS[s + 7]; turInst[b + 5] = turS[s + 4]; turInst[b + 6] = turS[s + 5] > 0.5 ? 2.6 : 0;
  }
  monInst[0] = monX; monInst[1] = monY; monInst[2] = monZ; monInst[3] = monYaw;
  monInst[4] = 0.15; monInst[5] = 0; monInst[6] = R[MONT]; monInst[7] = R[MON] === 1 ? 1 : 0;
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
    if (h) h.textContent = '♥'.repeat(hearts) + '♡'.repeat(hearts < MAXH ? MAXH - hearts : 0);
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
  shake += -shake * k; scare += -scare * k;
  paintFx(dt);
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
  const turtleDead = !blind && !R[PAUSE] && stepTurtles(dt, blind);
  if (R[SPRINT]) R[STAM] -= dt * 0.32; else R[STAM] += dt * 0.2;
  if (R[STAM] < 0) R[STAM] = 0; else if (R[STAM] > 1) R[STAM] = 1;
  if (F[CY] > -4.2) R[AIR] += dt * 18; else R[AIR] -= dt;
  if (R[AIR] > AIRMAX) R[AIR] = AIRMAX; else if (R[AIR] < 0) R[AIR] = 0;
  airWarn = R[AIR] < AIRLOW ? (AIRLOW - R[AIR]) / AIRLOW : 0;
  const k = 1 - exp(-dt * 4);
  danger += (wantD - danger) * k; vignette += (wantV - vignette) * k;
  paintHud(dt);
  paintFx(dt);
  if (!blind && R[INV] <= 0 && !R[PAUSE] && R[AIR] <= 0) { gameSync(); if (loseLife(0)) return 1; }
  if (!blind && hit) {
    // Already blinking: still separate, so the shark is not waiting on the diver when it ends.
    if (R[INV] > 0) breakOff();
    else { gameSync(); if (loseLife(1)) return 1; }
  }
  const monsterDead = !blind && stepMonster(dt);
  if (turtleDead || monsterDead) { gameSync(); return 1; }
  if ((R[SURV] | 0) % 8 === 0) saveScores();
  gameSync();
  return 0;
}
