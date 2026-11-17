// ============================================================================
// gameplay: shark chase
// ============================================================================
// The free-swim scene stays as it is. This layer adds one predator and a survival clock.
// Coins and an air meter are not in yet: give them slots beside SURV, step them at the
// end of gameTick, and draw them from the same HUD update as the timer in main.js.
// All per-frame state lives in GS / sharkInst, so the frame loop allocates nothing.

// GS: 0-2 position, 3 yaw, 4 pitch, 5 roll, 6 speed, 7 phase, 8 tail Hz,
// 9 mode (0 patrol, 1 chase, 2 search), 10 seconds since sight was lost,
// 11 survived, 12 best, 13 grace, 14-16 last seen, 17 waypoint, 18-19 wander offset,
// 20 cruise height, 21 run started, 22 caught, 23 stuck timer, 24-25 stuck sample
const GS = new Float64Array(26);
const SX = 0, SY = 1, SZ = 2, SYAW = 3, SPIT = 4, SROL = 5, SSPD = 6, PHASE = 7, BEAT = 8;
const MODE = 9, LOST = 10, SURV = 11, BEST = 12, GRACE = 13;
const LX = 14, LY = 15, LZ = 16, WPI = 17, TOX = 18, TOZ = 19, TY = 20, RUN = 21, CAUGHT = 22, STUCK = 23, PX = 24, PZ = 25;
const sharkInst = new Float32Array(8);
// threat fed to the heartbeat (audio.js) and, while actually chasing, the red vignette (mis.w)
let danger = 0, vignette = 0;
let kelpMap, shipP, shipQ, kelpHide = 255, kelpBlock = 255;
const SIGHT = 34, GIVEUP = 4, SNOUT = 0.52 * 6.2;
const WP = new Float32Array([
  18, -26, 24, 55, -24, 14, 72, -22, -6, 36, -28, -46, 6, -32, -78, -28, -26, -56,
  -66, -22, -8, -46, -24, 38, -10, -28, 66, 20, -30, 42, -4, -30, -8, 42, -22, 34,
]);
const WPN = 12;
let wr = 0x5EED;
const wrand = () => { wr = (Math.imul(wr, 1664525) + 1013904223) | 0; return (wr >>> 0) / 4294967296; };
let QX = 0, QY = 0, QZ = 0, SLX = 0, SLY = 0, SLZ = 0;

function qApply(qx, qy, qz, qw, x, y, z) {
  const cx = qy * z - qz * y + qw * x, cy = qz * x - qx * z + qw * y, cz = qx * y - qy * x + qw * z;
  QX = x + 2 * (qy * cz - qz * cy); QY = y + 2 * (qz * cx - qx * cz); QZ = z + 2 * (qx * cy - qy * cx);
}
function toShip(x, y, z) {
  qApply(-shipQ[0], -shipQ[1], -shipQ[2], shipQ[3], x - shipP[0], y - shipP[1], z - shipP[2]);
  SLX = QX; SLY = QY; SLZ = QZ;
}
function toWorld(x, y, z) {
  qApply(shipQ[0], shipQ[1], shipQ[2], shipQ[3], x, y, z);
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
// signed distance to rock, metres (> 0 inside rock), same field the camera collides with
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
  // the collision field is clamped to ±1 m, so -1 means "at least a metre of water"
  let best = prefer, score = 1e9;
  for (let y = -8; y >= -44; y -= 2) {
    const d = rockAt(x, y, z);
    if (d > -0.45) continue;
    const sc = abs(y - prefer) + (d > -0.9 ? 6 : 0);
    if (sc < score) { score = sc; best = y; }
  }
  return best;
}
function pushOut() {
  for (let k = 0; k < 2; k++) {
    const d = rockAt(GS[SX], GS[SY], GS[SZ]);
    if (d < -0.55) return;
    const e = 0.8;
    let gx = rockAt(GS[SX] + e, GS[SY], GS[SZ]) - rockAt(GS[SX] - e, GS[SY], GS[SZ]);
    let gy = rockAt(GS[SX], GS[SY] + e, GS[SZ]) - rockAt(GS[SX], GS[SY] - e, GS[SZ]);
    let gz = rockAt(GS[SX], GS[SY], GS[SZ] + e) - rockAt(GS[SX], GS[SY], GS[SZ] - e);
    const l = hypot(gx, gy, gz) || 1;
    const p = d + 0.7;
    GS[SX] -= gx / l * p; GS[SY] -= gy / l * p; GS[SZ] -= gz / l * p;
  }
}
function inShipBox() {
  return abs(SLX) < 17.5 && abs(SLY) < 8.2 && abs(SLZ) < 6.4;
}
function pushShip() {
  toShip(GS[SX], GS[SY], GS[SZ]);
  if (!inShipBox()) return;
  const px = 17.5 - abs(SLX), py = 8.2 - abs(SLY), pz = 6.4 - abs(SLZ);
  let lx = 0, ly = 0, lz = 0;
  if (px <= py && px <= pz) lx = (SLX < 0 ? -px : px) + (SLX < 0 ? -0.4 : 0.4);
  else if (py <= pz) ly = (SLY < 0 ? -py : py) + (SLY < 0 ? -0.4 : 0.4);
  else lz = (SLZ < 0 ? -pz : pz) + (SLZ < 0 ? -0.4 : 0.4);
  toWorld(lx, ly, lz);
  GS[SX] += QX; GS[SY] += QY; GS[SZ] += QZ;
}
function placeShark(x, y, z, yaw) {
  GS[SX] = x; GS[SZ] = z; GS[SY] = cruiseY(x, z, y); GS[SYAW] = yaw; GS[SPIT] = 0; GS[SROL] = 0;
  for (let i = 0; i < 3; i++) { pushOut(); pushShip(); }
}
function pickWp(step) {
  let i = (GS[WPI] + step) % WPN; if (i < 0) i += WPN;
  GS[WPI] = i;
  GS[TOX] = (wrand() - 0.5) * 16; GS[TOZ] = (wrand() - 0.5) * 16;
  GS[TY] = cruiseY(WP[i * 3] + GS[TOX], WP[i * 3 + 2] + GS[TOZ], WP[i * 3 + 1]);
}
function wrapAng(a) {
  a = (a + PI) / TAU; a -= floor(a); if (a < 0) a += 1;
  return a * TAU - PI;
}
function aheadBlocked(yaw, pit, dist) {
  const cp = cos(pit), x = GS[SX] + cp * sin(yaw) * dist, y = GS[SY] + sin(pit) * dist, z = GS[SZ] - cp * cos(yaw) * dist;
  if (rockAt(x, y, z) > -0.35) return 1;
  toShip(x, y, z);
  return inShipBox() ? 1 : 0;
}
function steer(tx, ty, tz, spd, turn, dt) {
  let dx = tx - GS[SX], dy = ty - GS[SY], dz = tz - GS[SZ];
  const yaw = GS[SYAW], pit = GS[SPIT];
  if (aheadBlocked(yaw, pit, 9)) {
    const left = aheadBlocked(yaw + 1, pit, 9), right = aheadBlocked(yaw - 1, pit, 9);
    const side = left <= right ? 1.2 : -1.2;
    if (left && right && !aheadBlocked(yaw, pit + 0.45, 8)) dy += 14;
    dx = sin(yaw + side) * 14; dz = -cos(yaw + side) * 14;
  }
  const ye = wrapAng(atan2(dx, -dz) - yaw);
  const step = turn * dt;
  const dyaw = ye > step ? step : ye < -step ? -step : ye;
  GS[SYAW] = yaw + dyaw;
  let wantPit = atan2(dy, hypot(dx, dz) || 1);
  if (wantPit > 0.48) wantPit = 0.48; else if (wantPit < -0.55) wantPit = -0.55;
  const dp = wantPit - pit, ps = 0.6 * dt;
  GS[SPIT] = pit + (dp > ps ? ps : dp < -ps ? -ps : dp);
  const yv = dt > 1e-4 ? dyaw / dt : 0;
  const wantRol = yv < -2.4 ? -0.55 : yv > 2.4 ? 0.55 : -yv * 0.22;
  GS[SROL] += (wantRol - GS[SROL]) * (1 - exp(-dt * 2.6));
  GS[SSPD] += (spd - GS[SSPD]) * (1 - exp(-dt * 2.2));
  const cyaw = GS[SYAW], cpit = GS[SPIT], ccp = cos(cpit);
  GS[SX] += ccp * sin(cyaw) * GS[SSPD] * dt;
  GS[SY] += sin(cpit) * GS[SSPD] * dt;
  GS[SZ] -= ccp * cos(cyaw) * GS[SSPD] * dt;
  const rad = hypot(GS[SX], GS[SZ]);
  if (rad > 132) { const s = 132 / rad; GS[SX] *= s; GS[SZ] *= s; }
  if (GS[SY] > -4.5) GS[SY] = -4.5; else if (GS[SY] < -47) GS[SY] = -47;
  pushOut();
  pushShip();
}
// 2: inside the wreck, 1: inside thick kelp, 0: in the open
function concealed() {
  toShip(F[CX], F[CY], F[CZ]);
  if (shipSection(SLX, SLY, SLZ, false)) return 2;
  return kelpAt(F[CX], F[CZ]) >= kelpHide ? 1 : 0;
}
function canSee() {
  const dx = F[CX] - GS[SX], dy = F[CY] - GS[SY], dz = F[CZ] - GS[SZ];
  if (dx * dx + dy * dy + dz * dz > SIGHT * SIGHT) return 0;
  if (concealed()) return 0;
  const dist = hypot(dx, dy, dz);
  let steps = dist * 0.45 | 0;
  if (steps < 2) steps = 2; else if (steps > 22) steps = 22;
  for (let i = 1; i < steps; i++) {
    const t = i / steps, x = GS[SX] + dx * t, y = GS[SY] + dy * t, z = GS[SZ] + dz * t;
    if (kelpAt(x, z) >= kelpBlock) return 0;
    toShip(x, y, z);
    if (shipSection(SLX, SLY, SLZ, true)) return 0;
  }
  return 1;
}
function reached() {
  toShip(F[CX], F[CY], F[CZ]);
  if (shipSection(SLX, SLY, SLZ, false)) return 0;
  if (GS[MODE] === 0 && kelpAt(F[CX], F[CZ]) >= kelpHide) return 0;
  const cp = cos(GS[SPIT]), yw = GS[SYAW];
  const mx = GS[SX] + cp * sin(yw) * SNOUT, my = GS[SY] + sin(GS[SPIT]) * SNOUT, mz = GS[SZ] - cp * cos(yw) * SNOUT;
  if (hypot(F[CX] - mx, F[CY] - my, F[CZ] - mz) < 1.55) return 1;
  return hypot(F[CX] - GS[SX], F[CY] - GS[SY], F[CZ] - GS[SZ]) < 1.28;
}
function gameSync() {
  sharkInst[0] = GS[SX]; sharkInst[1] = GS[SY]; sharkInst[2] = GS[SZ]; sharkInst[3] = GS[SYAW];
  sharkInst[4] = GS[SPIT]; sharkInst[5] = GS[SROL]; sharkInst[6] = GS[PHASE]; sharkInst[7] = GS[BEAT] > 0.4 ? GS[BEAT] : 0.4;
}
function gameReady(w) {
  kelpMap = w.kelp; shipP = w.shipP; shipQ = w.shipQ;
  tuneKelp();
  try { GS[BEST] = +localStorage.abyssalBest || 0; } catch { /* private mode */ }
  GS[PHASE] = wrand() * TAU; GS[BEAT] = 1.2; GS[SSPD] = 5.2;
  placeShark(-78, -25, 46, 0.6);
  pickWp(0);
  gameSync();
}
function gameDive() {
  if (GS[CAUGHT] || GS[RUN]) return;
  GS[RUN] = 1; GS[SURV] = 0; GS[GRACE] = 2; GS[MODE] = 0; GS[LOST] = 0;
}
function gameRestart() {
  GS[CAUGHT] = 0; GS[RUN] = 1; GS[SURV] = 0; GS[GRACE] = 2.4; GS[MODE] = 0; GS[LOST] = 0; GS[SSPD] = 5;
  danger = 0; vignette = 0;
  placeShark(-72, -26, -48, 2.2);
  pickWp(3);
  gameSync();
}
// menu / load: let the red edge and the heartbeat fall away, shark holds still
function gameIdle(dt) {
  const k = 1 - exp(-dt * 3);
  danger += -danger * k; vignette += -vignette * k;
}
// blind: dev fly-through, the shark keeps patrolling and ignores the camera
function gameTick(dt, blind) {
  if (GS[GRACE] > 0) GS[GRACE] -= dt;
  const seen = blind || GS[GRACE] > 0 ? 0 : canSee();
  if (blind) { GS[MODE] = 0; GS[LOST] = 0; }
  else if (seen) { GS[MODE] = 1; GS[LOST] = 0; GS[LX] = F[CX]; GS[LY] = F[CY]; GS[LZ] = F[CZ]; }
  else if (GS[MODE]) { GS[MODE] = 2; GS[LOST] += dt; if (GS[LOST] > GIVEUP) GS[MODE] = 0; }
  let tx, ty, tz, spd, turn;
  if (GS[MODE] === 1) {
    tx = F[CX] + F[VX] * 0.22; ty = F[CY] + F[VY] * 0.22; tz = F[CZ] + F[VZ] * 0.22; spd = 15; turn = 1.75;
  } else if (GS[MODE] === 2) {
    tx = GS[LX]; ty = GS[LY]; tz = GS[LZ]; spd = 8.5; turn = 1.25;
    if (hypot(GS[SX] - tx, GS[SZ] - tz) < 5.5) { tx = GS[SX] + sin(GS[SYAW] + 0.9) * 12; tz = GS[SZ] - cos(GS[SYAW] + 0.9) * 12; spd = 4.2; }
  } else {
    const i = GS[WPI] * 3;
    tx = WP[i] + GS[TOX]; ty = GS[TY]; tz = WP[i + 2] + GS[TOZ]; spd = 5.2; turn = 0.9;
    if (hypot(GS[SX] - tx, GS[SZ] - tz) < 8) pickWp(1 + (wrand() < 0.28 ? 1 : 0));
  }
  steer(tx, ty, tz, spd, turn, dt);
  GS[STUCK] += dt;
  if (GS[STUCK] > 2.5) {
    const moved = hypot(GS[SX] - GS[PX], GS[SZ] - GS[PZ]);
    GS[PX] = GS[SX]; GS[PZ] = GS[SZ]; GS[STUCK] = 0;
    if (moved < 1.1) { GS[SYAW] += 1.2; if (!GS[MODE]) pickWp(1); }
  }
  const hz = 0.85 + GS[SSPD] * 0.085;
  GS[BEAT] += (hz - GS[BEAT]) * (1 - exp(-dt * 2));
  let wantD = 0, wantV = 0;
  if (!blind && GS[MODE]) {
    const u = clamp((SIGHT - hypot(F[CX] - GS[SX], F[CY] - GS[SY], F[CZ] - GS[SZ])) / (SIGHT - 2.5), 0, 1);
    const shaped = u * (0.28 + 0.72 * u);
    if (GS[MODE] === 1) wantD = wantV = shaped;
    else wantD = shaped * (1 - GS[LOST] / GIVEUP) * 0.7;
  }
  const k = 1 - exp(-dt * 4);
  danger += (wantD - danger) * k; vignette += (wantV - vignette) * k;
  if (!blind && GS[GRACE] <= 0 && reached()) { GS[CAUGHT] = 1; danger = 0; vignette = 1; gameSync(); return 1; }
  gameSync();
  return 0;
}
