const DEFAULT_SIZE = 1000; // how many starting numbers (1..size) the tree holds
// The size slider offers the powers of 10 from 10^MIN_POWER to 10^MAX_POWER.
const MIN_POWER = 1;
const MAX_POWER = 5;
const MAX_INPUT = 1000000;

// Tree shape: each step turns a little, depending on whether the number is even or odd.
// A path back to 1 halves about log2(3) ≈ 1.585 times per tripling, so keeping
// ODD_TURN / EVEN_TURN close to that ratio stops the turns from piling up into loops.
// (Exactly 1.585 makes a branch's direction depend only on the size of its number;
// a bit more adds a gentle curl.)
const SEGMENT_LENGTH = 10;
const EVEN_TURN = 0.3803;   // radians, turn right
const ODD_TURN = -0.6452;  // radians, turn left (1.7× the even turn)

// Animation timing (ms).
const APPEAR_MS = 700;
const HOLD_MS = 1800;
const JOURNEY_MS = 7000; // a whole journey aims for roughly this long...
const MIN_STEP_MS = 150;  // ...but each jump stays within these bounds
const MAX_STEP_MS = 350;

const HOVER_RADIUS = 10; // px from a point before its number shows

// Zooming: scroll or pinch to zoom toward the cursor, drag to pan.
const MAX_ZOOM = 40;
const FIT_PAD = 50; // px kept free around the tree when it's fitted to the window

// Bloom mode: the tree grows number by number, from 1 up to the current size.
// The first numbers set off one by one with labels, then the rest follow faster and faster.
const BLOOM_MS = 60000;            // all launches happen within about this long
const BLOOM_LABELLED = 20;         // the first this-many numbers get a label...
const BLOOM_FIRST_GAP_MS = 800;    // ...setting off this far apart at first...
const BLOOM_LAST_GAP_MS = 250;     // ...speeding up to this, where the unlabelled swarm takes over
const BLOOM_APPEAR_MS = 1000;       // labelled numbers pop in for this long before setting off
const BLOOM_LINGER_MS = 300;       // ...and linger at 1 for this long afterwards
const BLOOM_MAX_STEP_MS = 70;      // snappy hops...
const BLOOM_JOURNEY_MS = 1500;     // ...and no journey takes longer than this
const BLOOM_START_ZOOM = 8;        // how close the camera starts on 1
const BLOOM_CAMERA_MS = 500;       // how quickly the camera follows the growth (smoothing)

// Returns the full sequence from n down to 1, e.g. 6 -> [6, 3, 10, 5, 16, 8, 4, 2, 1]
function collatz(n) {
  const seq = [n];
  while (n !== 1) {
    n = n % 2 === 0 ? n / 2 : 3 * n + 1;
    seq.push(n);
  }
  return seq;
}

let nodes = new Map(); // value -> { value, parent, x, y, angle, depth, count, fx, fy }
let treeLayer;         // the tree is drawn into this buffer only when the view changes
let treeDirty = true;  // whether treeLayer needs redrawing
let strokeGroups = []; // branches grouped by colour and thickness, so each group is one canvas path
let anim = null;       // the running animation, if any
let view = { zoom: 1, x: 0, y: 0 }; // zoom and pan on top of the fitted tree
let drag = null;       // the mouse press in progress on the canvas, if any
let treeSize = DEFAULT_SIZE;
let pendingSize = null; // set by the size slider, applied on the next frame
let grownNumbers = new Set(); // numbers searched for that lie outside 1..treeSize
let tracedNumbers = []; // every number whose path built the current tree, in order (the bloom replays these)
let branchColors = []; // colour for each hue step, indexed by node.hueIndex
let bloom = null;      // the running bloom, if any

function setup() {
  const canvas = createCanvas(windowWidth, windowHeight);
  canvas.mousePressed(canvasPressed);
  canvas.elt.addEventListener('wheel', canvasWheel, { passive: false });
  buildTree();
  setupToolbar();
}

function draw() {
  if (pendingSize !== null && !anim && !bloom) {
    treeSize = pendingSize;
    pendingSize = null;
    buildTree();
  }
  if (bloom) updateBloom();
  if (bloom) renderBloomTree();
  else if (treeDirty) renderTree();
  background(17);
  image(treeLayer, 0, 0);
  if (bloom) drawBloomTravellers();
  else if (anim) drawAnimation();
  else drawHover();
}

function buildTree() {
  nodes = new Map();
  nodes.set(1, { value: 1, parent: null, x: 0, y: 0, angle: -HALF_PI, depth: 0, count: 0 });
  tracedNumbers = [];
  for (let n = 1; n <= treeSize; n++) {
    addPath(collatz(n));
  }
  for (const n of grownNumbers) {
    if (!nodes.has(n)) addPath(collatz(n));
  }
  layoutTree();
}

// Walk a sequence backwards from 1. Each value always lands on the same spot,
// so sequences that share an ending share the same branch.
function addPath(seq) {
  tracedNumbers.push(seq[0]);
  const path = [...seq].reverse();
  nodes.get(1).count++;
  for (let i = 1; i < path.length; i++) {
    const value = path[i];
    if (!nodes.has(value)) {
      const parent = nodes.get(path[i - 1]);
      const angle = parent.angle + (value % 2 === 0 ? EVEN_TURN : ODD_TURN);
      nodes.set(value, {
        value,
        parent,
        x: parent.x + cos(angle) * SEGMENT_LENGTH,
        y: parent.y + sin(angle) * SEGMENT_LENGTH,
        angle,
        depth: parent.depth + 1,
        count: 0,
      });
    }
    nodes.get(value).count++;
  }
}

// Places every node on the canvas (fx, fy), before any zooming.
function layoutTree() {
  const all = [...nodes.values()];

  // Turn the whole tree so that, on average, it grows straight up from 1.
  const cx = all.reduce((sum, n) => sum + n.x, 0) / all.length;
  const cy = all.reduce((sum, n) => sum + n.y, 0) / all.length;
  const rotation = -HALF_PI - atan2(cy, cx);
  for (const node of all) {
    node.rx = node.x * cos(rotation) - node.y * sin(rotation);
    node.ry = node.x * sin(rotation) + node.y * cos(rotation);
  }

  const pad = FIT_PAD;
  const minX = min(all.map(n => n.rx)), maxX = max(all.map(n => n.rx));
  const minY = min(all.map(n => n.ry)), maxY = max(all.map(n => n.ry));
  const scale = min((width - 2 * pad) / (maxX - minX), (height - 2 * pad) / (maxY - minY));
  const offsetX = (width - (maxX - minX) * scale) / 2 - minX * scale;
  const offsetY = (height - (maxY - minY) * scale) / 2 - minY * scale;
  for (const node of all) {
    node.fx = offsetX + node.rx * scale;
    node.fy = offsetY + node.ry * scale;
  }

  // Branches: thicker where more numbers pass through, colour shifting with distance from 1.
  // Grouping them by (rounded) colour and thickness lets each group be drawn in a single stroke.
  const maxDepth = max(all.map(n => n.depth));
  const maxCount = nodes.get(1).count;
  if (branchColors.length === 0) {
    for (let i = 0; i <= 64; i++) branchColors.push(branchColor(160 + i * 2.5)); // hues 160..320
  }
  for (const node of all) node.hueIndex = round(map(node.depth, 0, maxDepth, 0, 64));
  strokeGroups = groupBranches(all, node => node.count, maxCount);

  view = { zoom: 1, x: 0, y: 0 };
  treeDirty = true;
}

function branchWeight(count, maxCount) {
  return round(map(sqrt(count), 1, sqrt(maxCount), 1, 8) * 4) / 4;
}

// Buckets branches by colour and thickness (thickness from countOf), thinnest first so the trunk ends up on top.
function groupBranches(branchNodes, countOf, maxCount) {
  const groups = new Map();
  for (const node of branchNodes) {
    if (!node.parent) continue;
    const weight = branchWeight(countOf(node), maxCount);
    const key = node.hueIndex * 100 + weight * 4;
    let group = groups.get(key);
    if (!group) groups.set(key, group = { color: branchColors[node.hueIndex], weight, nodes: [] });
    group.nodes.push(node);
  }
  return [...groups.values()].sort((a, b) => a.weight - b.weight);
}

function branchColor(hue) {
  colorMode(HSB, 360, 100, 100, 100);
  const c = color(hue, 60, 95, 80).toString();
  colorMode(RGB, 255);
  return c;
}

// Draws the part of the tree visible in the current view into treeLayer.
// Lines are drawn at the same on-screen thickness whatever the zoom.
function renderTree() {
  drawGroups(strokeGroups);
  treeDirty = false;
}

function drawGroups(groups) {
  if (!treeLayer || treeLayer.width !== width || treeLayer.height !== height) {
    if (treeLayer) treeLayer.remove();
    treeLayer = createGraphics(width, height);
  }
  treeLayer.clear();

  const ctx = treeLayer.drawingContext;
  ctx.lineCap = 'round';
  for (const group of groups) {
    ctx.strokeStyle = group.color;
    ctx.lineWidth = group.weight;
    ctx.beginPath();
    for (const node of group.nodes) {
      const ax = node.parent.fx * view.zoom + view.x, ay = node.parent.fy * view.zoom + view.y;
      const bx = node.fx * view.zoom + view.x, by = node.fy * view.zoom + view.y;
      if (max(ax, bx) < 0 || min(ax, bx) > width || max(ay, by) < 0 || min(ay, by) > height) continue;
      ctx.moveTo(ax, ay);
      ctx.lineTo(bx, by);
    }
    ctx.stroke();
  }
}

// The canvas fills the window, so the tree is re-fitted whenever the window changes size.
function windowResized() {
  resizeCanvas(windowWidth, windowHeight);
  layoutTree();
}

function toScreen(node) {
  return createVector(node.fx * view.zoom + view.x, node.fy * view.zoom + view.y);
}

// --- Zoom and pan ---------------------------------------------------------

function canvasWheel(event) {
  event.preventDefault(); // don't scroll or zoom the page itself
  if (bloom) return;      // the bloom drives the camera
  const delta = event.deltaMode === 1 ? event.deltaY * 16 : event.deltaY; // Firefox reports lines
  // Trackpad pinches arrive as ctrl+wheel with small deltas, so they get a stronger factor.
  zoomAt(mouseX, mouseY, view.zoom * Math.exp(-delta * (event.ctrlKey ? 0.01 : 0.0015)));
}

// Zooms while keeping the point under (px, py) in place.
function zoomAt(px, py, zoom) {
  zoom = constrain(zoom, 1, MAX_ZOOM);
  const k = zoom / view.zoom;
  view.x = px - (px - view.x) * k;
  view.y = py - (py - view.y) * k;
  view.zoom = zoom;
  viewChanged();
}

function canvasPressed() {
  drag = { startX: mouseX, startY: mouseY, lastX: mouseX, lastY: mouseY, moved: false };
}

function mouseDragged() {
  if (!drag || bloom) return;
  if (!drag.moved && dist(mouseX, mouseY, drag.startX, drag.startY) < 4) return;
  drag.moved = true;
  view.x += mouseX - drag.lastX;
  view.y += mouseY - drag.lastY;
  drag.lastX = mouseX;
  drag.lastY = mouseY;
  viewChanged();
}

// A press that didn't turn into a drag is a click: it sends the point hopping down to 1.
function mouseReleased() {
  if (!drag) return;
  const wasClick = !drag.moved;
  drag = null;
  if (bloom) {
    finishBloom(); // clicking during a bloom skips to the finished tree
    return;
  }
  if (!wasClick || anim) return;
  const node = hoveredNode();
  if (node) startAnimation(node.value);
}

// Keeps the zoomed tree covering the canvas, so it can't be dragged out of sight.
function viewChanged() {
  view.x = constrain(view.x, width * (1 - view.zoom), 0);
  view.y = constrain(view.y, height * (1 - view.zoom), 0);
  treeDirty = true;
}

// --- Toolbar --------------------------------------------------------------

function setupToolbar() {
  for (const tool of document.querySelectorAll('.tool')) {
    if (!tool.querySelector('.panel')) continue; // the flower is just a button
    tool.querySelector('.icon').addEventListener('click', () => openTool(tool));
    // Clicking or tabbing anywhere outside the open panel turns it back into its icon.
    tool.addEventListener('focusout', e => {
      if (!tool.contains(e.relatedTarget)) closeTool(tool);
    });
    tool.addEventListener('keydown', e => {
      if (e.key === 'Escape') closeTool(tool);
    });
  }
  setupSearch();
  setupSizeSlider();
  document.querySelector('#flower-tool .icon').addEventListener('click', e => {
    e.currentTarget.blur();
    startBloom();
  });
}

function openTool(tool) {
  for (const other of document.querySelectorAll('.tool.open')) closeTool(other);
  tool.classList.add('open');
  tool.querySelector('input').focus();
}

function closeTool(tool) {
  if (!tool.classList.contains('open')) return;
  tool.classList.remove('open');
  if (tool.contains(document.activeElement)) document.activeElement.blur();
}

function setupSearch() {
  const tool = document.getElementById('search-tool');
  const input = document.getElementById('number-input');

  input.addEventListener('keydown', e => {
    if (e.key !== 'Enter') return;
    const n = Number(input.value.trim());
    if (!Number.isInteger(n) || n < 1 || n > MAX_INPUT) {
      input.classList.add('invalid');
      setTimeout(() => input.classList.remove('invalid'), 600);
      return;
    }
    input.value = '';
    closeTool(tool);
    startAnimation(n);
  });
}

// Each slider position is a power of 10, with a tick mark above it.
function setupSizeSlider() {
  const slider = document.getElementById('size-slider');
  const label = document.getElementById('size-value');
  const ticks = document.getElementById('size-ticks');

  slider.min = MIN_POWER;
  slider.max = MAX_POWER;
  slider.value = Math.round(Math.log10(treeSize));
  for (let p = MIN_POWER; p <= MAX_POWER; p++) {
    ticks.appendChild(document.createElement('span'));
  }

  const update = () => {
    const power = Number(slider.value);
    label.textContent = 10 ** power;
    ticks.querySelectorAll('span').forEach((tick, i) => {
      tick.classList.toggle('active', i === power - MIN_POWER);
    });
    return 10 ** power;
  };
  update();

  slider.addEventListener('input', () => {
    pendingSize = update();
  });
}

// --- Animation ------------------------------------------------------------

function startAnimation(n) {
  document.getElementById('toolbar').classList.add('hidden');
  cursor(ARROW);
  const seq = collatz(n);
  // A number outside the tree grows a new branch, so the tree gets redrawn to fit it.
  if (!nodes.has(n)) {
    grownNumbers.add(n);
    addPath(seq);
    layoutTree();
  }
  const steps = seq.length - 1;
  anim = {
    path: seq.map(v => nodes.get(v)),
    start: millis(),
    stepMs: constrain(JOURNEY_MS / steps, MIN_STEP_MS, MAX_STEP_MS),
  };
}

function drawAnimation() {
  const { path, stepMs } = anim;
  const steps = path.length - 1;
  const t = millis() - anim.start;
  const travelEnd = APPEAR_MS + steps * stepMs;

  let pos, value, dotScale = 1, alpha = 255, i = 0;

  if (t < APPEAR_MS) {
    // The number pops into view at its spot on the tree.
    const k = t / APPEAR_MS;
    pos = toScreen(path[0]);
    value = path[0].value;
    dotScale = easeOutBack(k);
    alpha = 255 * k;
  } else if (t < travelEnd) {
    // Jump from step to step, with a little hop on each one.
    const k = (t - APPEAR_MS) / stepMs;
    i = floor(k);
    const f = easeInOut(k - i);
    const a = toScreen(path[i]), b = toScreen(path[i + 1]);
    pos = p5.Vector.lerp(a, b, f);
    pos.y -= sin(PI * f) * 8;
    value = path[i].value;
  } else if (t < travelEnd + HOLD_MS) {
    // Rest at 1 for a moment, then fade out.
    const k = (t - travelEnd) / HOLD_MS;
    i = steps;
    pos = toScreen(path[steps]);
    value = 1;
    alpha = 255 * (1 - easeInOut(constrain((k - 0.6) / 0.4, 0, 1)));
  } else {
    anim = null;
    document.getElementById('toolbar').classList.remove('hidden');
    return;
  }

  // Trail of the steps taken so far.
  noFill();
  stroke(255, alpha * 0.6);
  strokeWeight(2);
  beginShape();
  for (let j = 0; j <= i; j++) {
    const p = toScreen(path[j]);
    vertex(p.x, p.y);
  }
  vertex(pos.x, pos.y);
  endShape();

  drawMarker(pos, value, t >= travelEnd ? stepsLabel(steps) : null, alpha, dotScale);
}

// --- Bloom ----------------------------------------------------------------

// Regrows the current tree from nothing. Every node keeps its final position, and its
// branch thickens each time a number passes through it, so the last frame is the normal tree.
function startBloom() {
  document.getElementById('toolbar').classList.add('hidden');
  cursor(ARROW);

  const numbers = tracedNumbers;
  for (const node of nodes.values()) node.bloomCount = 0;
  const one = nodes.get(1);
  bloom = {
    start: millis(),
    lastFrame: millis(),
    numbers,
    next: 0,          // index of the next number to set off
    travellers: [],   // numbers currently on their way to 1
    revealed: [],     // nodes whose branch has appeared
    bounds: { minX: one.fx, maxX: one.fx, minY: one.fy, maxY: one.fy }, // everything grown so far
    camera: { x: one.fx, y: one.fy, zoom: BLOOM_START_ZOOM },
    launches: bloomSchedule(numbers.length),
  };
}

// When each number sets off, in ms after the bloom starts.
function bloomSchedule(count) {
  const times = [];

  // The labelled intro: gaps shrink steadily from BLOOM_FIRST_GAP_MS to BLOOM_LAST_GAP_MS.
  const intro = min(count, BLOOM_LABELLED);
  const ratio = pow(BLOOM_LAST_GAP_MS / BLOOM_FIRST_GAP_MS, 1 / max(BLOOM_LABELLED - 1, 1));
  let t = 0;
  for (let k = 0; k < intro; k++) {
    times.push(t);
    t += BLOOM_FIRST_GAP_MS * pow(ratio, k);
  }

  // The swarm: the remaining numbers on a logarithmic schedule over the time left, i.e.
  // launch j at t + span * log(1 + j/c) / log(1 + (rest-1)/c). c is chosen so the first gap
  // matches the intro's last one, so the pace keeps accelerating without a jolt.
  const rest = count - intro;
  const span = max(BLOOM_MS - t, 0);
  if (rest <= 1 || span / (rest - 1) >= BLOOM_LAST_GAP_MS) {
    for (let j = 0; j < rest; j++) times.push(t + j * BLOOM_LAST_GAP_MS); // too few to need speeding up
    return times;
  }
  const firstGap = c => span * log(1 + 1 / c) / log(1 + (rest - 1) / c); // shrinks as c grows
  let lo = 1e-6, hi = 1e9;
  for (let i = 0; i < 100; i++) {
    const c = sqrt(lo * hi);
    if (firstGap(c) > BLOOM_LAST_GAP_MS) lo = c;
    else hi = c;
  }
  const c = sqrt(lo * hi), scale = log(1 + (rest - 1) / c);
  for (let j = 0; j < rest; j++) times.push(t + span * log(1 + j / c) / scale);
  return times;
}

function updateBloom() {
  const now = millis();
  const t = now - bloom.start;

  // Set off every number whose time has come.
  while (bloom.next < bloom.numbers.length && bloom.launches[bloom.next] <= t) {
    const k = bloom.next++;
    const n = bloom.numbers[k];
    const path = collatz(n).map(v => nodes.get(v));
    const steps = path.length - 1;
    const labelled = k < BLOOM_LABELLED;
    const appear = labelled ? BLOOM_APPEAR_MS : 0;
    const stepMs = min(BLOOM_MAX_STEP_MS, BLOOM_JOURNEY_MS / max(steps, 1));
    const start = bloom.start + bloom.launches[k];
    bloom.travellers.push({
      n, path, labelled, appear, stepMs, start,
      end: start + appear + steps * stepMs + (labelled ? BLOOM_LINGER_MS : 0),
      done: 0, // hops completed
    });
    for (const node of path) growBounds(node);
  }

  // Each completed hop thickens (or first reveals) the branch it just travelled.
  bloom.travellers = bloom.travellers.filter(tr => {
    const steps = tr.path.length - 1;
    const hops = constrain(floor((now - tr.start - tr.appear) / tr.stepMs), 0, steps);
    while (tr.done < hops) {
      const node = tr.path[tr.done++];
      if (node.bloomCount++ === 0) bloom.revealed.push(node);
    }
    return now < tr.end;
  });

  // The camera eases toward a view that fits everything grown so far.
  const b = bloom.bounds, cam = bloom.camera;
  const targetZoom = constrain(
    min((width - 2 * FIT_PAD) / (b.maxX - b.minX), (height - 2 * FIT_PAD) / (b.maxY - b.minY)),
    1, BLOOM_START_ZOOM);
  const targetX = (b.minX + b.maxX) / 2, targetY = (b.minY + b.maxY) / 2;
  const k = 1 - exp(-(now - bloom.lastFrame) / BLOOM_CAMERA_MS);
  bloom.lastFrame = now;
  cam.zoom = exp(lerp(log(cam.zoom), log(targetZoom), k));
  cam.x = lerp(cam.x, targetX, k);
  cam.y = lerp(cam.y, targetY, k);
  view = { zoom: cam.zoom, x: width / 2 - cam.x * cam.zoom, y: height / 2 - cam.y * cam.zoom };

  const settled = abs(cam.zoom - targetZoom) < 0.002 && abs(cam.x - targetX) < 0.5 && abs(cam.y - targetY) < 0.5;
  if (bloom.next === bloom.numbers.length && bloom.travellers.length === 0 && settled) finishBloom();
}

function growBounds(node) {
  const b = bloom.bounds;
  b.minX = min(b.minX, node.fx);
  b.maxX = max(b.maxX, node.fx);
  b.minY = min(b.minY, node.fy);
  b.maxY = max(b.maxY, node.fy);
}

function finishBloom() {
  bloom = null;
  view = { zoom: 1, x: 0, y: 0 };
  treeDirty = true;
  document.getElementById('toolbar').classList.remove('hidden');
}

function keyPressed() {
  if (bloom && keyCode === ESCAPE) finishBloom();
}

// The tree as grown so far, with each branch as thick as the numbers that have passed through it.
function renderBloomTree() {
  drawGroups(groupBranches(bloom.revealed, node => node.bloomCount, nodes.get(1).count));
}

function drawBloomTravellers() {
  const now = millis();

  // The swarm: one small dot per number in flight, drawn in a single batch.
  const ctx = drawingContext;
  ctx.fillStyle = 'rgba(255, 255, 255, 0.75)';
  ctx.beginPath();
  for (const tr of bloom.travellers) {
    if (tr.labelled) continue;
    const p = travellerPosition(tr, now);
    ctx.rect(p.x - 1.5, p.y - 1.5, 3, 3);
  }
  ctx.fill();

  // The first few numbers get the full treatment: a pop, a label and a little hop on each step.
  for (const tr of bloom.travellers) {
    if (!tr.labelled) continue;
    const t = now - tr.start;
    const lingerStart = tr.end - BLOOM_LINGER_MS - tr.start;
    const p = travellerPosition(tr, now);
    const dotScale = t < tr.appear ? easeOutBack(t / tr.appear) : 1;
    const alpha = t < tr.appear ? 255 * t / tr.appear
      : t > lingerStart ? 255 * (1 - (t - lingerStart) / BLOOM_LINGER_MS)
      : 255;

    if (p.from) {
      stroke(255, alpha * 0.6);
      strokeWeight(2);
      line(p.from.x, p.from.y, p.x, p.y);
    }
    drawMarker(p, tr.n, null, alpha, dotScale);
  }
}

// Where a traveller is right now; mid-hop it also reports the point it hopped from.
function travellerPosition(tr, now) {
  const steps = tr.path.length - 1;
  const k = (now - tr.start - tr.appear) / tr.stepMs;
  if (k <= 0 || k >= steps) return toScreen(tr.path[k <= 0 ? 0 : steps]);
  const i = floor(k);
  const f = tr.labelled ? easeInOut(k - i) : k - i;
  const from = toScreen(tr.path[i]);
  const p = p5.Vector.lerp(from, toScreen(tr.path[i + 1]), f);
  if (tr.labelled) p.y -= sin(PI * f) * 6;
  p.from = from;
  return p;
}

// --- Hover ----------------------------------------------------------------

// Shows the number closest to the mouse, if it's close enough.
function drawHover() {
  if (drag?.moved) {
    cursor('grabbing');
    return;
  }
  const node = hoveredNode();
  cursor(node ? HAND : ARROW);
  if (node) drawMarker(toScreen(node), node.value, stepsLabel(node.depth));
}

function hoveredNode() {
  let closest = null;
  let closestDist = HOVER_RADIUS;
  for (const node of nodes.values()) {
    const x = node.fx * view.zoom + view.x, y = node.fy * view.zoom + view.y;
    const d = dist(mouseX, mouseY, x, y);
    if (d < closestDist) {
      closest = node;
      closestDist = d;
    }
  }
  return closest;
}

// A white dot with a number above it and an optional caption below.
function drawMarker(pos, value, caption, alpha = 255, dotScale = 1) {
  noStroke();
  fill(255, alpha);
  circle(pos.x, pos.y, 10 * dotScale);

  textAlign(CENTER, BOTTOM);
  textSize(18);
  stroke(17, alpha);
  strokeWeight(4);
  text(value, pos.x, pos.y - 12);

  if (caption) {
    textSize(12);
    textAlign(CENTER, TOP);
    fill(200, alpha);
    text(caption, pos.x, pos.y + 10);
  }
}

function stepsLabel(steps) {
  return `${steps} step${steps === 1 ? '' : 's'}`;
}

function easeInOut(x) {
  return x < 0.5 ? 2 * x * x : 1 - pow(-2 * x + 2, 2) / 2;
}

function easeOutBack(x) {
  const c = 1.7;
  return 1 + (c + 1) * pow(x - 1, 3) + c * pow(x - 1, 2);
}
