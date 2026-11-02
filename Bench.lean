import Example

open Puri Puri.Platform Example

/-! Measures the incremental view against drawing the whole window, with no
display: the same script of scrolls and edits, one per frame, through both.

- Incremental: `view.df` and `extent.df` give the drawing's edits and the
  extent's, `Scroll.apply` edits the list; the edits are rendered into
  retained rows (only rows that enter or change are drawn), and the rows are
  composited. On a window the GPU composites; here the CPU copies pixels,
  which is timed apart.
- Whole: `Scroll.apply` edits the list (the same anchored list, so finding
  the rows that show is already cheap), the drawing and the extent are
  recomputed, and ThorVG draws the whole window.

Usage: `bench [--frames N] [--rounds N] [--scale S] [--no-check]
[--images DIR] [--sdl] [--callgrind]`. `--sdl` also checks the window code
with SDL's offscreen video driver. With `--callgrind`, run under
`valgrind --tool=callgrind --collect-atstart=no`; each frame's instructions are
dumped, and `scripts/callgrind-summary.py` sums them up. -/

def wide : Nat := 520
def tall : Nat := 760
def listSize : Nat := 10000

structure Opts where
  frames : Nat := 600
  rounds : Nat := 5
  scale : Float := 2
  check : Bool := true
  images : Option String := none
  callgrind : Bool := false
  sdl : Bool := false

partial def Opts.parse (o : Opts) : List String → Opts
  | "--frames" :: n :: t => Opts.parse { o with frames := n.toNat! } t
  | "--rounds" :: n :: t => Opts.parse { o with rounds := n.toNat! } t
  | "--scale" :: s :: t => Opts.parse { o with scale := if s == "1" then 1 else if s == "1.5" then 1.5 else 2 } t
  | "--no-check" :: t => Opts.parse { o with check := false } t
  | "--images" :: d :: t => Opts.parse { o with images := some d } t
  | "--callgrind" :: t => Opts.parse { o with callgrind := true, rounds := 1, check := false } t
  | "--sdl" :: t => Opts.parse { o with sdl := true } t
  | _ :: t => Opts.parse o t
  | [] => o

/-! ## The script -/

inductive Step where
  | scroll (dy : Int)
  | toggle
  | insert
  | delete

/-- One step per frame: scrolling down at 4 to 22 points a frame, as a wheel
or trackpad does, then up at 15, a page down, a jump to the top, and a fling
at 60; every 40 frames, an item in the middle of the window is opened or
closed, an item inserted there, and one deleted. -/
def script (frames : Nat) (H : Int) : Array Step := Id.run do
  let mut s := #[]
  for f in [0:frames] do
    let step :=
      if f % 40 == 10 then .toggle
      else if f % 40 == 20 then .insert
      else if f % 40 == 30 then .delete
      else if f < frames * 5 / 12 then .scroll (4 + (f % 7 : Nat) * 3)
      else if f < frames * 2 / 3 then .scroll (-15)
      else if f == frames * 2 / 3 then .scroll (H - 44)
      else if f == frames * 2 / 3 + 1 then .scroll (-1000000)
      else .scroll 60
    s := s.push step
  return s

def middle (v : View) : Nat := (v.rowAt (Float.ofInt v.height / 2)).getD v.z.above.length

/-- The step as an edit of the view: scrolling cut short at the list's ends. -/
def Step.edit (v : View) (n : Nat) : Step → Scroll.Edit items
  | .scroll dy => .scroll (v.clamp dy)
  | .toggle => .list (.update (middle v) .toggle)
  | .insert => .list (.insert (middle v) (fresh n))
  | .delete => .list (.delete (middle v))

def kind : Scroll.Edit items → String
  | .scroll dy => if dy.natAbs ≥ 300 then "jump" else "scroll"
  | .list _ => "edit"

/-! ## Running -/

/-- One frame's measurements, in nanoseconds. -/
structure Sample where
  kind : String
  lean : Float
  rows : Float := 0
  compose : Float := 0
  draw : Float := 0
  total : Float
  edits : Nat := 0
  drawn : Nat := 0

def startView : View := View.init ((List.range listSize).map item) tall

def ns (a b : UInt64) : Float := (b - a).toNat.toFloat

def runIncremental (o : Opts) (steps : Array Step) : IO (Array Sample) := do
  let w ← Window.offscreen wide.toUInt32 tall.toUInt32 o.scale
  let rows ← Rows.new w background
  let mut v := startView
  fillRows rows wide.toFloat v
  let mut out := #[]
  let mut n := 0
  for s in steps do
    let e := s.edit v n
    if s matches .insert then n := n + 1
    let k := kind e
    let drawn0 ← rows.drawn
    if o.callgrind then callgrindZero
    let t0 ← clockAfter e
    let r := v.edit e
    let t1 ← clockAfter r
    if o.callgrind then callgrindDump s!"incremental lean {k}"; callgrindZero
    let t1' ← IO.monoNanosNow
    Drawing.render rows Item.height (Item.paint wide.toFloat) r.2
    let t2 ← IO.monoNanosNow
    if o.callgrind then callgrindDump s!"incremental rows {k}"; callgrindZero
    let t2' ← IO.monoNanosNow
    let (bx, by_, bw, bh) := r.1.thumb wide.toFloat
    rows.compose bx by_ bw bh barColor
    let t3 ← IO.monoNanosNow
    if o.callgrind then callgrindDump s!"incremental composite {k}"
    v := r.1
    let drawn1 ← rows.drawn
    out := out.push { kind := k, lean := ns t0 t1, rows := ns t1'.toUInt64 t2.toUInt64,
                      compose := ns t2'.toUInt64 t3.toUInt64,
                      total := ns t0 t1 + ns t1'.toUInt64 t2.toUInt64 + ns t2'.toUInt64 t3.toUInt64,
                      edits := r.2.length, drawn := (drawn1 - drawn0).toNat }
  return out

/-- The whole path's model step: the list edited as the incremental path
edits it, and the drawing and extent recomputed. -/
def recompute (v : View) (e : Scroll.Edit items) : View × List (Placed Item) :=
  let z := Scroll.apply items Item.height e v.z
  let v' : View := { v with z, extent := z.extent Item.height }
  (v', v'.drawing)

def runWhole (o : Opts) (steps : Array Step) : IO (Array Sample) := do
  let w ← Window.offscreen wide.toUInt32 tall.toUInt32 o.scale
  let mut v := startView
  drawWhole w wide.toFloat v
  let mut out := #[]
  let mut n := 0
  for s in steps do
    let e := s.edit v n
    if s matches .insert then n := n + 1
    let k := kind e
    if o.callgrind then callgrindZero
    let t0 ← clockAfter e
    let r := recompute v e
    let t1 ← clockAfter r
    if o.callgrind then callgrindDump s!"whole lean {k}"; callgrindZero
    let t1' ← IO.monoNanosNow
    paintWhole w wide.toFloat r.1 r.2
    let t2 ← IO.monoNanosNow
    if o.callgrind then callgrindDump s!"whole draw {k}"
    v := r.1
    out := out.push { kind := k, lean := ns t0 t1, draw := ns t1'.toUInt64 t2.toUInt64,
                      total := ns t0 t1 + ns t1'.toUInt64 t2.toUInt64 }
  return out

/-! ## Checking -/

/-- How far apart, in any channel, two frames' pixels may be. Text's
antialiasing differs by up to 4 levels between a row drawn at its top and one
drawn at 0 and copied there, and by up to 17 on the window's top edge, where
drawing the whole window clips glyphs that a row drawn whole doesn't. A
misplaced or missing row differs by far more. -/
def tolerance : Nat := 24

/-- Runs both paths in step, and checks after every frame that they agree:
the drawing kept by its edits equals the drawing recomputed, the extent kept
by its derivative equals the extent recomputed, the retained rows' tops are
the drawing's, and the two offscreen targets' pixels are the same. -/
def check (o : Opts) (steps : Array Step) : IO Bool := do
  let wi ← Window.offscreen wide.toUInt32 tall.toUInt32 o.scale
  let ww ← Window.offscreen wide.toUInt32 tall.toUInt32 o.scale
  let rows ← Rows.new wi background
  let mut v := startView
  fillRows rows wide.toFloat v
  drawWhole ww wide.toFloat v
  let mut kept := v.drawing
  let mut bad := 0
  let mut pixels := 0
  let mut most := 0
  let mut n := 0
  for (s, f) in steps.zipIdx do
    let e := s.edit v n
    if s matches .insert then n := n + 1
    let (v', ds) := v.edit e
    kept := run (Drawing.editStructure Item) ds kept
    drawEdits rows wide.toFloat v' ds
    let (vw, d) := recompute v e
    paintWhole ww wide.toFloat vw d
    let tops ← rows.tops
    let (diff, far) ← Window.diff wi ww
    pixels := pixels + diff
    most := max most far
    unless kept == d && v'.extent == vw.extent && tops == d.map (·.top) && far ≤ tolerance do
      bad := bad + 1
      if bad ≤ 5 then
        IO.println s!"  frame {f}: drawing {kept == d}, extent {v'.extent == vw.extent}, tops {tops == d.map (·.top)}, {diff} pixels differ by up to {far}"
    if let some dir := o.images then
      if f % 100 == 0 || f == steps.size - 1 || far > tolerance then
        wi.savePPM s!"{dir}/incremental-{f}.ppm"
        ww.savePPM s!"{dir}/whole-{f}.ppm"
    v := v'
  let all := steps.size * (wide * tall).toFloat.toUInt64.toNat * (o.scale * o.scale).toUInt64.toNat
  IO.println s!"check: {steps.size} frames, {bad} disagreeing; drawings, extents and rows' tops equal; {pixels} of {all} pixels differ, by at most {most}/255 in a channel"
  return bad == 0

/-- Checks the window code, the path the demo takes, with SDL's offscreen
video driver and software renderer: rows composited as SDL textures, and the
whole window drawn and uploaded as one, each read back and compared with an
offscreen target drawn the same way, at one pixel per point. -/
def checkSDL (steps : Array Step) : IO Bool := do
  useOffscreenVideo
  let sdl ← Window.open "check" wide.toUInt32 tall.toUInt32
  let (sw, sh) ← sdl.size
  let scale ← sdl.scale
  if sw != wide || sh != tall || scale != 1 then
    IO.println s!"check SDL: the window is {sw}x{sh} points at {scale}, not {wide}x{tall} at 1"
    return false
  let off ← Window.offscreen wide.toUInt32 tall.toUInt32 1
  let sdlRows ← Rows.new sdl background
  let offRows ← Rows.new off background
  let mut v := startView
  fillRows sdlRows wide.toFloat v
  fillRows offRows wide.toFloat v
  let mut bad := 0
  let mut most := 0
  let mut n := 0
  for (s, f) in steps.zipIdx do
    let e := s.edit v n
    if s matches .insert then n := n + 1
    let (v', ds) := v.edit e
    let whole := f % 2 == 1
    drawEdits sdlRows wide.toFloat v' ds
    drawEdits offRows wide.toFloat v' ds
    if whole then
      drawWhole sdl wide.toFloat v'
      drawWhole off wide.toFloat v'
    sdl.readBack
    sdl.show
    let (diff, far) ← Window.diff sdl off
    most := max most far
    if far > 0 then
      bad := bad + 1
      if bad ≤ 5 then IO.println s!"  frame {f} ({if whole then "whole" else "rows"}): {diff} pixels differ by up to {far}"
    v := v'
  IO.println s!"check SDL: {steps.size} frames, rows and whole window alternating: {bad} differing, by at most {most}/255"
  return bad == 0

/-! ## Reporting -/

def sorted (xs : Array Float) : Array Float := xs.qsort (· < ·)

def quantile (q : Float) (xs : Array Float) : Float :=
  let s := sorted xs
  if s.isEmpty then 0 else s[min (s.size - 1) (q * s.size.toFloat).toUInt64.toNat]!

def median (xs : Array Float) : Float := quantile 0.5 xs

/-- `x` with `d` decimals. -/
def fmt (x : Float) (d : Nat := 3) : String :=
  let m := (x * (10 ^ d).toFloat).round.toUInt64.toNat
  let i := m / 10 ^ d
  let f := toString (m % 10 ^ d)
  if d == 0 then toString i else s!"{i}.{"".pushn '0' (d - f.length)}{f}"

def pad (s : String) (n : Nat) : String := s.pushn ' ' (n - s.length)
def padl (s : String) (n : Nat) : String := "".pushn ' ' (n - s.length) ++ s

def row (label : String) (xs : Array Float) : String :=
  let ms (x : Float) := padl (fmt (x / 1e6)) 9
  s!"{pad label 34}{ms (median xs)}{ms (quantile 0.9 xs)}{ms (xs.foldl max 0)}"

def report (name : String) (parts : List (String × (Sample → Float))) (samples : Array Sample) : IO Unit := do
  for k in ["all", "scroll", "jump", "edit"] do
    let ss := if k == "all" then samples else samples.filter (·.kind == k)
    if ss.isEmpty then continue
    IO.println s!"{name}, {k} frames ({ss.size}):"
    for (label, get) in parts do
      IO.println (row s!"  {label}" (ss.map get))

def main (args : List String) : IO UInt32 := do
  let o := Opts.parse {} args
  unless (← fontLoad "assets/fonts/Inter-Regular.ttf") do
    IO.eprintln "no font loaded: run from the repository's root"
    return 1
  let steps := script o.frames tall
  IO.println s!"{listSize} items, {wide}x{tall} points at {o.scale} pixels per point, {o.frames} frames, {o.rounds} rounds"
  if o.check then
    unless (← check o steps) do return 1
  if o.sdl then
    unless (← checkSDL steps) do return 1
  let mut inc := #[]
  let mut whole := #[]
  for _ in [0:o.rounds] do
    inc := inc ++ (← runIncremental o steps)
    whole := whole ++ (← runWhole o steps)
  if o.callgrind || o.rounds == 0 then return 0
  IO.println s!"\n{pad "milliseconds per frame" 34}{padl "median" 9}{padl "p90" 9}{padl "max" 9}"
  report "incremental" [("total", (·.total)), ("total less composite", fun s => s.lean + s.rows),
    ("Lean: view.df, extent.df, apply", (·.lean)), ("rows: render edits", (·.rows)),
    ("rows: composite (CPU here)", (·.compose))] inc
  report "whole" [("total", (·.total)), ("Lean: apply, draw, extent", (·.lean)), ("ThorVG: draw window", (·.draw))] whole
  let sum (f : Sample → Float) := inc.foldl (fun a s => a + f s) 0
  let per (f : Sample → Nat) := sum (fun s => (f s).toFloat) / inc.size.toFloat
  IO.println s!"\nincremental: {fmt (per (·.edits)) 2} drawing edits and {fmt (per (·.drawn)) 2} rows drawn per frame, on average"
  IO.println s!"incremental: rendering edits took {fmt (sum (·.rows) / sum (·.drawn.toFloat) / 1e6)} ms per row drawn"
  IO.println s!"median total, whole / incremental: {fmt (median (whole.map (·.total)) / median (inc.map (·.total))) 1}x"
  return 0
