/-
The platform: an SDL3 window that ThorVG draws into (native/platform.c), or
an offscreen target with the same drawing and no display. Coordinates are
logical points; the bridge scales drawing to the window's pixel density.
Events cross the bridge as flat words and are decoded here.
-/

namespace Puri.Platform

opaque WindowPointed : NonemptyType
def Window : Type := WindowPointed.type
instance : Nonempty Window := WindowPointed.property

@[extern "puri_window_open"]
opaque Window.open (title : @& String) (width height : UInt32) : IO Window

/-- A target with no display, `width` by `height` points at `scale` pixels
per point, for measuring and checking without a window. -/
@[extern "puri_offscreen_open"]
opaque Window.offscreen (width height : UInt32) (scale : Float) : IO Window

/-- Pixels per point: 2 on a 2x display. -/
@[extern "puri_window_scale"]
opaque Window.scale (w : @& Window) : IO Float

@[extern "puri_window_size"]
private opaque Window.sizeWord (w : @& Window) : IO UInt64

/-- The window's width and height, in points. -/
def Window.size (w : Window) : IO (Nat × Nat) := do
  let s ← w.sizeWord
  return ((s >>> 32).toNat, (s &&& 0xffffffff).toNat)

@[extern "puri_window_set_title"]
opaque Window.setTitle (w : @& Window) (title : @& String) : IO Unit

@[extern "puri_window_wait"]
opaque Window.waitWords (w : @& Window) (timeoutMs : Int32) : IO (Array UInt32)

/-! ## Drawing a frame: everything, each time -/

@[extern "puri_frame_begin"]
opaque Window.beginFrame (w : @& Window) (background : UInt32) : IO Unit

@[extern "puri_fill_round_rect"]
opaque Window.fillRoundRect (w : @& Window) (x y width height radius : Float) (rgba : UInt32) : IO Unit

@[extern "puri_fill_text"]
opaque Window.fillText (w : @& Window) (x y size : Float) (rgba : UInt32) (text : @& String) : IO Unit

/-- Draws the frame, ready to show. -/
@[extern "puri_frame_end"]
opaque Window.endFrame (w : @& Window) : IO Unit

/-- Shows what was drawn, waiting for the display's next refresh. -/
@[extern "puri_window_show"]
opaque Window.show (w : @& Window) : IO Unit

def Window.present (w : Window) : IO Unit := do
  w.endFrame
  w.show

@[extern "puri_font_load"]
opaque fontLoad (path : @& String) : IO Bool

/-! ## Rows: drawn once, then moved

A window's retained rows, each drawn into its own pixels when it enters or
changes. The operations are a drawing's edits (`Puri/Drawing.lean`); a row
is painted between `begin` and the `insert` or `update` that places it.
Positions and tops are as in a drawing: rows counted from 0, tops in points
down from the window's top. -/

opaque RowsPointed : NonemptyType
def Rows : Type := RowsPointed.type
instance : Nonempty Rows := RowsPointed.property

/-- Rows shown in `w`, on a background of `background`. -/
@[extern "puri_rows_new"]
opaque Rows.new (w : @& Window) (background : UInt32) : IO Rows

/-- Starts painting a row `height` points tall. -/
@[extern "puri_rows_begin"]
opaque Rows.begin (rs : @& Rows) (height : UInt32) : IO Unit

@[extern "puri_rows_fill_round_rect"]
opaque Rows.fillRoundRect (rs : @& Rows) (x y width height radius : Float) (rgba : UInt32) : IO Unit

@[extern "puri_rows_fill_text"]
opaque Rows.fillText (rs : @& Rows) (x y size : Float) (rgba : UInt32) (text : @& String) : IO Unit

/-- The row just painted enters at position `k`, with its top at `top`. -/
@[extern "puri_rows_insert"]
opaque Rows.insert (rs : @& Rows) (k : UInt32) (top : Int32) : IO Unit

/-- The row at position `k` becomes the row just painted, keeping its top. -/
@[extern "puri_rows_update"]
opaque Rows.update (rs : @& Rows) (k : UInt32) : IO Unit

/-- The row at position `k` leaves. -/
@[extern "puri_rows_delete"]
opaque Rows.delete (rs : @& Rows) (k : UInt32) : IO Unit

/-- The rows from position `k` on move down by `dy`. -/
@[extern "puri_rows_shift"]
opaque Rows.shift (rs : @& Rows) (k : UInt32) (dy : Int32) : IO Unit

/-- Every row moves down by `dy`. -/
@[extern "puri_rows_translate"]
opaque Rows.translate (rs : @& Rows) (dy : Int32) : IO Unit

/-- Every row leaves. -/
@[extern "puri_rows_clear"]
opaque Rows.clear (rs : @& Rows) : IO Unit

/-- Composites the rows, and a bar over them (`x y width height` in points),
ready to show with `Window.show`. -/
@[extern "puri_rows_compose"]
opaque Rows.compose (rs : @& Rows) (x y width height : Float) (bar : UInt32) : IO Unit

@[extern "puri_rows_tops"]
private opaque Rows.topWords (rs : @& Rows) : IO (Array UInt32)

/-- The rows' tops, for checking them against a drawing. -/
def Rows.tops (rs : Rows) : IO (List Int) := do
  return (← rs.topWords).toList.map (·.toInt32.toInt)

/-- How many rows have been drawn into pixels so far. -/
@[extern "puri_rows_drawn"]
opaque Rows.drawn (rs : @& Rows) : IO UInt64

/-! ## Checking and measuring -/

@[extern "puri_window_diff"]
private opaque Window.diffWord (a b : @& Window) : IO UInt64

/-- How two offscreen targets' last frames differ: how many pixels differ,
and the largest difference in any channel (0 to 255). -/
def Window.diff (a b : Window) : IO (Nat × Nat) := do
  let d ← Window.diffWord a b
  return ((d &&& 0xffffffffffffff).toNat, (d >>> 56).toNat)

/-- Makes the next window use SDL's offscreen video driver and software
renderer: a window with no display, for checking the window code. -/
@[extern "puri_use_offscreen_video"]
opaque useOffscreenVideo : IO Unit

/-- Reads back what a window's renderer holds, before `show`, so `diff` can
compare it. -/
@[extern "puri_window_read_back"]
opaque Window.readBack (w : @& Window) : IO Unit

/-- Writes an offscreen target's last frame as a PPM image. -/
@[extern "puri_window_save_ppm"]
opaque Window.savePPM (w : @& Window) (path : @& String) : IO Unit

/-- The monotonic clock, in nanoseconds, read after `x` is computed. -/
@[extern "puri_clock_after"]
opaque clockAfter {α : Type} (x : @& α) : IO UInt64

/-- Under callgrind, zeroes its counts; otherwise does nothing. -/
@[extern "puri_callgrind_zero"]
opaque callgrindZero : IO Unit

/-- Under callgrind, dumps its counts since the last zero as a part named
`name`; otherwise does nothing. -/
@[extern "puri_callgrind_dump"]
opaque callgrindDump (name : @& String) : IO Unit

/-! ## Events -/

inductive Event where
  | quit
  | move (x y : Float)
  | down (x y : Float) (button : UInt32)
  | up (x y : Float) (button : UInt32)
  | keyDown (key : UInt32) (isRepeat : Bool) (mods : UInt32)
  | keyUp (key : UInt32) (mods : UInt32)
  | text (s : String)
  | resized (width height : UInt32)
  | wheel (x y dx dy : Float)
  | exposed
  deriving Repr

private def float (u : UInt32) : Float := (Float32.ofBits u).toFloat

/-- The UTF-8 bytes packed four per word after a text event's header. -/
private def bytes (ws : Array UInt32) (start n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for i in [0:n] do
    let w := ws[start + i / 4]!
    b := b.push (w >>> (8 * (i % 4)).toUInt32).toUInt8
  return b

/-- Decodes the bridge's words: five per event, then a text event's bytes. -/
partial def decode (ws : Array UInt32) (i : Nat := 0) (acc : Array Event := #[]) : Array Event :=
  if i + 5 > ws.size then acc else
  let a := ws[i+1]!; let b := ws[i+2]!; let c := ws[i+3]!; let d := ws[i+4]!
  match ws[i]! with
  | 1 => decode ws (i+5) (acc.push .quit)
  | 2 => decode ws (i+5) (acc.push (.move (float a) (float b)))
  | 3 => decode ws (i+5) (acc.push (.down (float a) (float b) c))
  | 4 => decode ws (i+5) (acc.push (.up (float a) (float b) c))
  | 5 => decode ws (i+5) (acc.push (.keyDown a (b != 0) c))
  | 6 => decode ws (i+5) (acc.push (.keyUp a c))
  | 7 =>
    let n := a.toNat
    let s := String.fromUTF8? (bytes ws (i+5) n) |>.getD ""
    decode ws (i + 5 + (n + 3) / 4) (acc.push (.text s))
  | 8 => decode ws (i+5) (acc.push (.resized a b))
  | 9 => decode ws (i+5) (acc.push (.wheel (float a) (float b) (float c) (float d)))
  | 10 => decode ws (i+5) (acc.push .exposed)
  | _ => decode ws (i+5) acc

/-- Waits for events, `timeoutMs` at most (negative: no deadline). -/
def Window.wait (w : Window) (timeoutMs : Int32 := -1) : IO (Array Event) :=
  return decode (← w.waitWords timeoutMs)

end Puri.Platform
