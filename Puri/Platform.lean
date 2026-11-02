/-
The platform: an SDL3 window that ThorVG draws into (native/platform.c).
Coordinates are logical points; the bridge scales drawing to the window's
pixel density. Events cross the bridge as flat words and are decoded here.
-/

namespace Puri.Platform

opaque WindowPointed : NonemptyType
def Window : Type := WindowPointed.type
instance : Nonempty Window := WindowPointed.property

@[extern "puri_window_open"]
opaque Window.open (title : @& String) (width height : UInt32) : IO Window

/-- Pixels per point: 2 on a 2x display. -/
@[extern "puri_window_scale"]
opaque Window.scale (w : @& Window) : IO Float

@[extern "puri_window_wait"]
opaque Window.waitWords (w : @& Window) (timeoutMs : Int32) : IO (Array UInt32)

@[extern "puri_frame_begin"]
opaque Window.beginFrame (w : @& Window) (background : UInt32) : IO Unit

@[extern "puri_fill_round_rect"]
opaque Window.fillRoundRect (w : @& Window) (x y width height radius : Float) (rgba : UInt32) : IO Unit

@[extern "puri_fill_text"]
opaque Window.fillText (w : @& Window) (x y size : Float) (rgba : UInt32) (text : @& String) : IO Unit

@[extern "puri_frame_present"]
opaque Window.present (w : @& Window) : IO Unit

@[extern "puri_font_load"]
opaque fontLoad (path : @& String) : IO Bool

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
