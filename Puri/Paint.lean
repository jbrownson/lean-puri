/-
Painting, as a final encoding: a picture is code written against `Paint`, and
each backend is one implementation of it. Coordinates are logical points;
colors are 0xRRGGBBAA.
-/
import Puri.Platform

namespace Puri

structure Paint (m : Type → Type) where
  roundRect : (x y width height radius : Float) → (rgba : UInt32) → m Unit
  text : (x y size : Float) → (rgba : UInt32) → String → m Unit

/-- Painting into a window's frame, through ThorVG. -/
def Platform.Window.paint (w : Platform.Window) : Paint IO where
  roundRect := w.fillRoundRect
  text x y size rgba s := w.fillText x y size rgba s

end Puri
