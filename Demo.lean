import Puri
import Puri.Paint

open Puri Puri.Platform

/-! A first window: cards you click to count, and a button that adds one.
The labels are a mapped list kept up to date with `dmap`'s edits. -/

/-- Numbers that change by "add n". -/
abbrev adds : EditStructure := ⟨Nat, Nat, fun n x => x + n⟩

/-- Strings that change only by being replaced. -/
abbrev texts : EditStructure := whole (none String)

def label (n : Nat) : String :=
  if n == 1 then "clicked once" else s!"clicked {n} times"

/-- A card's label, recomputed whenever its count changes. -/
def labelInc : Inc adds texts := recompute (cb := none String) label

structure Model where
  x : Float := 0
  y : Float := 0
  counts : List Nat
  labels : List String

def Model.edit (m : Model) (es : List (Edit.of adds)) : Model :=
  { m with counts := patch adds es m.counts, labels := patch texts (dmap labelInc es m.counts) m.labels }

def initial : Model :=
  let counts := [0, 0, 0]
  { counts, labels := counts.map label }

/-! Layout, in points. -/

def card (i : Nat) : Float × Float × Float × Float := (24, 72 + i.toFloat * 56, 360, 44)
def addButton : Float × Float × Float × Float := (24, 20, 44, 36)

def inside (r : Float × Float × Float × Float) (x y : Float) : Bool :=
  let (rx, ry, w, h) := r
  rx ≤ x && x < rx + w && ry ≤ y && y < ry + h

def hovered (m : Model) (r : Float × Float × Float × Float) : Bool := inside r m.x m.y

/-! The view, written against `Paint`. -/

def view {m : Type → Type} [Monad m] (p : Paint m) (model : Model) : m Unit := do
  let (ax, ay, aw, ah) := addButton
  p.roundRect ax ay aw ah 8 (if hovered model addButton then 0x3db169ff else 0x2f8f55ff)
  p.text (ax + 14) (ay + 4) 24 0xf0f0f0ff "+"
  p.text 84 26 18 0x9aa4b2ff s!"{model.counts.length} cards"
  for (i, s) in (List.range model.labels.length).zip model.labels do
    let r@(x, y, w, h) := card i
    p.roundRect x y w h 10 (if hovered model r then 0x4c70a6ff else 0x2b3445ff)
    p.text (x + 16) (y + 11) 18 0xe8ecf2ff s

/-! Input: a click on a card counts, a click on + adds a card. -/

def clicked (m : Model) (x y : Float) : List (Edit.of adds) :=
  if inside addButton x y then [.insert m.counts.length 0]
  else match (List.range m.counts.length).find? (fun i => inside (card i) x y) with
    | .some i => [.update i 1]
    | .none => []

def step (m : Model) : Event → Model
  | .move x y => { m with x, y }
  | .down x y 1 => m.edit (clicked m x y)
  | _ => m

def draw (w : Window) (m : Model) : IO Unit := do
  w.beginFrame 0x171b22ff
  view w.paint m
  w.present

def main : IO Unit := do
  let w ← Window.open "lean-puri" 420 360
  unless (← fontLoad "assets/fonts/Inter-Regular.ttf") do
    IO.eprintln "no font loaded; text won't show"
  IO.println s!"pixels per point: {← w.scale}"
  let mut m := initial
  draw w m
  repeat
    let events ← w.wait
    if events.any (fun | .quit => true | _ => false) then break
    m := events.foldl step m
    draw w m
