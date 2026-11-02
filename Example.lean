/-
The example both `Demo.lean` and `Bench.lean` use: a long list of items in a
window, kept as a scrolled list, with its two outputs (the drawing of the
rows that show, and the extent) kept up to date from its edits, and two ways
to put it on screen: rendering the drawing's edits into retained rows, or
drawing the whole window each frame.
-/
import Puri
import Puri.Render

namespace Example

open Puri Puri.Platform

/-! ## Items -/

/-- A row of the list: a title, and lines of detail shown when it is open. -/
structure Item where
  title : String
  details : List String
  isOpen : Bool
  deriving DecidableEq, Repr

/-- An item's edit. -/
inductive Item.Edit where
  /-- Opens a closed item, closes an open one. -/
  | toggle

def Item.Edit.apply : Item.Edit → Item → Item
  | .toggle, it => { it with isOpen := !it.isOpen }

abbrev items : EditStructure := ⟨Item, Item.Edit, Item.Edit.apply⟩

/-- An item's height in points: a line for the title, and a line for each
detail when it is open. -/
def Item.height (it : Item) : Nat :=
  if it.isOpen then 44 + 22 * it.details.length + 8 else 44

def background : UInt32 := 0x171b22ff
def barColor : UInt32 := 0x5a6475ff

/-- Paints an item from its top-left corner, in a window `width` points
wide. -/
def Item.paint {m : Type → Type} [Monad m] (width : Float) (p : Paint m) (it : Item) : m Unit := do
  let h := it.height.toFloat
  p.roundRect 12 3 (width - 40) (h - 6) 8 (if it.isOpen then 0x2d3b55ff else 0x252c38ff)
  p.text 26 12 17 0xe8ecf2ff it.title
  if it.isOpen then
    let mut y : Float := 44
    for line in it.details do
      p.text 42 y 15 0x9aa4b2ff line
      y := y + 22

def words : Array String := #[
  "amber", "basalt", "cedar", "delta", "ember", "fjord", "garnet", "harbor", "indigo", "juniper",
  "kelp", "lantern", "meadow", "nimbus", "orchid", "pebble", "quartz", "river", "saffron", "tundra",
  "umber", "velvet", "willow", "xenon", "yarrow", "zephyr", "anchor", "bramble", "cobalt", "dune",
  "estuary", "fennel", "glacier", "heron", "iris", "jasper", "kestrel", "lichen", "marble", "nettle"]

/-- The `i`th item of the example list, made up from `words`. -/
def item (i : Nat) : Item :=
  let pick (k : Nat) := words[(i * 7919 + k * 104729 + k * k * 31) % words.size]!
  { title := s!"{i + 1}. {pick 1} {pick 2} {pick 3}"
    details := (List.range (1 + i % 4)).map fun j => s!"{pick (j + 4)} {pick (j + 5)} {pick (j + 6)} {pick (j + 7)}"
    isOpen := i % 9 == 4 }

/-- A new item, for inserting. -/
def fresh (n : Nat) : Item :=
  { title := s!"new item {n}", details := ["inserted with Return", "deleted with Delete"], isOpen := false }

/-! ## The view -/

/-- The list in a window `height` points tall, scrolled, with its extent
kept up to date. `z` is kept normalized: every edit normalizes. -/
structure View where
  z : Scroll Item
  extent : Extent
  height : Int

def View.init (its : List Item) (height : Int) : View :=
  let z := Scroll.normalize Item.height ⟨[], its, 0⟩
  { z, extent := z.extent Item.height, height }

/-- What shows, recomputed. -/
def View.drawing (v : View) : List (Placed Item) := Scroll.draw Item.height v.height v.z

/-- Makes an edit: the edited view, and the drawing's edits, from the
derivatives `view.df` and `extent.df`, whose laws `view_ok` and `extent_ok`
say they are right. -/
def View.edit (v : View) (e : Scroll.Edit items) : View × List (Drawing.Edit Item) :=
  let ds := view.df items Item.height v.height v.z e
  let x := Extent.edits.apply (extent.df items Item.height v.z e) v.extent
  ({ v with z := Scroll.apply items Item.height e v.z, extent := x }, ds)

/-- Makes a run of edits, joining their drawing edits. -/
def View.edits (v : View) (es : List (Scroll.Edit items)) : View × List (Drawing.Edit Item) :=
  es.foldl (fun (v, ds) e => let (v', ds') := v.edit e; (v', ds ++ ds')) (v, [])

/-- `dy`, cut short so the window stays on the list: the list's top no lower
than the window's top, and its bottom no higher than the window's bottom,
unless the list is shorter than the window. Uses only the extent. -/
def View.clamp (v : View) (dy : Int) : Int :=
  let most := max 0 (v.extent.height - v.height)
  let off := min most (max 0 (v.extent.offset + dy))
  off - v.extent.offset

/-- The scroll bar's thumb, at the window's right edge `width` points wide,
in whole points: x, y, width, height. Its height is 0 if the list fits. -/
def View.thumb (v : View) (width : Float) : Float × Float × Float × Float :=
  let total := v.extent.height
  if total ≤ v.height then (width - 10, 0, 6, 0) else
  let th := max 24 (v.height * v.height / total)
  let ty := (v.extent.offset * (v.height - th)) / max 1 (total - v.height)
  (width - 10, Float.ofInt ty, 6, Float.ofInt th)

/-- The position in the list of the row at `y` points down the window, if
any. It walks from the anchor (the first row that shows), and counts the
rows above it. -/
def View.rowAt (v : View) (y : Float) : Option Nat :=
  let rec go (top : Int) (k : Nat) : List Item → Option Nat
    | [] => none
    | r :: rs =>
      let bottom := top + r.height
      if y < Float.ofInt bottom then (if Float.ofInt top ≤ y then some k else none)
      else if top ≥ v.height then none
      else go bottom (k + 1) rs
  (go (-v.z.off) 0 v.z.rest).map (v.z.above.length + ·)

/-! ## On screen -/

/-- Draws the whole window: the rows of drawing `d`, and the scroll bar. -/
def paintWhole (w : Window) (width : Float) (v : View) (d : List (Placed Item)) : IO Unit := do
  w.beginFrame background
  for p in d do
    Item.paint width (w.paint.down (Float.ofInt p.top)) p.row
  let (bx, by_, bw, bh) := v.thumb width
  if bh > 0 then w.fillRoundRect bx by_ bw bh 0 barColor
  w.endFrame

/-- Draws the whole window: every row that shows, and the scroll bar. -/
def drawWhole (w : Window) (width : Float) (v : View) : IO Unit :=
  paintWhole w width v v.drawing

/-- Makes the drawing's edits to the retained rows, and composites them with
the scroll bar. -/
def drawEdits (rs : Rows) (width : Float) (v : View) (ds : List (Drawing.Edit Item)) : IO Unit := do
  Drawing.render rs Item.height (Item.paint width) ds
  let (bx, by_, bw, bh) := v.thumb width
  rs.compose bx by_ bw bh barColor

/-- Fills retained rows from nothing with what shows: the edits that build
the drawing from the empty one. -/
def fillRows (rs : Rows) (width : Float) (v : View) : IO Unit := do
  rs.clear
  drawEdits rs width v (Drawing.diff [] v.drawing)

end Example
