import Example

open Puri Puri.Platform Example

/-! A long list in a window, 10,000 items, drawn from the drawing's edits:
each frame renders only the rows that enter, leave or change, and moves the
rest.

- Wheel, arrow keys, Page Up/Down, Home/End: scroll.
- Click an item: open or close it (the items below it shift).
- Return or `n`: insert an item below the one under the pointer.
- Delete, Backspace or `d`: delete the item under the pointer.
- `w`: draw the whole window every frame instead, to compare.
- `a`: scroll by itself, to watch and time frames.
- `q` or Escape: quit.

The title bar and standard output report the work per frame: the time from
the events to the frame being ready to show, not counting the wait for the
display's refresh. -/

structure App where
  view : View
  rows : Rows
  width : Float
  mouse : Float × Float := (0, 0)
  /-- The pointer is in the window. -/
  pointer : Bool := false
  /-- Draw the whole window each frame, instead of rendering edits. -/
  whole : Bool := false
  /-- Points to scroll each frame when scrolling by itself; 0 when not. -/
  auto : Int := 0
  /-- Scrolling not yet made: whole points wait here until the next list
  edit or the end of the events, and fractions of a point until later. -/
  pending : Float := 0
  /-- What the next frame must do: the drawing's edits so far. -/
  edits : List (Drawing.Edit Item) := []
  /-- The rows must be filled again from nothing (after a resize). -/
  refill : Bool := false
  /-- Something changed and the next frame must be drawn. -/
  dirty : Bool := true
  inserted : Nat := 0
  quit : Bool := false

namespace App

/-- Makes a list or scroll edit, keeping the drawing's edits for the next
frame. -/
def edit (app : App) (e : Scroll.Edit items) : App :=
  let (view, ds) := app.view.edit e
  { app with view, edits := app.edits ++ ds, dirty := true }

/-- Makes the whole points of the pending scrolling, cut short at the ends of
the list. -/
def flush (app : App) : App :=
  let whole := app.pending.round
  if whole == 0 then app else
  let app := { app with pending := app.pending - whole }
  let dy := app.view.clamp whole.toInt64.toInt
  if dy == 0 then { app with pending := 0 } else app.edit (.scroll dy)

def scroll (app : App) (dy : Float) : App := { app with pending := app.pending + dy }

def listEdit (app : App) (e : Edit.of items) : App := app.flush.edit (.list e)

/-- The item under the pointer, if any: not when the pointer has left the
window, or is over the scroll bar. -/
def hovered (app : App) : Option Nat :=
  if !app.pointer || app.mouse.1 ≥ app.width - 14 then .none else app.view.rowAt app.mouse.2

/-- Brings the scroll back onto the list if it has fallen off the end: after
the window grows, or the list shrinks while scrolled to its bottom. -/
def settle (app : App) : App :=
  let dy := app.view.clamp 0
  if dy == 0 then app else app.edit (.scroll dy)

def key (app : App) (k : UInt32) (isRepeat : Bool) : App :=
  let page := max 44 (Float.ofInt app.view.height - 44)
  match k with
  | 0x40000051 => app.scroll 44                      -- down
  | 0x40000052 => app.scroll (-44)                   -- up
  | 0x4000004E => app.scroll page                    -- page down
  | 0x4000004B => app.scroll (-page)                 -- page up
  | 0x4000004A => app.scroll (-Float.ofInt app.view.extent.offset - app.pending)  -- home
  | 0x4000004D => app.scroll (Float.ofInt app.view.extent.height)                 -- end
  | 0x0D | 0x6E =>                                   -- return, n
    let pos := (app.hovered.map (· + 1)).getD app.view.z.above.length
    { app with inserted := app.inserted + 1 }.listEdit (.insert pos (fresh (app.inserted + 1)))
  | 0x7F | 0x08 | 0x64 =>                            -- delete, backspace, d
    match app.hovered with
    | .some i => app.listEdit (.delete i)
    | .none => app
  | 0x77 =>                                           -- w
    if isRepeat then app else { app with whole := !app.whole, refill := app.whole, dirty := true }
  | 0x61 =>                                           -- a
    if isRepeat then app else { app with auto := if app.auto == 0 then 6 else 0 }
  | 0x71 | 0x1B => { app with quit := true }                                       -- q, escape
  | _ => app

def event (app : App) : Event → App
  | .quit => { app with quit := true }
  | .move x y => { app with mouse := (x, y), pointer := true }
  | .leave => { app with pointer := false }
  | .down x y 1 =>
    let app := { app with mouse := (x, y), pointer := true }
    match app.hovered with
    | .some i => app.listEdit (.update i .toggle)
    | .none => app
  | .wheel x y _ dy =>
    -- A wheel's notches come as whole numbers; a trackpad's precise
    -- movement comes as fractions, about a tenth of a point each.
    let perUnit : Float := if dy == dy.round then 48 else 10
    { app with mouse := (x, y), pointer := true }.scroll (-dy * perUnit)
  | .keyDown k isRepeat _ => app.key k isRepeat
  | .resized width height =>
    { app with width := width.toNat.toFloat, view := { app.view with height := height.toNat }, refill := true,
               dirty := true }
  | .exposed => { app with dirty := true }
  | _ => app

/-- Scrolls by itself: down, and back up at the ends. -/
def autoStep (app : App) : App :=
  if app.auto == 0 then app else
  let dy := app.view.clamp app.auto
  if dy == 0 then { app with auto := -app.auto } else app.edit (.scroll dy)

/-- Draws the frame: the whole window, or the edits since the last frame. -/
def draw (app : App) (w : Window) : IO App := do
  if app.whole then
    drawWhole w app.width app.view
  else if app.refill then
    fillRows app.rows app.width app.view
  else
    drawEdits app.rows app.width app.view app.edits
  return { app with edits := [], refill := false, dirty := false }

end App

def main : IO Unit := do
  let w ← Window.open "lean-puri" 520 760
  unless (← fontLoad "assets/fonts/Inter-Regular.ttf") do
    IO.eprintln "no font loaded; text won't show (run from the repository's root)"
  let (width, height) ← w.size
  let n := 10000
  let view := View.init ((List.range n).map item) height
  let rows ← Rows.new w background
  let mut app : App := { view, rows, width := width.toFloat, refill := true }
  let mut frames := 0
  let mut work := 0
  let mut since ← IO.monoNanosNow
  repeat
    let events ← w.wait (if app.auto != 0 || app.dirty then 0 else 500)
    let t0 ← IO.monoNanosNow
    app := (events.foldl App.event app).flush.settle.autoStep
    if app.quit then break
    if app.dirty then
      app ← app.draw w
      let t1 ← IO.monoNanosNow
      w.show
      frames := frames + 1
      work := work + (t1 - t0)
    let now ← IO.monoNanosNow
    if now - since ≥ 1000000000 && frames > 0 then
      let ms := (work.toFloat / frames.toFloat) / 1e6
      let mode := if app.whole then "whole window each frame" else "edits"
      let report := s!"{app.view.z.rows.length} items, drawing {mode}: {frames} frames, {ms} ms of work per frame"
      IO.println report
      w.setTitle s!"lean-puri: {report}"
      frames := 0
      work := 0
      since := now
