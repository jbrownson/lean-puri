/-
Rendering a drawing's edits: each edit made to the rows a window retains
(`Platform.Rows`). This is the trusted step between the proved edits and the
pixels: the bridge's rows must do what `Drawing.edit` does to a list, which
`Bench.lean` checks by comparing tops and pixels against drawing whole.
-/
import Puri.Drawing
import Puri.Paint

namespace Puri

open Platform

/-- Makes a drawing edit to the rows `rs`, painting each row that enters or
changes with `paint`, from its top-left corner; `h` gives a row's height. -/
def Drawing.Edit.render {R : Type} (rs : Rows) (h : R → Nat) (paint : Paint IO → R → IO Unit) :
    Drawing.Edit R → IO Unit
  | .translate dy => if dy == 0 then pure () else rs.translate dy.toInt32
  | .shift k dy => if dy == 0 then pure () else rs.shift k.toUInt32 dy.toInt32
  | .insert k p => do
    rs.begin (h p.row).toUInt32
    paint rs.paint p.row
    rs.insert k.toUInt32 p.top.toInt32
  | .delete k => rs.delete k.toUInt32
  | .update k r => do
    rs.begin (h r).toUInt32
    paint rs.paint r
    rs.update k.toUInt32

/-- Makes a run of drawing edits to the rows `rs`. -/
def Drawing.render {R : Type} (rs : Rows) (h : R → Nat) (paint : Paint IO → R → IO Unit)
    (es : List (Drawing.Edit R)) : IO Unit :=
  es.forM (·.render rs h paint)

end Puri
