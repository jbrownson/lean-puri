/-
Drawings, and how they're edited: the output of a list seen through a window
(`Puri/Scroll.lean`). A drawing is a list of rows placed at heights, from the
top. Its edits are the ones a renderer can make cheaply: move every row, move
the rows after one, and enter, leave or change one row. Positions are whole
points, down from the window's top; rows are counted from 0.
-/
import Puri.List

namespace Puri

/-- A row at a height: its top, in points down from the window's top. -/
structure Placed (R : Type) where
  top : Int
  row : R
  deriving DecidableEq, Repr

/-- A placed row moved down by `dy`, or up if `dy` is negative. -/
def Placed.move {R : Type} (p : Placed R) (dy : Int) : Placed R := ⟨p.top + dy, p.row⟩

namespace Drawing

/-- An edit of a drawing. -/
inductive Edit (R : Type) where
  /-- Every row moves down by `dy`, or up if `dy` is negative. -/
  | translate (dy : Int)
  /-- The rows from position `k` on move down by `dy`. -/
  | shift (k : Nat) (dy : Int)
  /-- A placed row enters at position `k`. -/
  | insert (k : Nat) (p : Placed R)
  /-- The row at position `k` leaves. -/
  | delete (k : Nat)
  /-- The row at position `k` becomes `r`, keeping its top. -/
  | update (k : Nat) (r : R)
  deriving Repr

/-- The rows from position `k` on, moved down by `dy`. -/
def shiftFrom {R : Type} (dy : Int) : Nat → List (Placed R) → List (Placed R)
  | 0, ps => ps.map (·.move dy)
  | _ + 1, [] => []
  | k + 1, p :: ps => p :: shiftFrom dy k ps

/-- The row at position `k` replaced by `r`, at the same top. -/
def setRow {R : Type} (r : R) : Nat → List (Placed R) → List (Placed R)
  | _, [] => []
  | 0, p :: ps => ⟨p.top, r⟩ :: ps
  | k + 1, p :: ps => p :: setRow r k ps

/-- The drawing after one edit. -/
def edit {R : Type} : Edit R → List (Placed R) → List (Placed R)
  | .translate dy, ps => ps.map (·.move dy)
  | .shift k dy, ps => shiftFrom dy k ps
  | .insert k p, ps => Puri.insert ps k p
  | .delete k, ps => remove ps k
  | .update k r, ps => setRow r k ps

/-- How drawings are edited, one edit at a time. -/
abbrev editStructure (R : Type) : EditStructure := ⟨List (Placed R), Edit R, edit⟩

/-! ## Getting from any drawing to any other -/

/-- Deletes every row, front first. -/
def clear {R : Type} : List (Placed R) → List (Edit R)
  | [] => []
  | _ :: ps => .delete 0 :: clear ps

/-- Builds `qs` from the empty drawing: its tail, then its head at the
front. -/
def fill {R : Type} : List (Placed R) → List (Edit R)
  | [] => []
  | q :: qs => fill qs ++ [.insert 0 q]

/-- A run that gets from `ps` to `qs`: clear `ps`, then fill with `qs`. This
is redrawing everything, as edits. -/
def diff {R : Type} (ps qs : List (Placed R)) : List (Edit R) :=
  clear ps ++ fill qs

theorem clear_ok {R : Type} (ps : List (Placed R)) : run (editStructure R) (clear ps) ps = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact ih

theorem fill_ok {R : Type} (qs : List (Placed R)) : run (editStructure R) (fill qs) [] = qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    show run (editStructure R) (fill qs ++ [Edit.insert 0 q]) [] = q :: qs
    rw [run_append, ih]
    cases qs <;> rfl

/-- `diff` gets from `ps` to `qs`. -/
theorem diff_ok {R : Type} (ps qs : List (Placed R)) : run (editStructure R) (diff ps qs) ps = qs := by
  show run (editStructure R) (clear ps ++ fill qs) ps = qs
  rw [run_append, clear_ok, fill_ok]

/-- A drawing's change structure: runs of its edits, which get from any
drawing to any other by `diff`. -/
def changeStructure (R : Type) : ChangeStructure :=
  ⟨runs (editStructure R), fun ps qs => ⟨diff ps qs, diff_ok ps qs⟩⟩

end Drawing

end Puri
