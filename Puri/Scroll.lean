/-
A long list seen through a window: the rows that show, kept up to date from
the list's edits and the scroll instead of being placed and drawn again.
Positions are whole points, down from the window's top.

The list is held split at its anchor, the first row that shows, so scrolling
touches only the rows that enter or leave, and positions are worked out only
for the rows that show. Edits outside the window don't move what shows: a
row inserted above the anchor moves the scroll offset down with it, as
browsers' scroll anchoring does.

Two outputs are kept up to date, each an `Inc` with its law: `view`, the
drawing of the rows that show (`Puri/Drawing.lean`), and `extent`, how far
the list is scrolled and how tall it is, which is what a scroll bar shows.
The laws are at the end of the file.
-/
import Puri.Drawing

namespace Puri

/-! ## Placing rows -/

section
variable {R : Type} (h : R → Nat) (H : Int)

/-- The rows' heights, added up. -/
def height : List R → Nat
  | [] => 0
  | r :: rs => h r + height rs

/-- Rows one under another, the first with its top at `y`; `h` gives each
row's height. -/
def place (y : Int) : List R → List (Placed R)
  | [] => []
  | r :: rs => ⟨y, r⟩ :: place (y + h r) rs

/-- Rows placed as `place` places them, from the first, while they start
above the bottom of a window of height `H`. -/
def window (y : Int) : List R → List (Placed R)
  | [] => []
  | r :: rs => if y < H then ⟨y, r⟩ :: window (y + h r) rs else []

/-- How many rows `window` places, without placing them. -/
def count (y : Int) : List R → Nat
  | [] => 0
  | r :: rs => if y < H then count (y + h r) rs + 1 else 0

/-- A placed row shows in a window of height `H` if it ends below the
window's top and starts above its bottom. -/
def shows (p : Placed R) : Bool := 0 < p.top + h p.row && p.top < H

end

/-! ## A scrolled list -/

/-- A list in a window, scrolled. Its anchor is a row near the window's top
(normally the first that shows): `rest` is the anchor and the rows after it,
`above` the rows before it, nearest first, and `off` how far the anchor's
top is above the window's top. -/
structure Scroll (R : Type) where
  above : List R
  rest : List R
  off : Int

namespace Scroll

variable {R : Type}

/-- The list. -/
def rows (z : Scroll R) : List R := z.above.reverse ++ z.rest

/-- How far the list's top is above the window's top. -/
def offset (h : R → Nat) (z : Scroll R) : Int := height h z.above + z.off

/-- The row at position `i` of the list, found from the anchor. -/
def get? (z : Scroll R) (i : Nat) : Option R :=
  let a := z.above.length
  if i < a then z.above[a - 1 - i]? else z.rest[i - a]?

/-- Moves the anchor down past the rows that end above the window's top. -/
def push (h : R → Nat) (above : List R) : List R → Int → Scroll R
  | [], off => ⟨above, [], off⟩
  | r :: rs, off => if (h r : Int) ≤ off then push h (r :: above) rs (off - h r) else ⟨above, r :: rs, off⟩

/-- Moves the anchor up while its top is below the window's top. -/
def pull (h : R → Nat) (rest : List R) : List R → Int → Scroll R
  | [], off => ⟨[], rest, off⟩
  | r :: above, off => if off < 0 then pull h (r :: rest) above (off + h r) else ⟨r :: above, rest, off⟩

/-- The anchor moved to the first row that shows: the row the window's top
falls in, or the first row if the window's top is above the list, or past
the end if it is below. -/
def normalize (h : R → Nat) (z : Scroll R) : Scroll R :=
  if z.off < 0 then pull h z.rest z.above z.off else push h z.above z.rest z.off

/-- What shows in a window of height `H`: the rows from the anchor, once
normalized, placed from its top. -/
def draw (h : R → Nat) (H : Int) (z : Scroll R) : List (Placed R) :=
  let n := normalize h z
  window h H (-n.off) n.rest

/-- An edit of a scrolled list: an edit of the list, or scrolling down by
`dy` points (up, if negative). -/
inductive Edit (ca : EditStructure) where
  | list (e : Puri.Edit.of ca)
  | scroll (dy : Int)

/-- A list edit, made where its position falls: in `above`, counted from the
anchor up, if it is before the anchor, else in `rest`. -/
def edit (ca : EditStructure) : Puri.Edit.of ca → Scroll ca.Value → Scroll ca.Value
  | .insert i x, ⟨above, rest, off⟩ =>
    let a := above.length
    if i < a then ⟨Puri.insert above (a - i) x, rest, off⟩ else ⟨above, Puri.insert rest (i - a) x, off⟩
  | .delete i, ⟨above, rest, off⟩ =>
    let a := above.length
    if i < a then ⟨remove above (a - 1 - i), rest, off⟩ else ⟨above, remove rest (i - a), off⟩
  | .update i d, ⟨above, rest, off⟩ =>
    let a := above.length
    if i < a then ⟨update ca above (a - 1 - i) d, rest, off⟩ else ⟨above, update ca rest (i - a) d, off⟩

/-- An edit made, without normalizing. -/
def step (ca : EditStructure) : Edit ca → Scroll ca.Value → Scroll ca.Value
  | .list e, z => edit ca e z
  | .scroll dy, z => { z with off := z.off + dy }

/-- An edit applied: made to the normalized list, then normalized again. -/
def apply (ca : EditStructure) (h : ca.Value → Nat) (e : Edit ca) (z : Scroll ca.Value) : Scroll ca.Value :=
  normalize h (step ca e (normalize h z))

/-- How a scrolled list is edited, one edit at a time. -/
abbrev editStructure (ca : EditStructure) (h : ca.Value → Nat) : EditStructure :=
  ⟨Scroll ca.Value, Edit ca, apply ca h⟩

end Scroll

/-! ## The view's derivative -/

namespace view

section
variable {R : Type} (h : R → Nat) (H : Int)

/-- Deletes, at position `k`, as many rows as the first `m` of `rs`. -/
def dropAll (k : Nat) : Nat → List R → List (Drawing.Edit R)
  | 0, _ => []
  | _ + 1, [] => []
  | m + 1, _ :: rs => .delete k :: dropAll k m rs

/-- The edits from what the drawing holds at position `k` on to
`window h H y rs`, when it holds the `m` rows of `rs` that follow the first
`p`, placed as they are in `rs` from `y`. The first `p` rows are new: each
enters while it starts above the window's bottom. The drawn rows that now
start below the bottom leave, and the rows after them that start above it
enter. -/
def fit (k : Nat) (y : Int) : Nat → Nat → List R → List (Drawing.Edit R)
  | _, _, [] => []
  | p + 1, m, r :: rs => if y < H then .insert k ⟨y, r⟩ :: fit (k + 1) (y + h r) p m rs else dropAll k m (rs.drop p)
  | 0, 0, r :: rs => if y < H then .insert k ⟨y, r⟩ :: fit (k + 1) (y + h r) 0 0 rs else []
  | 0, m + 1, r :: rs => if y < H then fit (k + 1) (y + h r) 0 m rs else dropAll k (m + 1) (r :: rs)

/-- `Scroll.push`'s edits, from the first `m` of `rest` placed from `-off`:
each row it moves above leaves the top. -/
def push (m : Nat) : List R → Int → List (Drawing.Edit R)
  | [], _ => []
  | r :: rs, off =>
    if (h r : Int) ≤ off then (if m = 0 then [] else [.delete 0]) ++ push (m - 1) rs (off - h r)
    else fit h H 0 (-off) 0 m (r :: rs)

/-- `Scroll.pull`'s edits: it counts the rows it moves back, `p`, and `fit`
enters those that show at the top. -/
def pull (p m : Nat) (rest : List R) : List R → Int → List (Drawing.Edit R)
  | [], off => fit h H 0 (-off) p m rest
  | r :: above, off =>
    if off < 0 then pull (p + 1) m (r :: rest) above (off + h r)
    else fit h H 0 (-off) p m rest

/-- From the first `m` rows of `z.rest` placed from `-z.off`, to `z`'s
drawing: normalizing's edits, then `fit`'s. -/
def settle (m : Nat) (z : Scroll R) : List (Drawing.Edit R) :=
  if z.off < 0 then pull h H 0 m z.rest z.above z.off else push h H m z.rest z.off

end

/-- An edit's own effect on the first `m` rows of a normal `n`, placed: the
drawing edits, and how many rows of the edited list they leave placed.
Scrolling translates; a list edit at a placed row places it, and shifts the
rows after it by the change in height; any other edit leaves them. -/
def core (ca : EditStructure) (h : ca.Value → Nat) (n : Scroll ca.Value) (m : Nat) :
    Scroll.Edit ca → List (Drawing.Edit ca.Value) × Nat
  | .scroll dy => ([.translate (-dy)], m)
  | .list (.insert i x) =>
    let a := n.above.length
    if a ≤ i ∧ i - a < m then
      ([.insert (i - a) ⟨-n.off + height h (n.rest.take (i - a)), x⟩, .shift (i - a + 1) (h x)], m + 1)
    else ([], m)
  | .list (.delete i) =>
    let a := n.above.length
    if a ≤ i ∧ i - a < m then
      match n.rest[i - a]? with
      | .some x => ([.delete (i - a), .shift (i - a) (-(h x : Int))], m - 1)
      | .none => ([], m)
    else ([], m)
  | .list (.update i d) =>
    let a := n.above.length
    if a ≤ i ∧ i - a < m then
      match n.rest[i - a]? with
      | .some x => ([.update (i - a) (ca.apply d x), .shift (i - a + 1) ((h (ca.apply d x) : Int) - h x)], m)
      | .none => ([], m)
    else ([], m)

/-- The view's derivative: the edit's own effect on what shows, then the
rows that enter or leave. -/
def df (ca : EditStructure) (h : ca.Value → Nat) (H : Int) (z : Scroll ca.Value) (e : Scroll.Edit ca) :
    List (Drawing.Edit ca.Value) :=
  let n := Scroll.normalize h z
  let c := core ca h n (count h H (-n.off) n.rest) e
  c.1 ++ settle h H c.2 (Scroll.step ca e n)

end view

/-- The view of a scrolled list in a window of height `H`: what shows, as an
incremental function of the list's edits and the scroll. -/
def view (ca : EditStructure) (h : ca.Value → Nat) (H : Int) :
    Inc (Scroll.editStructure ca h) (runs (Drawing.editStructure ca.Value)) :=
  ⟨Scroll.draw h H, view.df ca h H⟩

/-- The lifted view, whose derivative takes runs of edits. -/
def view.inc (ca : EditStructure) (h : ca.Value → Nat) (H : Int) :
    Inc (runs (Scroll.editStructure ca h)) (runs (Drawing.editStructure ca.Value)) :=
  lift (view ca h H)

/-! ## The extent -/

/-- What a scroll bar shows: how far the list's top is above the window's
top, and how tall the list is, in points. -/
structure Extent where
  offset : Int
  height : Int
  deriving DecidableEq, Repr

/-- An extent's edit: amounts added to its offset and its height. -/
abbrev Extent.edits : EditStructure :=
  ⟨Extent, Int × Int, fun d x => ⟨x.offset + d.1, x.height + d.2⟩⟩

/-- Where a list edit acts. -/
def Edit.pos {A DA : Type} : Edit A DA → Nat
  | .insert i _ => i
  | .delete i => i
  | .update i _ => i

/-- How much taller a list edit makes the list of `n` (shorter, if
negative): an insert adds its row's height, a delete takes away the deleted
row's, and an update adds the change in its row's. -/
def grows (ca : EditStructure) (h : ca.Value → Nat) (n : Scroll ca.Value) : Edit.of ca → Int
  | .insert _ x => h x
  | .delete i =>
    match n.get? i with
    | .some x => -(h x : Int)
    | .none => 0
  | .update i d =>
    match n.get? i with
    | .some x => (h (ca.apply d x) : Int) - h x
    | .none => 0

/-- The extent of a scrolled list. -/
def Scroll.extent {R : Type} (h : R → Nat) (z : Scroll R) : Extent :=
  ⟨z.offset h, height h z.rows⟩

/-- The extent's derivative. Scrolling moves the offset. A list edit grows
the list, and moves the offset too if it is before the anchor, so that what
shows stays put. -/
def extent.df (ca : EditStructure) (h : ca.Value → Nat) (z : Scroll ca.Value) : Scroll.Edit ca → Int × Int
  | .scroll dy => (dy, 0)
  | .list e =>
    let n := Scroll.normalize h z
    let g := grows ca h n e
    (if e.pos < n.above.length then g else 0, g)

/-- The extent, as an incremental function of the list's edits and the
scroll. -/
def extent (ca : EditStructure) (h : ca.Value → Nat) : Inc (Scroll.editStructure ca h) Extent.edits :=
  ⟨Scroll.extent h, extent.df ca h⟩

/-! ## Proof steps: list edits by position -/

section
variable {A : Type}

theorem insert_zero (xs : List A) (x : A) : insert xs 0 x = x :: xs := by
  cases xs <;> rfl

theorem insert_append_length (pre xs : List A) (x : A) :
    insert (pre ++ xs) pre.length x = pre ++ x :: xs := by
  induction pre with
  | nil => exact insert_zero xs x
  | cons p t ih => simp [insert, ih]

theorem remove_append_length (pre xs : List A) (x : A) :
    remove (pre ++ x :: xs) pre.length = pre ++ xs := by
  induction pre with
  | nil => rfl
  | cons p t ih => simp [remove, ih]

theorem take_insert_of_le (xs : List A) (x : A) (j m : Nat) (hj : j ≤ m) :
    (insert xs j x).take (m + 1) = insert (xs.take m) j x := by
  induction xs generalizing j m with
  | nil => simp [insert]
  | cons r rs ih =>
    cases j with
    | zero => simp [insert, insert_zero]
    | succ j =>
      cases m with
      | zero => omega
      | succ m => simp [insert, ih j m (by omega)]

theorem take_insert_of_ge (xs : List A) (x : A) (j m : Nat) (hj : m ≤ j) (hm : m ≤ xs.length) :
    (insert xs j x).take m = xs.take m := by
  induction xs generalizing j m with
  | nil => simp at hm; simp [hm]
  | cons r rs ih =>
    cases m with
    | zero => simp
    | succ m =>
      cases j with
      | zero => omega
      | succ j => simp [insert, ih j m (by omega) (by simp at hm; omega)]

theorem take_remove_of_lt (xs : List A) (j m : Nat) (hj : j < m) :
    (remove xs j).take (m - 1) = remove (xs.take m) j := by
  induction xs generalizing j m with
  | nil => simp [remove]
  | cons r rs ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases j with
      | zero => simp [remove]
      | succ j =>
        cases m with
        | zero => omega
        | succ m =>
          have := ih j (m + 1) (by omega)
          simp only [Nat.add_sub_cancel] at this
          simp [remove, this]

theorem take_remove_of_ge (xs : List A) (j m : Nat) (hj : m ≤ j) :
    (remove xs j).take m = xs.take m := by
  induction xs generalizing j m with
  | nil => simp [remove]
  | cons r rs ih =>
    cases m with
    | zero => simp
    | succ m =>
      cases j with
      | zero => omega
      | succ j => simp [remove, ih j m (by omega)]

end

theorem take_update (ca : EditStructure) (xs : List ca.Value) (j m : Nat) (d : ca.Edit) :
    (update ca xs j d).take m = update ca (xs.take m) j d := by
  induction xs generalizing j m with
  | nil => simp [update]
  | cons r rs ih =>
    cases m with
    | zero => simp [update]
    | succ m =>
      cases j with
      | zero => simp [update]
      | succ j => simp [update, ih j m]

theorem take_update_of_ge (ca : EditStructure) (xs : List ca.Value) (j m : Nat) (d : ca.Edit) (hj : m ≤ j) :
    (update ca xs j d).take m = xs.take m := by
  rw [take_update, update_past _ _ (by simp; omega)]

/-! ## Proof steps: placing -/

section
variable {R : Type} (h : R → Nat) (H : Int)

theorem place_move (y d : Int) (xs : List R) :
    (place h y xs).map (·.move d) = place h (y + d) xs := by
  induction xs generalizing y with
  | nil => rfl
  | cons r rs ih =>
    show (⟨y, r⟩ : Placed R).move d :: (place h (y + h r) rs).map (·.move d) = ⟨y + d, r⟩ :: place h (y + d + h r) rs
    rw [ih, show y + ↑(h r) + d = y + d + ↑(h r) by omega]
    rfl

theorem window_eq_place (y : Int) (rs : List R) :
    window h H y rs = place h y (rs.take (window h H y rs).length) := by
  induction rs generalizing y with
  | nil => rfl
  | cons r rs ih =>
    by_cases hy : y < H
    · simp only [window, hy, ite_true, List.length_cons, List.take_succ_cons, place]
      exact congrArg _ (ih _)
    · simp [window, hy, place]

theorem window_length_le (y : Int) (rs : List R) : (window h H y rs).length ≤ rs.length := by
  induction rs generalizing y with
  | nil => simp [window]
  | cons r rs ih => by_cases hy : y < H <;> simp [window, hy, ih]

theorem place_insert (x : R) (xs : List R) (j : Nat) (y : Int) (hj : j ≤ xs.length) :
    place h y (insert xs j x) =
      Drawing.shiftFrom (h x) (j + 1) (insert (place h y xs) j ⟨y + height h (xs.take j), x⟩) := by
  induction xs generalizing j y with
  | nil =>
    have : j = 0 := by simpa using hj
    subst this
    simp [insert, place, height, Drawing.shiftFrom]
  | cons r rs ih =>
    cases j with
    | zero =>
      simp only [insert, place, List.take_zero, height, Int.natCast_zero, Int.add_zero, Drawing.shiftFrom,
        List.map_cons, place_move]
      rw [show y + ↑(h r) + ↑(h x) = y + ↑(h x) + ↑(h r) by omega]
      rfl
    | succ j =>
      simp only [insert, place, Drawing.shiftFrom, List.take_succ_cons, height]
      rw [ih j (y + h r) (by simp at hj; omega)]
      rw [show y + ↑(h r) + ↑(height h (rs.take j)) = y + ↑(h r + height h (rs.take j)) by omega]

theorem place_remove (x : R) (xs : List R) (j : Nat) (y : Int) (hx : xs[j]? = some x) :
    place h y (remove xs j) = Drawing.shiftFrom (-(h x : Int)) j (remove (place h y xs) j) := by
  induction xs generalizing j y with
  | nil => simp at hx
  | cons r rs ih =>
    cases j with
    | zero =>
      simp at hx
      subst hx
      simp only [remove, place, Drawing.shiftFrom, place_move]
      rw [show y + ↑(h r) + -↑(h r) = y by omega]
    | succ j =>
      simp at hx
      simp only [remove, place, Drawing.shiftFrom]
      rw [ih j (y + h r) hx]

theorem place_update (ca : EditStructure) (h : ca.Value → Nat) (x : ca.Value) (d : ca.Edit)
    (xs : List ca.Value) (j : Nat) (y : Int) (hx : xs[j]? = some x) :
    place h y (update ca xs j d) =
      Drawing.shiftFrom ((h (ca.apply d x) : Int) - h x) (j + 1) (Drawing.setRow (ca.apply d x) j (place h y xs)) := by
  induction xs generalizing j y with
  | nil => simp at hx
  | cons r rs ih =>
    cases j with
    | zero =>
      simp at hx
      subst hx
      simp only [update, place, Drawing.setRow, Drawing.shiftFrom, place_move]
      rw [show y + ↑(h r) + (↑(h (ca.apply d r)) - ↑(h r)) = y + ↑(h (ca.apply d r)) by omega]
    | succ j =>
      simp at hx
      simp only [update, place, Drawing.setRow, Drawing.shiftFrom]
      rw [ih j (y + h r) hx]

/-! ## Proof steps: the rows that enter and leave -/

theorem dropAll_ok (pre : List (Placed R)) (y : Int) (m : Nat) (rs : List R) :
    run (Drawing.editStructure R) (view.dropAll pre.length m rs) (pre ++ place h y (rs.take m)) = pre := by
  induction rs generalizing m y with
  | nil => cases m <;> simp [view.dropAll, place, run]
  | cons r rs ih =>
    cases m with
    | zero => simp [view.dropAll, place, run]
    | succ m =>
      show run (Drawing.editStructure R) (view.dropAll pre.length m rs)
        (remove (pre ++ ⟨y, r⟩ :: place h (y + h r) (rs.take m)) pre.length) = pre
      rw [remove_append_length]
      exact ih _ _

theorem fit_ok (pre : List (Placed R)) (y : Int) (p m : Nat) (rs : List R) :
    run (Drawing.editStructure R) (view.fit h H pre.length y p m rs)
      (pre ++ place h (y + height h (rs.take p)) ((rs.drop p).take m)) = pre ++ window h H y rs := by
  induction rs generalizing pre y p m with
  | nil => cases p <;> cases m <;> simp [view.fit, place, window, run]
  | cons r rs ih =>
    by_cases hy : y < H
    · have step : ∀ p' m' (d : List (Placed R)),
          run (Drawing.editStructure R) (view.fit h H (pre.length + 1) (y + h r) p' m' rs)
            (pre ++ ⟨y, r⟩ :: d) = pre ++ window h H y (r :: rs) →
          run (Drawing.editStructure R) (view.fit h H (pre.length + 1) (y + h r) p' m' rs)
            (pre ++ ⟨y, r⟩ :: d) = pre ++ window h H y (r :: rs) := fun _ _ _ x => x
      have ih' := fun p' m' => ih (pre ++ [⟨y, r⟩]) (y + h r) p' m'
      simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at ih'
      cases p with
      | succ p =>
        simp only [view.fit, hy, ite_true, window, List.take_succ_cons, List.drop_succ_cons, height]
        show run (Drawing.editStructure R) (view.fit h H (pre.length + 1) (y + h r) p m rs)
          (insert (pre ++ place h (y + ↑(h r + height h (rs.take p))) ((rs.drop p).take m)) pre.length ⟨y, r⟩) = _
        rw [insert_append_length, show y + ↑(h r + height h (rs.take p)) = y + ↑(h r) + ↑(height h (rs.take p)) by omega]
        exact ih' p m
      | zero =>
        cases m with
        | zero =>
          simp only [view.fit, hy, ite_true, window]
          show run (Drawing.editStructure R) (view.fit h H (pre.length + 1) (y + h r) 0 0 rs)
            (insert (pre ++ []) pre.length ⟨y, r⟩) = _
          rw [insert_append_length]
          simpa [place] using ih' 0 0
        | succ m =>
          simp only [view.fit, hy, ite_true, window, List.take_zero, List.drop_zero, List.take_succ_cons, place,
            height, Int.natCast_zero, Int.add_zero]
          simpa [place, height] using ih' 0 m
    · cases p with
      | succ p =>
        simp only [view.fit, hy, ite_false, window, List.append_nil, List.take_succ_cons, List.drop_succ_cons]
        exact dropAll_ok h pre _ m (rs.drop p)
      | zero =>
        cases m with
        | zero => simp [view.fit, hy, window, place, run]
        | succ m =>
          simp only [view.fit, hy, ite_false, window, List.append_nil, List.take_zero, List.drop_zero, height,
            Int.natCast_zero, Int.add_zero]
          exact dropAll_ok h pre y (m + 1) (r :: rs)

/-- `fit` with no new rows, from the start of the drawing. -/
theorem fit_ok' (y : Int) (m : Nat) (rs : List R) :
    run (Drawing.editStructure R) (view.fit h H 0 y 0 m rs) (place h y (rs.take m)) = window h H y rs := by
  simpa [height] using fit_ok h H [] y 0 m rs

theorem push_ok (above : List R) (m : Nat) (rs : List R) (off : Int) :
    run (Drawing.editStructure R) (view.push h H m rs off) (place h (-off) (rs.take m)) =
      window h H (-(Scroll.push h above rs off).off) (Scroll.push h above rs off).rest := by
  induction rs generalizing above m off with
  | nil => cases m <;> rfl
  | cons r rs ih =>
    by_cases hr : (h r : Int) ≤ off
    · simp only [view.push, Scroll.push, hr, ite_true]
      rw [run_append]
      cases m with
      | zero => simpa [run, place] using ih (r :: above) 0 (off - h r)
      | succ m =>
        show run (Drawing.editStructure R) (view.push h H m rs (off - h r)) (remove (⟨-off, r⟩ :: place h (-off + h r) (rs.take m)) 0) = _
        simp only [remove]
        rw [show -off + ↑(h r) = -(off - ↑(h r)) by omega]
        exact ih (r :: above) m (off - h r)
    · simp only [view.push, Scroll.push, hr, ite_false]
      exact fit_ok' h H (-off) m (r :: rs)

theorem pull_ok (p m : Nat) (rest above : List R) (off : Int) :
    run (Drawing.editStructure R) (view.pull h H p m rest above off)
      (place h (-off + height h (rest.take p)) ((rest.drop p).take m)) =
      window h H (-(Scroll.pull h rest above off).off) (Scroll.pull h rest above off).rest := by
  induction above generalizing p rest off with
  | nil =>
    simp only [view.pull, Scroll.pull]
    simpa using fit_ok h H [] (-off) p m rest
  | cons r above ih =>
    by_cases ho : off < 0
    · simp only [view.pull, Scroll.pull, ho, ite_true]
      have := ih (p + 1) (r :: rest) (off + h r)
      simp only [List.take_succ_cons, List.drop_succ_cons, height] at this
      rw [show -(off + ↑(h r)) + ↑(h r + height h (rest.take p)) = -off + ↑(height h (rest.take p)) by omega] at this
      exact this
    · simp only [view.pull, Scroll.pull, ho, ite_false]
      simpa using fit_ok h H [] (-off) p m rest

theorem settle_ok (m : Nat) (z : Scroll R) :
    run (Drawing.editStructure R) (view.settle h H m z) (place h (-z.off) (z.rest.take m)) = Scroll.draw h H z := by
  unfold view.settle Scroll.draw Scroll.normalize
  by_cases ho : z.off < 0
  · simp only [ho, ite_true]
    simpa [height] using pull_ok h H 0 m z.rest z.above z.off
  · simp only [ho, ite_false]
    exact push_ok h H z.above m z.rest z.off

theorem count_eq (y : Int) (rs : List R) : count h H y rs = (window h H y rs).length := by
  induction rs generalizing y with
  | nil => rfl
  | cons r rs ih => by_cases hy : y < H <;> simp [count, window, hy, ih]

/-! ## Proof steps: normalizing -/

theorem push_normal (above rs : List R) (off : Int) (ho : 0 ≤ off) :
    Scroll.normalize h (Scroll.push h above rs off) = Scroll.push h above rs off := by
  induction rs generalizing above off with
  | nil => simp [Scroll.push, Scroll.normalize, Int.not_lt.mpr ho]
  | cons r rs ih =>
    by_cases hr : (h r : Int) ≤ off
    · simp only [Scroll.push, hr, ite_true]
      exact ih _ _ (by omega)
    · simp [Scroll.push, Scroll.normalize, hr, Int.not_lt.mpr ho]

theorem pull_normal (rest above : List R) (off : Int)
    (hp : off < 0 ∨ ∃ r rs, rest = r :: rs ∧ off < (h r : Int)) :
    Scroll.normalize h (Scroll.pull h rest above off) = Scroll.pull h rest above off := by
  induction above generalizing rest off with
  | nil =>
    by_cases ho : off < 0
    · simp [Scroll.pull, Scroll.normalize, ho]
    · obtain ⟨r, rs, rfl, hr⟩ := hp.resolve_left ho
      simp [Scroll.pull, Scroll.normalize, Scroll.push, ho, Int.not_le.mpr hr]
  | cons a above ih =>
    by_cases ho : off < 0
    · simp only [Scroll.pull, ho, ite_true]
      exact ih _ _ (.inr ⟨a, rest, rfl, by omega⟩)
    · obtain ⟨r, rs, rfl, hr⟩ := hp.resolve_left ho
      simp [Scroll.pull, Scroll.normalize, Scroll.push, ho, Int.not_le.mpr hr]

end

/-! ## Proof steps: an edit's own effect -/

theorem core_ok (ca : EditStructure) (h : ca.Value → Nat) (n : Scroll ca.Value) (m : Nat)
    (hm : m ≤ n.rest.length) (e : Scroll.Edit ca) :
    run (Drawing.editStructure ca.Value) (view.core ca h n m e).1 (place h (-n.off) (n.rest.take m)) =
      place h (-(Scroll.step ca e n).off) ((Scroll.step ca e n).rest.take (view.core ca h n m e).2) := by
  obtain ⟨above, rest, off⟩ := n
  simp only at hm
  cases e with
  | scroll dy =>
    show (place h (-off) (rest.take m)).map (·.move (-dy)) = place h (-(off + dy)) (rest.take m)
    rw [place_move, show -off + -dy = -(off + dy) by omega]
  | list e =>
    cases e with
    | insert i x =>
      by_cases hi : i < above.length
      · have : ¬ (above.length ≤ i ∧ i - above.length < m) := by omega
        simp [view.core, Scroll.step, Scroll.edit, hi, this, run]
      · by_cases hj : i - above.length < m
        · have hc : above.length ≤ i ∧ i - above.length < m := ⟨by omega, hj⟩
          simp only [view.core, Scroll.step, Scroll.edit, hi, hc, and_self, ite_true, ite_false]
          show Drawing.shiftFrom (h x) (i - above.length + 1)
              (insert (place h (-off) (rest.take m)) (i - above.length)
                ⟨-off + height h (rest.take (i - above.length)), x⟩) = _
          rw [take_insert_of_le _ _ _ _ (by omega),
            place_insert h x _ _ _ (by simp; omega), List.take_take, Nat.min_eq_left (by omega)]
        · have hc : ¬ (above.length ≤ i ∧ i - above.length < m) := by omega
          simp only [view.core, Scroll.step, Scroll.edit, hi, hc, ite_false]
          rw [take_insert_of_ge _ _ _ _ (by omega) hm]
          rfl
    | delete i =>
      by_cases hi : i < above.length
      · have : ¬ (above.length ≤ i ∧ i - above.length < m) := by omega
        simp [view.core, Scroll.step, Scroll.edit, hi, this, run]
      · by_cases hj : i - above.length < m
        · have hc : above.length ≤ i ∧ i - above.length < m := ⟨by omega, hj⟩
          cases hx : rest[i - above.length]? with
          | none => simp at hx; omega
          | some x =>
            simp only [view.core, Scroll.step, Scroll.edit, hi, hc, hx, and_self, ite_true, ite_false]
            show Drawing.shiftFrom (-(h x : Int)) (i - above.length)
                (remove (place h (-off) (rest.take m)) (i - above.length)) = _
            rw [take_remove_of_lt _ _ _ hj, place_remove h x _ _ _ (by rw [List.getElem?_take]; simp [hj, hx])]
        · have hc : ¬ (above.length ≤ i ∧ i - above.length < m) := by omega
          simp only [view.core, Scroll.step, Scroll.edit, hi, hc, ite_false]
          rw [take_remove_of_ge _ _ _ (by omega)]
          rfl
    | update i d =>
      by_cases hi : i < above.length
      · have : ¬ (above.length ≤ i ∧ i - above.length < m) := by omega
        simp [view.core, Scroll.step, Scroll.edit, hi, this, run]
      · by_cases hj : i - above.length < m
        · have hc : above.length ≤ i ∧ i - above.length < m := ⟨by omega, hj⟩
          cases hx : rest[i - above.length]? with
          | none => simp at hx; omega
          | some x =>
            simp only [view.core, Scroll.step, Scroll.edit, hi, hc, hx, and_self, ite_true, ite_false]
            show Drawing.shiftFrom ((h (ca.apply d x) : Int) - h x) (i - above.length + 1)
                (Drawing.setRow (ca.apply d x) (i - above.length) (place h (-off) (rest.take m))) = _
            rw [take_update, place_update ca h x d _ _ _ (by rw [List.getElem?_take]; simp [hj, hx])]
        · have hc : ¬ (above.length ≤ i ∧ i - above.length < m) := by omega
          simp only [view.core, Scroll.step, Scroll.edit, hi, hc, ite_false]
          rw [take_update_of_ge _ _ _ _ _ (by omega)]
          rfl

/-! ## Proof steps: the list the scrolled list holds -/

section
variable {A : Type}

theorem insert_append_of_le (xs ys : List A) (x : A) (i : Nat) (hi : i ≤ xs.length) :
    insert (xs ++ ys) i x = insert xs i x ++ ys := by
  induction xs generalizing i with
  | nil => simp at hi; subst hi; simp [insert_zero, insert]
  | cons r rs ih =>
    cases i with
    | zero => simp [insert]
    | succ i => simp [insert, ih i (by simp at hi; omega)]

theorem insert_append_add (xs ys : List A) (x : A) (j : Nat) :
    insert (xs ++ ys) (xs.length + j) x = xs ++ insert ys j x := by
  induction xs with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons, Nat.add_right_comm]
    simp [insert, ih]

theorem remove_append_of_lt (xs ys : List A) (i : Nat) (hi : i < xs.length) :
    remove (xs ++ ys) i = remove xs i ++ ys := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons r rs ih =>
    cases i with
    | zero => simp [remove]
    | succ i => simp [remove, ih i (by simp at hi; omega)]

theorem remove_append_add (xs ys : List A) (j : Nat) :
    remove (xs ++ ys) (xs.length + j) = xs ++ remove ys j := by
  induction xs with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons, Nat.add_right_comm]
    simp [remove, ih]

theorem insert_reverse (xs : List A) (x : A) (i : Nat) (hi : i ≤ xs.length) :
    insert xs.reverse i x = (insert xs (xs.length - i) x).reverse := by
  induction xs generalizing i with
  | nil => simp at hi; subst hi; rfl
  | cons y t ih =>
    rw [List.reverse_cons]
    by_cases ht : i ≤ t.length
    · rw [insert_append_of_le _ _ _ _ (by simpa using ht), ih i ht,
        show (y :: t).length - i = t.length - i + 1 by simp; omega]
      simp [insert]
    · have : i = t.length + 1 := by simp at hi; omega
      subst this
      rw [show t.length + 1 = t.reverse.length + [y].length by simp, insert_append_add]
      simp [insert, insert_zero]

theorem remove_reverse (xs : List A) (i : Nat) (hi : i < xs.length) :
    remove xs.reverse i = (remove xs (xs.length - 1 - i)).reverse := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons y t ih =>
    rw [List.reverse_cons]
    by_cases ht : i < t.length
    · rw [remove_append_of_lt _ _ _ (by simpa using ht), ih i ht,
        show (y :: t).length - 1 - i = t.length - 1 - i + 1 by simp; omega]
      simp [remove]
    · have : i = t.length := by simp at hi; omega
      subst this
      rw [show t.length = t.reverse.length + 0 by simp, remove_append_add]
      simp [remove]

end

theorem update_append_of_lt (ca : EditStructure) (xs ys : List ca.Value) (d : ca.Edit) (i : Nat)
    (hi : i < xs.length) : update ca (xs ++ ys) i d = update ca xs i d ++ ys := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons r rs ih =>
    cases i with
    | zero => simp [update]
    | succ i => simp [update, ih i (by simp at hi; omega)]

theorem update_append_add (ca : EditStructure) (xs ys : List ca.Value) (d : ca.Edit) (j : Nat) :
    update ca (xs ++ ys) (xs.length + j) d = xs ++ update ca ys j d := by
  induction xs with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons, Nat.add_right_comm]
    simp [update, ih]

theorem update_reverse (ca : EditStructure) (xs : List ca.Value) (d : ca.Edit) (i : Nat)
    (hi : i < xs.length) : update ca xs.reverse i d = (update ca xs (xs.length - 1 - i) d).reverse := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons y t ih =>
    rw [List.reverse_cons]
    by_cases ht : i < t.length
    · rw [update_append_of_lt _ _ _ _ _ (by simpa using ht), ih i ht,
        show (y :: t).length - 1 - i = t.length - 1 - i + 1 by simp; omega]
      simp [update]
    · have : i = t.length := by simp at hi; omega
      subst this
      rw [show t.length = t.reverse.length + 0 by simp, update_append_add]
      simp [update]

theorem rows_edit (ca : EditStructure) (e : Edit.of ca) (z : Scroll ca.Value) :
    (Scroll.edit ca e z).rows = edit ca e z.rows := by
  obtain ⟨above, rest, off⟩ := z
  cases e with
  | insert i x =>
    by_cases hi : i < above.length
    · simp only [Scroll.edit, hi, ite_true, Scroll.rows, edit]
      rw [insert_append_of_le _ _ _ _ (by simp; omega), insert_reverse _ _ _ (by omega)]
    · simp only [Scroll.edit, hi, ite_false, Scroll.rows, edit]
      rw [show i = above.reverse.length + (i - above.length) by simp; omega, insert_append_add]
      simp
  | delete i =>
    by_cases hi : i < above.length
    · simp only [Scroll.edit, hi, ite_true, Scroll.rows, edit]
      rw [remove_append_of_lt _ _ _ (by simpa using hi), remove_reverse _ _ (by omega)]
    · simp only [Scroll.edit, hi, ite_false, Scroll.rows, edit]
      rw [show i = above.reverse.length + (i - above.length) by simp; omega, remove_append_add]
      simp
  | update i d =>
    by_cases hi : i < above.length
    · simp only [Scroll.edit, hi, ite_true, Scroll.rows, edit]
      rw [update_append_of_lt _ _ _ _ _ (by simpa using hi), update_reverse _ _ _ _ (by omega)]
    · simp only [Scroll.edit, hi, ite_false, Scroll.rows, edit]
      rw [show i = above.reverse.length + (i - above.length) by simp; omega, update_append_add]
      simp

section
variable {R : Type} (h : R → Nat) (H : Int)

theorem rows_push (above rs : List R) (off : Int) :
    (Scroll.push h above rs off).rows = above.reverse ++ rs := by
  induction rs generalizing above off with
  | nil => rfl
  | cons r rs ih =>
    by_cases hr : (h r : Int) ≤ off
    · simp [Scroll.push, hr, ih]
    · simp [Scroll.push, hr, Scroll.rows]

theorem rows_pull (rest above : List R) (off : Int) :
    (Scroll.pull h rest above off).rows = above.reverse ++ rest := by
  induction above generalizing rest off with
  | nil => rfl
  | cons r above ih =>
    by_cases ho : off < 0
    · simp [Scroll.pull, ho, ih]
    · simp [Scroll.pull, ho, Scroll.rows]

theorem offset_push (above rs : List R) (off : Int) :
    (Scroll.push h above rs off).offset h = height h above + off := by
  induction rs generalizing above off with
  | nil => rfl
  | cons r rs ih =>
    by_cases hr : (h r : Int) ≤ off
    · simp only [Scroll.push, hr, ite_true, ih, height]
      omega
    · simp [Scroll.push, hr, Scroll.offset]

theorem offset_pull (rest above : List R) (off : Int) :
    (Scroll.pull h rest above off).offset h = height h above + off := by
  induction above generalizing rest off with
  | nil => rfl
  | cons r above ih =>
    by_cases ho : off < 0
    · simp only [Scroll.pull, ho, ite_true, ih, height]
      omega
    · simp [Scroll.pull, ho, Scroll.offset]

end

/-! ## Proof steps: what shows -/

section
variable {R : Type} (h : R → Nat) (H : Int)

theorem height_append (xs ys : List R) : height h (xs ++ ys) = height h xs + height h ys := by
  induction xs with
  | nil => simp [height]
  | cons r rs ih => simp [height, ih]; omega

theorem height_reverse (xs : List R) : height h xs.reverse = height h xs := by
  induction xs with
  | nil => rfl
  | cons r rs ih => simp [height_append, height, ih]; omega

theorem place_append (y : Int) (xs ys : List R) :
    place h y (xs ++ ys) = place h y xs ++ place h (y + height h xs) ys := by
  induction xs generalizing y with
  | nil => simp [place, height]
  | cons r rs ih =>
    simp only [List.cons_append, place, ih, height]
    rw [show y + ↑(h r) + ↑(height h rs) = y + ↑(h r + height h rs) by omega]

theorem filter_place_ends_above (y : Int) (xs : List R) (hy : y + height h xs ≤ 0) :
    (place h y xs).filter (shows h H) = [] := by
  induction xs generalizing y with
  | nil => rfl
  | cons r rs ih =>
    simp only [height] at hy
    have : shows h H ⟨y, r⟩ = false := by simp [shows]; omega
    simp only [place, List.filter_cons, this, Bool.false_eq_true, ite_false]
    exact ih _ (by omega)

theorem filter_place_starts_below (y : Int) (xs : List R) (hy : H ≤ y) :
    (place h y xs).filter (shows h H) = [] := by
  induction xs generalizing y with
  | nil => rfl
  | cons r rs ih =>
    have : shows h H ⟨y, r⟩ = false := by simp [shows]; omega
    simp only [place, List.filter_cons, this, Bool.false_eq_true, ite_false]
    exact ih _ (by omega)

theorem filter_place_starts_inside (y : Int) (xs : List R) (hy : 0 < y) :
    (place h y xs).filter (shows h H) = window h H y xs := by
  induction xs generalizing y with
  | nil => rfl
  | cons r rs ih =>
    by_cases hH : y < H
    · have : shows h H ⟨y, r⟩ = true := by simp [shows]; omega
      simp only [place, List.filter_cons, this, ite_true, window, hH]
      rw [ih _ (by omega)]
    · simp only [window, hH, ite_false]
      exact filter_place_starts_below h H y _ (by omega)

/-- What normalizing leaves: an anchor whose top is at or above the window's
top and which ends below it (or no anchor, past the end), or else the
window's top above the list's first row. -/
def normalShape (n : Scroll R) : Prop :=
  (0 ≤ n.off ∧ ∀ r rs, n.rest = r :: rs → n.off < h r) ∨ (n.off < 0 ∧ n.above = [])

theorem push_shape (above rs : List R) (off : Int) (ho : 0 ≤ off) : normalShape h (Scroll.push h above rs off) := by
  induction rs generalizing above off with
  | nil => exact .inl ⟨ho, by simp [Scroll.push]⟩
  | cons r rs ih =>
    by_cases hr : (h r : Int) ≤ off
    · simp only [Scroll.push, hr, ite_true]
      exact ih _ _ (by omega)
    · simp only [Scroll.push, hr, ite_false]
      refine .inl ⟨ho, ?_⟩
      intro r' rs' he
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      show off < h r
      omega

theorem pull_shape (rest above : List R) (off : Int)
    (hp : off < 0 ∨ ∃ r rs, rest = r :: rs ∧ off < (h r : Int)) : normalShape h (Scroll.pull h rest above off) := by
  induction above generalizing rest off with
  | nil =>
    by_cases ho : off < 0
    · exact .inr ⟨ho, rfl⟩
    · obtain ⟨r, rs, rfl, hr⟩ := hp.resolve_left ho
      refine .inl ⟨show 0 ≤ off by omega, ?_⟩
      intro r' rs' he
      simp only [Scroll.pull, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hr
  | cons a above ih =>
    by_cases ho : off < 0
    · simp only [Scroll.pull, ho, ite_true]
      exact ih _ _ (.inr ⟨a, rest, rfl, by omega⟩)
    · obtain ⟨r, rs, rfl, hr⟩ := hp.resolve_left ho
      simp only [Scroll.pull, ho, ite_false]
      refine .inl ⟨show 0 ≤ off by omega, ?_⟩
      intro r' rs' he
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hr

theorem normalize_shape (z : Scroll R) : normalShape h (Scroll.normalize h z) := by
  unfold Scroll.normalize
  split
  · exact pull_shape h _ _ _ (.inl (by assumption))
  · exact push_shape h _ _ _ (by omega)

theorem window_of_shape (n : Scroll R) (hn : normalShape h n) :
    window h H (-n.off) n.rest = (place h (-(n.offset h)) n.rows).filter (shows h H) := by
  obtain ⟨above, rest, off⟩ := n
  simp only [Scroll.rows, Scroll.offset, place_append, List.filter_append, height_reverse]
  rw [show -(↑(height h above) + off) + ↑(height h above) = -off by omega]
  rcases hn with ⟨ho, hr⟩ | ⟨ho, ha⟩
  · simp only at ho
    rw [filter_place_ends_above h H _ _ (by rw [height_reverse]; omega), List.nil_append]
    cases rest with
    | nil => rfl
    | cons r rs =>
      have hr := hr r rs rfl
      simp only at ho hr
      by_cases hH : -off < H
      · have : shows h H ⟨-off, r⟩ = true := by simp [shows]; omega
        simp only [window, hH, ite_true, place, List.filter_cons, this]
        rw [filter_place_starts_inside h H _ _ (by omega)]
      · simp only [window, hH, ite_false]
        exact (filter_place_starts_below h H _ _ (by omega)).symm
  · simp only at ho ha
    subst ha
    simp only [List.reverse_nil, place, List.filter_nil, List.nil_append]
    exact (filter_place_starts_inside h H _ _ (by omega)).symm

end

/-! ## Proof steps: the extent -/

section
variable {R : Type} (h : R → Nat)

theorem remove_past (xs : List R) (j : Nat) (hj : xs.length ≤ j) : remove xs j = xs := by
  induction xs generalizing j with
  | nil => rfl
  | cons y t ih =>
    cases j with
    | zero => simp at hj
    | succ j =>
      show y :: remove t j = y :: t
      rw [ih j (by simp at hj; omega)]

theorem height_insert (xs : List R) (j : Nat) (x : R) : height h (insert xs j x) = height h xs + h x := by
  induction xs generalizing j with
  | nil => simp [insert, height]
  | cons y t ih => cases j <;> simp [insert, height, ih] <;> omega

theorem height_remove (xs : List R) (j : Nat) (x : R) (hx : xs[j]? = some x) :
    height h (remove xs j) + h x = height h xs := by
  induction xs generalizing j with
  | nil => simp at hx
  | cons y t ih =>
    cases j with
    | zero =>
      simp at hx
      subst hx
      simp [remove, height]
      omega
    | succ j =>
      simp at hx
      have := ih j hx
      simp [remove, height]
      omega

end

theorem height_update (ca : EditStructure) (h : ca.Value → Nat) (xs : List ca.Value) (j : Nat) (x : ca.Value)
    (d : ca.Edit) (hx : xs[j]? = some x) :
    height h (update ca xs j d) + h x = height h xs + h (ca.apply d x) := by
  induction xs generalizing j with
  | nil => simp at hx
  | cons y t ih =>
    cases j with
    | zero =>
      simp at hx
      subst hx
      simp [update, height]
      omega
    | succ j =>
      simp at hx
      have := ih j hx
      simp [update, height]
      omega

/-- A list edit's effect on the extent, before normalizing. -/
theorem extent_edit (ca : EditStructure) (h : ca.Value → Nat) (e : Edit.of ca) (n : Scroll ca.Value) :
    (Scroll.edit ca e n).extent h =
      Extent.edits.apply (if e.pos < n.above.length then grows ca h n e else 0, grows ca h n e) (n.extent h) := by
  obtain ⟨above, rest, off⟩ := n
  simp only [Scroll.extent, Scroll.offset, Scroll.rows, height_append, height_reverse, Extent.mk.injEq]
  cases e with
  | insert i x =>
    by_cases hi : i < above.length
    · simp only [Scroll.edit, hi, ite_true, Edit.pos, grows, height_insert]
      omega
    · simp only [Scroll.edit, hi, ite_false, Edit.pos, grows, height_insert]
      omega
  | delete i =>
    by_cases hi : i < above.length
    · obtain ⟨x, hx⟩ : ∃ x, above[above.length - 1 - i]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have := height_remove h above _ x hx
      simp only [Scroll.edit, hi, ite_true, Edit.pos, grows, Scroll.get?, hx]
      omega
    · simp only [Scroll.edit, hi, ite_false, Edit.pos, grows, Scroll.get?]
      cases hx : rest[i - above.length]? with
      | none =>
        rw [remove_past rest _ (List.getElem?_eq_none_iff.mp hx)]
        simp only
        omega
      | some x =>
        have := height_remove h rest _ x hx
        simp only
        omega
  | update i d =>
    by_cases hi : i < above.length
    · obtain ⟨x, hx⟩ : ∃ x, above[above.length - 1 - i]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have := height_update ca h above _ x d hx
      simp only [Scroll.edit, hi, ite_true, Edit.pos, grows, Scroll.get?, hx]
      omega
    · simp only [Scroll.edit, hi, ite_false, Edit.pos, grows, Scroll.get?]
      cases hx : rest[i - above.length]? with
      | none =>
        rw [update_past rest _ (List.getElem?_eq_none_iff.mp hx)]
        simp only
        omega
      | some x =>
        have := height_update ca h rest _ x d hx
        simp only
        omega

/-! ## Laws -/

section
variable {R : Type} (h : R → Nat) (H : Int)

/-- Normalizing keeps the list. -/
theorem rows_normalize (z : Scroll R) : (Scroll.normalize h z).rows = z.rows := by
  unfold Scroll.normalize
  split
  · exact rows_pull h _ _ _
  · exact rows_push h _ _ _

/-- Normalizing keeps the offset. -/
theorem offset_normalize (z : Scroll R) : (Scroll.normalize h z).offset h = z.offset h := by
  unfold Scroll.normalize
  split
  · exact offset_pull h _ _ _
  · exact offset_push h _ _ _

/-- Normalizing twice is normalizing once: a normalized list stays as it is. -/
theorem normalize_normalize (z : Scroll R) :
    Scroll.normalize h (Scroll.normalize h z) = Scroll.normalize h z := by
  unfold Scroll.normalize
  by_cases ho : z.off < 0
  · simp only [ho, ite_true]
    exact pull_normal h z.rest z.above z.off (.inl ho)
  · simp only [ho, ite_false]
    exact push_normal h z.above z.rest z.off (by omega)

/-- What shows is the list's rows that show, placed one under another from
the scroll offset: the view, recomputed from the whole list. -/
theorem draw_eq (z : Scroll R) :
    Scroll.draw h H z = (place h (-(z.offset h)) z.rows).filter (shows h H) := by
  show window h H (-(Scroll.normalize h z).off) (Scroll.normalize h z).rest = _
  rw [window_of_shape h H _ (normalize_shape h z), offset_normalize, rows_normalize]

end

/-- A list edit edits the list. -/
theorem rows_apply_list (ca : EditStructure) (h : ca.Value → Nat) (e : Edit.of ca) (z : Scroll ca.Value) :
    (Scroll.apply ca h (.list e) z).rows = edit ca e z.rows := by
  simp only [Scroll.apply, rows_normalize, Scroll.step, rows_edit]

/-- Scrolling keeps the list. -/
theorem rows_apply_scroll (ca : EditStructure) (h : ca.Value → Nat) (dy : Int) (z : Scroll ca.Value) :
    (Scroll.apply ca h (.scroll dy) z).rows = z.rows := by
  simp only [Scroll.apply, rows_normalize, Scroll.step]
  exact rows_normalize h z

/-- Scrolling by `dy` moves the offset by `dy`. -/
theorem offset_apply_scroll (ca : EditStructure) (h : ca.Value → Nat) (dy : Int) (z : Scroll ca.Value) :
    (Scroll.apply ca h (.scroll dy) z).offset h = z.offset h + dy := by
  simp only [Scroll.apply, offset_normalize, Scroll.step]
  rw [← offset_normalize h z]
  simp only [Scroll.offset]
  omega

/-- The extent's derivative is correct: its amounts, added to the extent,
give the extent after the edit. -/
theorem extent_ok (ca : EditStructure) (h : ca.Value → Nat) : (extent ca h).ok := by
  intro z e
  show Extent.edits.apply (extent.df ca h z e) (z.extent h) = (Scroll.apply ca h e z).extent h
  have hz : z.extent h = (Scroll.normalize h z).extent h := by
    unfold Scroll.extent
    rw [offset_normalize, rows_normalize]
  cases e with
  | scroll dy =>
    show (⟨z.offset h + dy, height h z.rows + 0⟩ : Extent) =
      ⟨(Scroll.apply ca h (.scroll dy) z).offset h, height h (Scroll.apply ca h (.scroll dy) z).rows⟩
    rw [offset_apply_scroll, rows_apply_scroll, Int.add_zero]
  | list e =>
    have ha : (Scroll.apply ca h (.list e) z).extent h = (Scroll.edit ca e (Scroll.normalize h z)).extent h := by
      unfold Scroll.apply Scroll.extent
      simp only [Scroll.step]
      rw [offset_normalize, rows_normalize]
    rw [ha, hz, extent_edit]
    rfl

/-- The view's derivative is correct: its edits take what shows to what
shows after the edit. -/
theorem view_ok (ca : EditStructure) (h : ca.Value → Nat) (H : Int) : (view ca h H).ok := by
  intro z e
  show run (Drawing.editStructure ca.Value) (view.df ca h H z e) (Scroll.draw h H z) = Scroll.draw h H (Scroll.apply ca h e z)
  have hd : Scroll.draw h H z = place h (-(Scroll.normalize h z).off)
      ((Scroll.normalize h z).rest.take (window h H (-(Scroll.normalize h z).off) (Scroll.normalize h z).rest).length) :=
    window_eq_place h H _ _
  unfold view.df
  simp only [count_eq]
  rw [run_append, hd, core_ok ca h _ _ (window_length_le h H _ _), settle_ok]
  unfold Scroll.apply Scroll.draw
  rw [normalize_normalize]

/-- So is the lifted view's, for runs of edits. -/
theorem view_inc_ok (ca : EditStructure) (h : ca.Value → Nat) (H : Int) : (view.inc ca h H).ok :=
  lift_ok _ (view_ok ca h H)

end Puri
