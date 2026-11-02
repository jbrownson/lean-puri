/-
A list's own edits, and mapping a function over a list and over its edits: a
port of `ilc/list/list.bend` and its laws. Positions count from 0. Past the
end, these functions still give an answer (an insert appends, a delete or an
update does nothing), which nothing relies on.
-/
import Puri.Change

namespace Puri

inductive Edit (A DA : Type) where
  | insert (i : Nat) (x : A)
  | delete (i : Nat)
  | update (i : Nat) (d : DA)

/-- An edit of a list whose elements change as `ca` says. -/
abbrev Edit.of (ca : EditStructure) : Type := Edit ca.Value ca.Edit

def insert {A : Type} : List A → Nat → A → List A
  | [], _, x => [x]
  | h :: t, 0, x => x :: h :: t
  | h :: t, p + 1, x => h :: insert t p x

def remove {A : Type} : List A → Nat → List A
  | [], _ => []
  | _ :: t, 0 => t
  | h :: t, p + 1 => h :: remove t p

def update (ca : EditStructure) : List ca.Value → Nat → ca.Edit → List ca.Value
  | [], _, _ => []
  | h :: t, 0, d => ca.apply d h :: t
  | h :: t, p + 1, d => h :: update ca t p d

/-- The list after one edit. -/
def edit (ca : EditStructure) : Edit.of ca → List ca.Value → List ca.Value
  | .insert i x, xs => insert xs i x
  | .delete i, xs => remove xs i
  | .update i d, xs => update ca xs i d

/-- A list's edit structure, given how its elements are edited: one edit at a
time, which is not a change structure. Runs of them are; see
`changeStructure`. -/
abbrev editStructure (ca : EditStructure) : EditStructure :=
  ⟨List ca.Value, Edit.of ca, edit ca⟩

/-- The list after a run of edits. -/
def patch (ca : EditStructure) (es : List (Edit.of ca)) (xs : List ca.Value) : List ca.Value :=
  run (editStructure ca) es xs

/-! ## Getting from any list to any other -/

/-- Deletes every element of `xs`, front first. -/
def clear (ca : EditStructure) : List ca.Value → List (Edit.of ca)
  | [] => []
  | _ :: t => .delete 0 :: clear ca t

/-- Builds `ys` from the empty list: its tail, then its head at the front. -/
def fill (ca : EditStructure) : List ca.Value → List (Edit.of ca)
  | [] => []
  | y :: t => fill ca t ++ [.insert 0 y]

/-- A run that gets from `xs` to `ys`: clear `xs`, then fill with `ys`. -/
def diff (ca : EditStructure) (xs ys : List ca.Value) : List (Edit.of ca) :=
  clear ca xs ++ fill ca ys

theorem clear_ok (ca : EditStructure) (xs : List ca.Value) : patch ca (clear ca xs) xs = [] := by
  induction xs with
  | nil => rfl
  | cons h t ih => exact ih

theorem fill_ok (ca : EditStructure) (ys : List ca.Value) : patch ca (fill ca ys) [] = ys := by
  induction ys with
  | nil => rfl
  | cons y t ih =>
    show run (editStructure ca) (fill ca t ++ [Edit.insert 0 y]) [] = y :: t
    rw [run_append]
    show insert (patch ca (fill ca t) []) 0 y = y :: t
    rw [ih]
    cases t <;> rfl

/-- `diff` gets from `xs` to `ys`. -/
theorem diff_ok (ca : EditStructure) (xs ys : List ca.Value) : patch ca (diff ca xs ys) xs = ys := by
  show run (editStructure ca) (clear ca xs ++ fill ca ys) xs = ys
  rw [run_append]
  show patch ca (fill ca ys) (patch ca (clear ca xs) xs) = ys
  rw [clear_ok, fill_ok]

/-- A list's change structure: runs of its edits, which get from any list to
any other by `diff`. -/
def changeStructure (ca : EditStructure) : ChangeStructure :=
  ⟨runs (editStructure ca), fun xs ys => ⟨diff ca xs ys, diff_ok ca xs ys⟩⟩

/-- A list's own edits are not a change structure, if its elements have any
value at all: no one edit gets from the empty list to a list of two. -/
theorem edits_not_change_structure (ca : EditStructure) (x : ca.Value) :
    ¬ ∃ e : Edit.of ca, edit ca e [] = [x, x] := by
  intro ⟨e, h⟩
  cases e <;> simp [edit, insert, remove, update] at h

/-! ## Positions in range -/

/-- Each edit's position is in range for the list it applies to: an insert
at a gap (`0` to the length), a delete or an update at an element. The laws
below say nothing about edits that aren't valid. -/
def valid (ca : EditStructure) : List (Edit.of ca) → List ca.Value → Prop
  | [], _ => True
  | .insert i x :: t, xs => i ≤ xs.length ∧ valid ca t (insert xs i x)
  | .delete i :: t, xs => i < xs.length ∧ valid ca t (remove xs i)
  | .update i d :: t, xs => i < xs.length ∧ valid ca t (update ca xs i d)

/-! ## Mapping -/

/-- The edits one edit makes to the mapped list, given the list before it: an
insert or a delete carries over, and an update updates the same position by
`g`'s derivative. Past the end there is no element, and no edits. -/
def map.edit {ca cb : EditStructure} (g : Inc ca cb) (xs : List ca.Value) :
    Edit.of ca → List (Edit.of cb)
  | .insert i x => [.insert i (g.f x)]
  | .delete i => [.delete i]
  | .update i d =>
    match xs[i]? with
    | .none => []
    | .some x => [.update i (g.df x d)]

/-- `map`'s derivative for one edit, as an `Inc` that `lift` turns into one
for runs. -/
def map.one {ca cb : EditStructure} (g : Inc ca cb) : Inc (editStructure ca) (runs (editStructure cb)) :=
  ⟨List.map g.f, map.edit g⟩

/-- `map`'s derivative: the edits to the list `g` maps to, from a run of edits
to the list and the list before them. -/
def dmap {ca cb : EditStructure} (g : Inc ca cb) (es : List (Edit.of ca)) (xs : List ca.Value) :
    List (Edit.of cb) :=
  lift.run (map.one g) es xs

/-- `map`, as an incremental function: `g`'s function mapped over a list,
with `dmap` as its derivative. -/
def map.inc {ca cb : EditStructure} (g : Inc ca cb) : Inc (runs (editStructure ca)) (runs (editStructure cb)) :=
  lift (map.one g)

theorem map_insert {A B : Type} (f : A → B) (xs : List A) (i : Nat) (x : A) :
    (insert xs i x).map f = insert (xs.map f) i (f x) := by
  induction xs generalizing i with
  | nil => rfl
  | cons h t ih => cases i <;> simp [insert, ih]

theorem map_remove {A B : Type} (f : A → B) (xs : List A) (i : Nat) :
    (remove xs i).map f = remove (xs.map f) i := by
  induction xs generalizing i with
  | nil => rfl
  | cons h t ih => cases i <;> simp [remove, ih]

theorem map_update {ca cb : EditStructure} (g : Inc ca cb) (h : g.ok) (xs : List ca.Value) (i : Nat)
    (x : ca.Value) (hx : xs[i]? = some x) (d : ca.Edit) :
    update cb (xs.map g.f) i (g.df x d) = (update ca xs i d).map g.f := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons y t ih =>
    cases i with
    | zero =>
      simp at hx
      subst hx
      simp [update, h y d]
    | succ p =>
      simp at hx
      simp [update, ih p hx]

theorem update_past {ca : EditStructure} (xs : List ca.Value) (i : Nat) (hx : xs.length ≤ i) (d : ca.Edit) :
    update ca xs i d = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons y t ih =>
    cases i with
    | zero => simp at hx
    | succ p =>
      show y :: update ca t p d = y :: t
      rw [ih p (by simp at hx; omega)]

/-- `map`'s derivative for one edit is correct, if `g`'s is. -/
theorem map_one_ok {ca cb : EditStructure} (g : Inc ca cb) (h : g.ok) : (map.one g).ok := by
  intro xs e
  cases e with
  | insert i x => exact (map_insert g.f xs i x).symm
  | delete i => exact (map_remove g.f xs i).symm
  | update i d =>
    show run (editStructure cb) (map.edit g xs (.update i d)) (xs.map g.f) = (update ca xs i d).map g.f
    cases hx : xs[i]? with
    | none =>
      simp only [map.edit, hx]
      rw [update_past xs i (List.getElem?_eq_none_iff.mp hx)]
      rfl
    | some x =>
      simp only [map.edit, hx]
      exact map_update g h xs i x hx d

/-- `map.inc g` is correct, if `g` is. -/
theorem map_inc_ok {ca cb : EditStructure} (g : Inc ca cb) (h : g.ok) : (map.inc g).ok :=
  lift_ok (map.one g) (map_one_ok g h)

/-- One run then another maps the second from the list the first produced. -/
theorem dmap_append {ca cb : EditStructure} (g : Inc ca cb) (p q : List (Edit.of ca)) (xs : List ca.Value) :
    dmap g (p ++ q) xs = dmap g p xs ++ dmap g q (patch ca p xs) := by
  induction p generalizing xs with
  | nil => rfl
  | cons e t ih =>
    show map.edit g xs e ++ dmap g (t ++ q) (edit ca e xs) = (map.edit g xs e ++ dmap g t (edit ca e xs)) ++ _
    rw [ih, List.append_assoc]
    rfl

/-! ## Where edits act -/

def shape.edit {A DA : Type} : Edit A DA → Edit Unit Unit
  | .insert i _ => .insert i ()
  | .delete i => .delete i
  | .update i _ => .update i ()

/-- Where a run of edits acts: the edits with their values left out. -/
def shape {A DA : Type} (es : List (Edit A DA)) : List (Edit Unit Unit) :=
  es.map shape.edit

/-- `dmap` is local: it acts exactly where valid edits act. -/
theorem dmap_local {ca cb : EditStructure} (g : Inc ca cb) (es : List (Edit.of ca)) (xs : List ca.Value)
    (v : valid ca es xs) : shape (dmap g es xs) = shape es := by
  induction es generalizing xs with
  | nil => rfl
  | cons e t ih =>
    unfold shape at ih ⊢
    show (map.edit g xs e ++ dmap g t (edit ca e xs)).map shape.edit = (e :: t).map shape.edit
    cases e with
    | insert i x =>
      obtain ⟨_, vt⟩ := v
      simp [map.edit, shape.edit, edit, ih _ vt]
    | delete i =>
      obtain ⟨_, vt⟩ := v
      simp [map.edit, shape.edit, edit, ih _ vt]
    | update i d =>
      obtain ⟨hi, vt⟩ := v
      have hx : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
      simp [map.edit, hx, shape.edit, edit, ih _ vt]

theorem length_insert {A : Type} (xs : List A) (i : Nat) (x : A) (h : i ≤ xs.length) :
    (insert xs i x).length = xs.length + 1 := by
  induction xs generalizing i with
  | nil => rfl
  | cons y t ih => cases i <;> simp_all [insert]

/-- `dmap` keeps edits valid, if `g` is correct: valid edits give edits valid
for the mapped list. -/
theorem dmap_valid {ca cb : EditStructure} (g : Inc ca cb) (h : g.ok) (es : List (Edit.of ca))
    (xs : List ca.Value) (v : valid ca es xs) : valid cb (dmap g es xs) (xs.map g.f) := by
  induction es generalizing xs with
  | nil => trivial
  | cons e t ih =>
    cases e with
    | insert i x =>
      obtain ⟨hi, vt⟩ := v
      refine ⟨by simpa using hi, ?_⟩
      rw [← map_insert]
      exact ih _ vt
    | delete i =>
      obtain ⟨hi, vt⟩ := v
      refine ⟨by simpa using hi, ?_⟩
      rw [← map_remove]
      exact ih _ vt
    | update i d =>
      obtain ⟨hi, vt⟩ := v
      have hx : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
      show valid cb (map.edit g xs (.update i d) ++ dmap g t (update ca xs i d)) _
      simp only [map.edit, hx]
      refine ⟨by simpa using hi, ?_⟩
      show valid cb (dmap g t _) (update cb (xs.map g.f) i (g.df xs[i] d))
      rw [map_update g h xs i xs[i] hx d]
      exact ih _ vt

end Puri
