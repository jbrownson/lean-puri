/-
Edits to any value: a port of `ilc/change/change.bend` and its laws.
-/

namespace Puri

/-- How values are edited: values of type `Value`, edits of type `Edit`, and
`apply`, which applies one. These are the edits a type supplies; they needn't
get from every value to every other. `runs` and `whole` add ways to get
further. -/
structure EditStructure where
  Value : Type
  Edit : Type
  apply : Edit → Value → Value

/-- One edit gets from any value to any other, and which edit it is. -/
def reaches (ce : EditStructure) : Type :=
  (a b : ce.Value) → { d : ce.Edit // ce.apply d a = b }

/-- A change structure: an edit structure, with the proof that one edit gets
from any value to any other. -/
structure ChangeStructure where
  edits : EditStructure
  reach : reaches edits

/-- The edits of values that have none of their own. -/
def none (A : Type) : EditStructure :=
  ⟨A, Empty, fun e _ => nomatch e⟩

/-- The value a run of edits leaves, applied in order. -/
def run (ce : EditStructure) : List ce.Edit → ce.Value → ce.Value
  | [], a => a
  | e :: t, a => run ce t (ce.apply e a)

/-- Runs of `ce`'s edits, applied in order: no edits leaves a value as it
is, and one run then another is the two joined. -/
abbrev runs (ce : EditStructure) : EditStructure :=
  ⟨ce.Value, List ce.Edit, run ce⟩

/-- Running joined runs runs the first, then the second. -/
theorem run_append (ce : EditStructure) (xs ys : List ce.Edit) (a : ce.Value) :
    run ce (xs ++ ys) a = run ce ys (run ce xs a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons e t ih => exact ih _

/-- An edit of a value: a whole new one, or one of its own edits. -/
inductive Whole (ce : EditStructure) where
  | replace (x : ce.Value)
  | apply (e : ce.Edit)

def whole.apply (ce : EditStructure) : Whole ce → ce.Value → ce.Value
  | .replace x, _ => x
  | .apply e, a => ce.apply e a

/-- `ce`'s edits, and replacing the whole value. -/
abbrev whole (ce : EditStructure) : EditStructure :=
  ⟨ce.Value, Whole ce, whole.apply ce⟩

/-- `whole ce`, which is a change structure whatever `ce` is: replacing gets
from any value to any other. -/
def whole.changeStructure (ce : EditStructure) : ChangeStructure :=
  ⟨whole ce, fun _ b => ⟨.replace b, rfl⟩⟩

/-- An incremental function, from values edited as `ca` says to values
edited as `cb` says: a function `f`, and its derivative `df`, which gives the
edit to `f`'s result from a value and the value's edit. -/
structure Inc (ca cb : EditStructure) where
  f : ca.Value → cb.Value
  df : ca.Value → ca.Edit → cb.Edit

/-- `g`'s derivative is correct: applying its edit to `f a` gives `f` of the
edited value. -/
def Inc.ok {ca cb : EditStructure} (g : Inc ca cb) : Prop :=
  ∀ a d, cb.apply (g.df a d) (g.f a) = g.f (ca.apply d a)

/-- `lift`'s derivative, for a run of edits from the value before them: `g`'s
run for each edit, joined in order. -/
def lift.run {ca cb : EditStructure} (g : Inc ca (runs cb)) : List ca.Edit → ca.Value → List cb.Edit
  | [], _ => []
  | e :: t, a => g.df a e ++ lift.run g t (ca.apply e a)

/-- Lifts `g`, whose derivative gives a run for one edit, to an `Inc` whose
derivative handles runs. -/
def lift {ca cb : EditStructure} (g : Inc ca (runs cb)) : Inc (runs ca) (runs cb) :=
  ⟨g.f, fun a es => lift.run g es a⟩

/-- Lifting a correct `Inc` gives a correct one. -/
theorem lift_ok {ca cb : EditStructure} (g : Inc ca (runs cb)) (h : g.ok) : (lift g).ok := by
  intro a es
  induction es generalizing a with
  | nil => rfl
  | cons e t ih =>
    show run cb (g.df a e ++ lift.run g t (ca.apply e a)) (g.f a) = g.f (run ca t (ca.apply e a))
    rw [run_append]
    exact (congrArg (run cb (lift.run g t (ca.apply e a))) (h a e)).trans (ih _)

/-- `whole.lift`'s derivative: replacing the input replaces the result with
`f` of the new value, and an edit gives `g`'s edit. -/
def whole.lift.df {ca cb : EditStructure} (g : Inc ca cb) : ca.Value → Whole ca → Whole cb
  | _, .replace x => .replace (g.f x)
  | a, .apply e => .apply (g.df a e)

/-- Lifts `g` to values that can also be replaced. -/
def whole.lift {ca cb : EditStructure} (g : Inc ca cb) : Inc (whole ca) (whole cb) :=
  ⟨g.f, whole.lift.df g⟩

theorem whole_lift_ok {ca cb : EditStructure} (g : Inc ca cb) (h : g.ok) : (whole.lift g).ok := by
  intro a w
  cases w with
  | replace x => rfl
  | apply e => exact h a e

/-- `f`, with the derivative that recomputes: whatever the edit, replace the
result. -/
def recompute {ca cb : EditStructure} (f : ca.Value → cb.Value) : Inc ca (whole cb) :=
  ⟨f, fun a e => .replace (f (ca.apply e a))⟩

theorem recompute_ok {ca cb : EditStructure} (f : ca.Value → cb.Value) : (recompute (cb := cb) f).ok :=
  fun _ _ => rfl

end Puri
