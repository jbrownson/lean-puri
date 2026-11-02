/-
The laws' axioms, checked as part of the build: each `#guard_msgs` fails the
build if what `#print axioms` says changes. Any `sorry` would show up as
`sorryAx`. The only axioms here are Lean's standard three: `propext`,
`Classical.choice` and `Quot.sound` (the last two come from tactics such as
`omega` and `simp`).
-/
import Puri.Scroll

open Puri

/-- info: 'Puri.lift_ok' does not depend on any axioms -/
#guard_msgs in #print axioms lift_ok

/-- info: 'Puri.whole_lift_ok' does not depend on any axioms -/
#guard_msgs in #print axioms whole_lift_ok

/-- info: 'Puri.recompute_ok' does not depend on any axioms -/
#guard_msgs in #print axioms recompute_ok

/-- info: 'Puri.diff_ok' does not depend on any axioms -/
#guard_msgs in #print axioms diff_ok

/-- info: 'Puri.map_inc_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms map_inc_ok

/-- info: 'Puri.dmap_local' depends on axioms: [propext] -/
#guard_msgs in #print axioms dmap_local

/-- info: 'Puri.dmap_valid' depends on axioms: [propext] -/
#guard_msgs in #print axioms dmap_valid

/-- info: 'Puri.Drawing.diff_ok' does not depend on any axioms -/
#guard_msgs in #print axioms Drawing.diff_ok

/-- info: 'Puri.draw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms draw_eq

/-- info: 'Puri.rows_apply_list' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rows_apply_list

/-- info: 'Puri.rows_apply_scroll' depends on axioms: [propext] -/
#guard_msgs in #print axioms rows_apply_scroll

/-- info: 'Puri.offset_apply_scroll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms offset_apply_scroll

/-- info: 'Puri.view_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms view_ok

/-- info: 'Puri.view_inc_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms view_inc_ok

/-- info: 'Puri.extent_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extent_ok
