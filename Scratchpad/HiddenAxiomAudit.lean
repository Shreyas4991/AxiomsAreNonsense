import Scratchpad.HiddenAxiomLibrary

/-!
# Imported axiom audit bug: the misleading clean report

Run `lake build Scratchpad.HiddenAxiomLibrary` first, then
`lake env lean Scratchpad/HiddenAxiomAudit.lean`.

Lean 4.34.1 incorrectly reports NO axioms for both the imported `S9` and a
theorem whose statement uses it. The same type, queried in its defining
module, reports the custom `linearMergeCost` axiom and `Classical.choice`.
Querying the constructor below also exposes those dependencies.

What goes wrong: the axiom collector traverses a cycle between an inductive
type and its constructor. An unfinished traversal can be cached as an empty
dependency set and exported into the `.olean`. The importer trusts that
cached result instead of walking the declarations again.

This is a real false negative in dependency reporting, NOT a proof of False
without assumptions. `usesS9` proves only `S9 → True`; its hidden dependency
is in the type of its argument. The final control shows that actually deriving
False from the bad cost axiom still exposes that axiom in this example.

The regression checks intentionally capture the buggy behavior. If an upgrade
fixes the collector, the first two checks should fail with corrected reports.
This does not establish that Lax's own validation accepts such a submission.
-/

theorem usesS9 (_ : S9) : True := trivial

/-- info: 'S9' does not depend on any axioms -/
#guard_msgs in
#print axioms S9

/-- info: 'usesS9' does not depend on any axioms -/
#guard_msgs in
#print axioms usesS9

-- Control: the constructor exposes what the imported type's report omits.
/-- info: 'S9.mk' depends on axioms: [linearMergeCost, Classical.choice] -/
#guard_msgs in
#print axioms S9.mk

-- The hidden axiom really is inconsistent, rather than merely unproved.
theorem cost_axiom_is_inconsistent : False := by
  obtain ⟨C, bound⟩ := linearMergeCost
  have impossible : C + 1 ≤ C :=
    Nat.le_of_mul_le_mul_right (bound (C + 1)) (Nat.two_pow_pos (C + 1))
  exact Nat.not_le_of_lt (Nat.lt_succ_self C) impossible

/-- info: 'cost_axiom_is_inconsistent' depends on axioms: [linearMergeCost] -/
#guard_msgs in
#print axioms cost_axiom_is_inconsistent
