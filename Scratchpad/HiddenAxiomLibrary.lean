/-!
# Imported axiom audit bug: library side

Reproducer for https://github.com/leanprover/lean4/issues/15226, adapted to
hide a custom (and inconsistent) mergesort cost axiom. Tested on Lean 4.34.1.
The companion file is `Scratchpad/HiddenAxiomAudit.lean`.

On inputs of length `2^k`, the stub charges `k * 2^k` units of work. The axiom
claims a uniform linear bound. It is false: set `k = C + 1` and cancel `2^k`.
`pick` selects the alleged constant; `S9` stores an index bounded by it.

The short names below deliberately preserve a declaration order that triggers
the bug. The exported cache depends on hashed declaration names: renaming a
declaration or adding siblings may change whether the bug appears.

Build this file separately, then run the importer:

    lake build Scratchpad.HiddenAxiomLibrary
    lake env lean Scratchpad/HiddenAxiomAudit.lean

No custom elaborators, unchecked declarations, or forged diagnostic messages
are used. `#guard_msgs` asserts Lean's actual diagnostic output.
-/

axiom linearMergeCost : ∃ C : Nat, ∀ k : Nat, k * 2 ^ k ≤ C * 2 ^ k

noncomputable def pick : Nat := Classical.choose linearMergeCost

structure S9 where
  x : Fin (pick + 1)

-- Control: inside the defining module, the axiom is correctly reported.
/-- info: 'S9' depends on axioms: [linearMergeCost, Classical.choice] -/
#guard_msgs in
#print axioms S9
