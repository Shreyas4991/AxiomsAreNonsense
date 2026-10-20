module

import Scratchpad.TrashCan.Theorem1

/-!

This file contains a theorem proved by an axiom that is marked private.
This is all known to anyone who understands the module system, but I thought
it might be better to demonstrate this anyway.

-/

theorem thm2 : False := by simp[thm1]

#print axioms thm2
