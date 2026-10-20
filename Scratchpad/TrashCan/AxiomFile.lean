module

/-!
## Module system doesn't keep axioms private

In this demo, we show that axioms don't stay unusable because they are marked private in a module. This is very well known to the lean community. But a good
demo regardless. For more details of how to use
this, see [Theorem2.lean](./Theorem2.lean)
-/
@[simp]
private axiom nonsenseAxiom : False

@[simp]
public theorem nonsenseTheorem : False := by simp
