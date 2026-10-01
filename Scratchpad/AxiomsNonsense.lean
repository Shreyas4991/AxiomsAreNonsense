import Mathlib

/-!
# Five plausible interfaces with unchecked assumptions

Each section resembles a small library: definitions, an axiom standing in for
an unfinished helper lemma, and an ordinary downstream theorem. All five final
statements have no hypothesis arguments. Nevertheless, their proofs depend on
the helper axioms; a clean-looking statement does not
make a result unconditional. The `#print axioms` commands expose that distinction.

**Note** : `#print axioms` is meta code. It is not proven correct that it gets all axioms. If you instead stated explicit hypothesis, then lean's kernel checks conditional statements as such.

Run: `lake env lean Scratchpad/AxiomsNonsense.lean`.
-/

namespace AxiomsNonsense

/-- An eventual linear cost bound with constants uniform in the input size. -/
def IsLinear (cost : ℕ → ℕ) : Prop :=
  ∃ C N : ℕ, ∀ n, N ≤ n → cost n ≤ C * n

/-! ## 1. Reusing a scheduler's cost certificate -/
namespace MergeSort

-- On powers of two, this work summary charges one visit per element per level.
def mergeWork (n : ℕ) : ℕ := n * Nat.log2 n
-- A linear upper bound on span for parallel recursion with sequential merging.
def spanBudget (n : ℕ) : ℕ := 2 * n

/-- Transfer the scheduler's resource certificate to the execution cost. -/
axiom scheduler_bound (n : ℕ) : mergeWork n ≤ spanBudget n

-- A closed theorem: no runtime assumptions appear in its statement.
theorem mergesort_is_linear : IsLinear mergeWork := by
  refine ⟨2, 0, ?_⟩
  intro n _
  exact scheduler_bound n

#print axioms mergesort_is_linear

/-!
What goes wrong: the scheduler certificate bounds the critical path, but the
helper applies it to total sequential work. The proof downstream is ordinary
bound propagation. For `n = 8`, the concrete summaries already give work 24
and budget 16. More generally, at `n = 2^k` the work/input ratio is k, so no
uniform linear bound exists. Keep work and span distinct in the interface,
and prove any transfer using the actual execution model.
-/
end MergeSort

/-! ## 2. Packaging local cost estimates into an asymptotic bound -/
namespace MovingConstant

def LocalEstimate (cost : ℕ → ℕ) : Prop :=
  ∀ n, ∃ C : ℕ, cost n ≤ C * n

/-- Assemble per-input estimates into a complexity certificate. -/
axiom uniformize (cost : ℕ → ℕ) : LocalEstimate cost → IsLinear cost

def allPairsCost (n : ℕ) : ℕ := n * n

theorem all_pairs_is_linear : IsLinear allPairsCost := by
  apply uniformize
  intro n
  exact ⟨n, Nat.le_refl _⟩

#print axioms all_pairs_is_linear

/-!
What goes wrong: the local witness C may depend on n. In this proof it IS n.
The helper silently turns `∀ n, ∃ C` into a uniform `∃ C N, ∀ n ≥ N`.
The final theorem has no assumptions in its statement, although its axiom
report still contains `uniformize`. For any proposed C and N, the input
`C + N + 1` violates the bound. Require the constant before quantifying over
inputs; a collection of pointwise estimates is not a big-O certificate.
-/
end MovingConstant

/-! ## 3. Extracting a return guarantee from a verified specification -/
namespace VerifiedProcedure

abbrev Program := ℕ → Option ℕ

-- A partial input/output semantics: `none` means there is no returned result.
def PartialCorrect (p : Program) : Prop :=
  ∀ input result, p input = some result → result = input

/-- A procedure satisfying its input/output specification returns a result. -/
axiom specification_adequacy (p : Program) :
  PartialCorrect p → ∀ input, ∃ result, p input = some result

def lookup : Program := fun key => if key = 0 then none else some key

theorem lookup_specification : PartialCorrect lookup := by
  intro input result h
  by_cases hzero : input = 0
  · simp [lookup, hzero] at h
  · simpa [lookup, hzero, eq_comm] using h

theorem lookup_returns_on_every_input : ∀ input, ∃ result, lookup input = some result :=
  specification_adequacy lookup lookup_specification

#print axioms lookup_returns_on_every_input

/-!
What goes wrong: the specification checks results WHEN they exist. It says
nothing about whether a result exists, so `lookup_specification` is provable
even though key 0 has no result. The axiom upgrades partial correctness
to successful return. The final theorem presents that return guarantee with
no precondition. Prove termination/availability separately, or retain the
precondition that rules out unsuccessful inputs. This issue also arises when
`none` is used to model divergence rather than a failed lookup.
-/
end VerifiedProcedure

/-! ## 4. Applying an amplification lemma to repeated trials -/
namespace RepeatedTrials

-- Exact probability on a uniformly sampled Boolean seed.
def probability (event : Bool → Bool) : ℚ :=
  ((if event false then 1 else 0) + (if event true then 1 else 0)) / 2

/-- The probability of joint failure is the product of the failure probabilities. -/
axiom joint_failure (first second : Bool → Bool) :
  probability (fun seed => first seed && second seed) = probability first * probability second

def trialFails (seed : Bool) : Bool := seed

theorem repeated_error_at_most_quarter :
    probability (fun seed => trialFails seed && trialFails seed) ≤ 1 / 4 := by
  rw [joint_failure]
  norm_num [probability, trialFails]

#print axioms repeated_error_at_most_quarter

/-!
What goes wrong: the multiplication rule needs independence, which its axiom
signature omits. These two trials share their seed. Repeating them therefore
leaves the actual failure probability at 1/2, even though the closed theorem
advertises at most 1/4. Equal marginal probabilities are not evidence of
independence. Use a product sample space with independent seeds, or supply
and verify the independence hypothesis for the actual joint distribution.
-/
end RepeatedTrials

/-! ## 5. Proving that a packet buffer accommodates its payload -/
namespace PacketBuffer

abbrev Word := Fin 256

def add (a b : Word) : Word :=
  ⟨(a.val + b.val) % 256, Nat.mod_lt _ (by decide)⟩

/-- Move a word addition into the natural-number arithmetic used by bounds proofs. -/
axiom add_value (a b : Word) : (add a b).val = a.val + b.val

theorem packet_buffer_sufficient :
    ∀ payload header : Word, payload.val ≤ (add payload header).val := by
  intro payload header
  rw [add_value]
  exact Nat.le_add_right _ _

#print axioms packet_buffer_sufficient

/-!
What goes wrong: the conversion lemma drops modular reduction without a
no-overflow hypothesis. A payload of 255 and a header of 1 allocate a word
size of 0. The bounds proof looks like routine natural-number arithmetic,
and its theorem has no precondition, because the missing precondition was
lost upstream in `add_value`. Preserve the modulus or require the sum to
fit in the word before using this arithmetic conversion.
-/
end PacketBuffer

end AxiomsNonsense
