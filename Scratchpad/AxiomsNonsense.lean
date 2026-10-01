import Mathlib
import Scratchpad.LeaderElectionAxioms

/-!
# Five failures from unchecked interfaces

These examples compose library contracts into stronger claims. The final
statements have no hypothesis arguments, but their proofs depend on custom
axioms. Each section isolates a different missing condition. The fifth case
is implemented in `LeaderElectionAxioms.lean`; its two contracts could also
originate in separate library files.

These are illustrative examples, not findings about laxarchive. Definitions
and cost summaries are deliberately small. Dependency reports distinguish
assumed contracts from the supporting lemmas proved here.

Run `lake build Scratchpad.LeaderElectionAxioms`, then
`lake env lean Scratchpad/AxiomsNonsense.lean`.
-/

namespace AxiomsNonsense

/-! ## 1. Amortized bounds for a persistent queue -/
namespace PersistentQueue
structure Charge where
  work : ℕ
  before : ℕ
  after : ℕ

def amortized (s : Charge) : ℤ := s.work + s.after - s.before

def totalWork (trace : List Charge) : ℕ := (trace.map Charge.work).sum

/-- Convert operation charges and initial credit into a total work bound. -/
axiom telescoping (first : Charge) (rest : List Charge) :
  (totalWork (first :: rest) : ℤ) ≤
    ((first :: rest).map amortized).sum + first.before

-- Reverse n pending elements, then remove one; the potential drops from n to 0.
def dequeue (n : ℕ) : Charge := ⟨n + 1, n, 0⟩

theorem dequeue_charge (n : ℕ) : amortized (dequeue n) = 1 := by
  simp [amortized, dequeue]

theorem repeated_dequeue_linear :
    ∃ C : ℕ, ∀ n, totalWork (List.replicate (n + 1) (dequeue n)) ≤ C * (n + 1) := by
  refine ⟨2, fun n => ?_⟩
  have h := telescoping (dequeue n) (List.replicate n (dequeue n))
  have charges : ((dequeue n :: List.replicate n (dequeue n)).map amortized).sum = n + 1 := by
    simp [dequeue_charge, List.sum_replicate]
    ring
  rw [charges] at h
  have bound : (totalWork (List.replicate (n + 1) (dequeue n)) : ℤ) ≤ 2 * (n + 1) := by
    rw [List.replicate_succ]
    dsimp only [dequeue] at h ⊢
    linarith
  exact_mod_cast bound

-- Control: this is the cost the certificate claims to bound.
theorem actual_work (n : ℕ) :
    totalWork (List.replicate (n + 1) (dequeue n)) = (n + 1) ^ 2 := by
  simp [totalWork, dequeue, List.sum_replicate, pow_two]
/-!
Each dequeue has a valid charge of 1. Persistence permits all calls to reuse
one original queue, so the same credit is spent repeatedly. Telescoping needs
adjacent potential values to agree; this interface omits that condition.
The resulting linear certificate covers work that is provably quadratic.
-/
#print axioms repeated_dequeue_linear
end PersistentQueue

/-! ## 2. Composing two secrecy guarantees -/
namespace ReusedKey

def probability (event : Bool → Bool) : ℚ :=
  ((if event false then 1 else 0) + (if event true then 1 else 0)) / 2

def SameLaw {α : Type} (X Y : Bool → α) : Prop :=
  ∀ test : α → Bool, probability (fun k => test (X k)) = probability (fun k => test (Y k))

/-- Compose distributional equivalences of two components. -/
axiom parallel_composition {α β : Type} (X X' : Bool → α) (Y Y' : Bool → β) :
  SameLaw X X' → SameLaw Y Y' →
    SameLaw (fun k => (X k, Y k)) (fun k => (X' k, Y' k))

theorem rekey {α : Type} (f : Bool → α) : SameLaw f (fun k => f (!k)) := by
  intro test
  simp [probability, add_comm]

theorem complement (event : Bool → Bool) :
    probability (fun k => !(event k)) = 1 - probability event := by
  cases h₀ : event false <;> cases h₁ : event true <;>
    norm_num [probability, h₀, h₁]

-- Encrypt a known zero bit and a secret bit with the same one-bit pad.
def transcript (secret key : Bool) : Bool × Bool := (key, Bool.xor key secret)

def success (guess : Bool × Bool → Bool) : ℚ :=
  (probability (fun k => !(guess (transcript false k))) +
    probability (fun k => guess (transcript true k))) / 2

theorem every_attacker_is_unbiased : ∀ guess, success guess = 1 / 2 := by
  intro guess
  have marginal : SameLaw (fun k : Bool => k) (fun k : Bool => !k) := rekey id
  have joint := parallel_composition id id id (fun k => !k) (fun _ => rfl) marginal
  have observed : probability (fun k => guess (transcript false k)) =
      probability (fun k => guess (transcript true k)) := by
    simpa [transcript] using joint guess
  unfold success
  rw [complement, observed]
  ring

theorem xor_attack_succeeds : success (fun c => Bool.xor c.1 c.2) = 1 := by
  norm_num [success, probability, transcript]
/-!
Each ciphertext separately has a secret-independent distribution. Their pair
does not: XOR cancels the reused pad. The proof derives an attacker success
rate of 1/2 from marginal equivalence, while direct calculation gives 1.
Composition requires control of the joint randomness, not just the marginals.
-/
#print axioms every_attacker_is_unbiased
end ReusedKey

/-! ## 3. Taking a monotone limit of verified deciders -/
namespace LimitDecider
open Nat.Partrec (Code)
open Nat.Partrec.Code

def Accepted (fuel : ℕ) (code : Code) : Prop := (evaln fuel code 0).isSome = true

/-- Decidability is preserved by an increasing sequence of acceptance predicates. -/
axiom monotone_limit (p : ℕ → Code → Prop)
    (step : ∀ n c, p n c → p (n + 1) c)
    (deciders : ∀ n, ComputablePred (p n)) : ComputablePred (fun c => ∃ n, p n c)

theorem accepted_computable (fuel : ℕ) : ComputablePred (Accepted fuel) := by
  have h := Primrec.option_isSome.to_comp.comp
    (primrec_evaln.to_comp.comp ((Computable.const fuel).pair Computable.id |>.pair (Computable.const 0)))
  unfold Accepted
  apply Computable.computablePred
  simpa using h

theorem halting_is_computable : ComputablePred (fun c : Code => (eval c 0).Dom) := by
  have monotone : ∀ n c, Accepted n c → Accepted (n + 1) c := by
    intro n c h
    obtain ⟨value, hv⟩ := Option.isSome_iff_exists.mp h
    apply Option.isSome_iff_exists.mpr
    exact ⟨value, evaln_mono (Nat.le_succ n) hv⟩
  apply (monotone_limit Accepted monotone accepted_computable).of_eq
  intro c
  constructor
  · rintro ⟨fuel, h⟩
    obtain ⟨value, hv⟩ := Option.isSome_iff_exists.mp h
    exact (evaln_sound hv).1
  · intro h
    obtain ⟨fuel, hv⟩ := evaln_complete.mp (Part.get_mem h)
    exact ⟨fuel, Option.isSome_iff_exists.mpr ⟨_, hv⟩⟩
/-!
Every bounded evaluator is computable, and acceptance increases with fuel.
Nevertheless, the limit is the halting predicate. A negative answer requires
knowing that no later bound will accept. Pointwise stabilization supplies no
computable stopping criterion; the closure axiom confuses decision with search.
-/
#print axioms halting_is_computable
end LimitDecider

/-! ## 4. Transferring termination through an abstraction -/
namespace Stuttering
abbrev State := ℕ × Bool

def tick (s : State) : State := if s.2 then (s.1 - 1, false) else (s.1, true)
def Step (next current : State) : Prop := next = tick current

/-- Transfer termination along a simulation allowing abstract stuttering. -/
axiom termination_transfer {A B : Type} (concrete : A → A → Prop)
    (abstract : B → B → Prop) (view : A → B) (terminates : WellFounded abstract)
    (simulation : ∀ s t, concrete t s → view t = view s ∨ abstract (view t) (view s)) :
    WellFounded concrete

theorem machine_terminates : WellFounded Step := by
  apply termination_transfer Step (· < ·) Prod.fst Nat.lt_wfRel.wf
  rintro ⟨n, phase⟩ next rfl
  cases phase with
  | false => exact Or.inl rfl
  | true =>
    by_cases h : n = 0
    · left; simp [tick, h]
    · right; dsimp [tick]; omega
theorem terminal_cycle : tick (tick (0, false)) = (0, false) := rfl

/-!
The simulation proof is valid: each step decreases the counter or preserves
its abstract state. At counter zero, however, the hidden phase alternates
forever. Termination transfer additionally requires ruling out infinite
stuttering; abstract well-foundedness alone does not establish progress.
-/
#print axioms machine_terminates
end Stuttering

/-!
## 5. Unique leader selection and rotation equivariance

See `LeaderElectionAxioms.lean`. Separate models satisfy each contract. Their
incompatibility follows by rotating a uniform input, transporting the elected
position, and applying uniqueness. This case explicitly derives the conflict
between two axioms; the preceding four end at the claimed application theorem.
-/

end AxiomsNonsense
