import Mathlib

/-!
# Unique leader selection and rotation equivariance

The two axioms below could be declared in different files: a protocol library
exports a unique-leader guarantee; a symmetry library exports equivariance.
Each contract has a model separately. Their conjunction fails on a uniform
initial state, where rotating the ring cannot change the observed input.
-/

namespace AxiomsNonsense.LeaderElection

abbrev State := Fin 3 → Bool

def next (i : Fin 3) : Fin 3 := ⟨(i.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
def rotate (s : State) : State := fun i => s (next i)
def UniqueLeader (run : State → State) : Prop := ∀ s, ∃! i, run s i = true
def Equivariant (run : State → State) : Prop := ∀ s, run (rotate s) = rotate (run s)

structure Protocol where
  run : State → State
  elects : UniqueLeader run

-- Contract supplied by the protocol library.
axiom protocol : Protocol

-- Contract supplied by the symmetry library for the same protocol.
axiom rotation_equivariance : Equivariant protocol.run

-- Selecting position 0 satisfies unique election.
theorem uniqueness_has_model : ∃ run, UniqueLeader run := by
  refine ⟨fun _ i => decide (i = 0), fun _ => ?_⟩
  exact ⟨0, rfl, fun i hi => of_decide_eq_true hi⟩

-- Preserving the input satisfies rotation equivariance.
theorem equivariance_has_model : ∃ run, Equivariant run := ⟨id, fun _ => rfl⟩

theorem contracts_conflict : False := by
  let initial : State := fun _ => false
  have unchanged : rotate initial = initial := rfl
  have fixed : protocol.run initial = rotate (protocol.run initial) := by
    simpa only [unchanged] using rotation_equivariance initial
  obtain ⟨leader, elected, unique⟩ := protocol.elects initial
  have neighbor : protocol.run initial (next leader) = true := by
    have same := congrFun fixed leader
    exact same.symm.trans elected
  have impossible : next leader = leader := unique (next leader) neighbor
  fin_cases leader <;> norm_num [next, Fin.ext_iff] at impossible

/-!
Equivariance forces the output to retain the input's rotational symmetry.
A unique selected position breaks that symmetry. Deterministic election
therefore needs an asymmetry, such as distinguished identifiers; choosing a
fixed position and claiming rotation equivariance cannot be combined.
-/

#print axioms uniqueness_has_model
#print axioms equivariance_has_model
#print axioms contracts_conflict

end AxiomsNonsense.LeaderElection
