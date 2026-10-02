import NLQCLean.Models.ClassicalCommunication.FiniteMixedCompression

/-!
# Finite-shape score reachability with free classical outcomes

The twelve shape entries enumerate resource registers, kept encoder systems,
quantum messages, classical outcomes, private instrument Kraus systems, and
final decoder environments, in that order. The resulting sets contain actual
finite protocols and common-map finite mixtures. Compression puts them in the
existing charged score-reachable sets. No Borel-alphabet or shared-randomness
scope, or arbitrary-register reindexing theorem, is asserted here.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix

/-- Twelve finite systems, with logical inputs and outputs of dimension `d`.
Slots `0,1` are resources; `2,3` are retained systems; `4,5` are quantum
messages; `6,7` are classical outcomes; `8,9` are private Kraus systems;
`10,11` are final private environments. -/
abbrev FinClassicalProtocol (d : ℕ) (s : Fin 12 → ℕ) :=
  FiniteClassicalProtocol (Fin d) (Fin d)
    (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
    (Fin (s 4)) (Fin (s 5)) (Fin (s 6)) (Fin (s 7))
    (Fin (s 8)) (Fin (s 9)) (Fin d) (Fin d) (Fin (s 10)) (Fin (s 11))

/-- The same twelve systems with each party outputting the full ordered PVM label. -/
abbrev FinClassicalPVMProtocol (d : ℕ) (s : Fin 12 → ℕ) :=
  FiniteClassicalProtocol (Fin d) (Fin d)
    (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
    (Fin (s 4)) (Fin (s 5)) (Fin (s 6)) (Fin (s 7))
    (Fin (s 8)) (Fin (s 9)) (Fin d × Fin d) (Fin d × Fin d)
    (Fin (s 10)) (Fin (s 11))

/-- Unitary score reachability by an actual pure finite-shape classical protocol. -/
def finitePureScoreReachable (d K : ℕ) (ε : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {U | ∃ s : Fin 12 → ℕ, ∃ P : FinClassicalProtocol d s,
    P.HasQuantumFootprint K ∧ 1 - ε ≤ scoreU (U : Matrix _ _ ℂ) P.operationalChannel}

/-- Unitary score reachability by an actual common-map finite mixed resource. -/
def finiteMixedScoreReachable (d K : ℕ) (ε : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {U | ∃ s : Fin 12 → ℕ, ∃ n : ℕ,
    ∃ m : MixedResource (Fin (s 0)) (Fin (s 1)) n,
    ∃ P : FinClassicalProtocol d s, P.HasMixedQuantumFootprint m K ∧
      1 - ε ≤ scoreU (U : Matrix _ _ ℂ) (P.mixedOperationalChannel m)}

/-- Joint-label PVM score reachability by an actual pure finite-shape protocol. -/
def finitePurePVMScoreReachable (d K : ℕ) (ε : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {M | ∃ s : Fin 12 → ℕ, ∃ P : FinClassicalPVMProtocol d s,
    P.HasQuantumFootprint K ∧ 1 - ε ≤ scorePVM (M : Matrix _ _ ℂ) P.operationalChannel}

/-- Joint-label PVM score reachability with common instruments and decoders
and an actual finite mixed decomposition, not a mixed-support dimension cap. -/
def finiteMixedPVMScoreReachable (d K : ℕ) (ε : ℝ) :
    Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ) :=
  {M | ∃ s : Fin 12 → ℕ, ∃ n : ℕ,
    ∃ m : MixedResource (Fin (s 0)) (Fin (s 1)) n,
    ∃ P : FinClassicalPVMProtocol d s, P.HasMixedQuantumFootprint m K ∧
      1 - ε ≤ scorePVM (M : Matrix _ _ ℂ) (P.mixedOperationalChannel m)}

/-- Finite pure score reachability transfers through compression. -/
theorem finitePureScoreReachable_subset_pureReachable {d K : ℕ} (hd : 0 < d) (ε : ℝ) :
    finitePureScoreReachable d K ε ⊆ pureReachable d (d ^ 4 * K ^ 5) ε := by
  rintro U ⟨s, P, hK, hscore⟩
  exact P.mem_pureReachable_of_quantumFootprint U hd hK hscore

/-- Mixed transfer uses a rank-capped actual component before finite compression. -/
theorem finiteMixedScoreReachable_subset_pureReachable {d K : ℕ} (hd : 0 < d) (ε : ℝ) :
    finiteMixedScoreReachable d K ε ⊆ pureReachable d (d ^ 4 * K ^ 5) ε := by
  rintro U ⟨s, n, m, P, hK, hscore⟩
  exact P.mem_pureReachable_of_mixedQuantumFootprint m U hd hK hscore

/-- Finite pure PVM transfer retains the existing two-sided correct-label score. -/
theorem finitePurePVMScoreReachable_subset_purePVMReachable {d K : ℕ}
    (hd : 0 < d) (ε : ℝ) :
    finitePurePVMScoreReachable d K ε ⊆ purePVMReachable d (d ^ 4 * K ^ 5) ε := by
  rintro M ⟨s, P, hK, hscore⟩
  exact P.mem_purePVMReachable_of_quantumFootprint M hd hK hscore

/-- Finite mixed PVM transfer has the same fifth-power charged budget. -/
theorem finiteMixedPVMScoreReachable_subset_purePVMReachable {d K : ℕ}
    (hd : 0 < d) (ε : ℝ) :
    finiteMixedPVMScoreReachable d K ε ⊆ purePVMReachable d (d ^ 4 * K ^ 5) ε := by
  rintro M ⟨s, n, m, P, hK, hscore⟩
  exact P.mem_purePVMReachable_of_mixedQuantumFootprint m M hd hK hscore

namespace FiniteClassicalProtocol

section PositiveInputs

variable {ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype σA] [Fintype σB] [Fintype ηA] [Fintype ηB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [Nonempty ιA] [Nonempty ιB]
variable (P : FiniteClassicalProtocol
  ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB)

/-- A unit resource and trace-preserving instruments on nonempty logical
inputs force positive resource rank and both quantum message dimensions. -/
theorem quantumFootprint_pos :
    0 < schmidtRank P.resource * Fintype.card μA * Fintype.card μB := by
  classical
  have hρ := P.resource_unit.card_pos
  simp only [Fintype.card_prod] at hρ
  have hρA := Nat.pos_of_mul_pos_right hρ
  have hρB := Nat.pos_of_mul_pos_left hρ
  have hιA : 0 < Fintype.card ιA := Fintype.card_pos
  have hιB : 0 < Fintype.card ιB := Fintype.card_pos
  have hencA : Fintype.card ιA * Fintype.card ρA ≤
      (Fintype.card κA * Fintype.card μA) * (Fintype.card σA * Fintype.card ηA) := by
    simpa only [Fintype.card_prod] using P.instrumentA.dilation_isometry.card_le
  have hencB : Fintype.card ιB * Fintype.card ρB ≤
      (Fintype.card κB * Fintype.card μB) * (Fintype.card σB * Fintype.card ηB) := by
    simpa only [Fintype.card_prod] using P.instrumentB.dilation_isometry.card_le
  have hmA : 0 < Fintype.card μA := Nat.pos_of_mul_pos_left
    (Nat.pos_of_mul_pos_right ((Nat.mul_pos hιA hρA).trans_le hencA))
  have hmB : 0 < Fintype.card μB := Nat.pos_of_mul_pos_left
    (Nat.pos_of_mul_pos_right ((Nat.mul_pos hιB hρB).trans_le hencB))
  exact Nat.mul_pos (Nat.mul_pos P.resource_unit.schmidtRank_pos hmA) hmB

/-- Budget zero is impossible for an actual finite classical protocol. -/
theorem not_hasQuantumFootprint_zero : ¬ P.HasQuantumFootprint 0 := by
  intro hK
  have h := (hasFootprint_iff 0 P.resource).mp hK
  exact (Nat.not_le_of_gt P.quantumFootprint_pos) h

/-- A common-map mixture cannot have quantum budget zero either: all actual
components are capped, and normalized convex weights force a component. -/
theorem not_hasMixedQuantumFootprint_zero {n : ℕ} (m : MixedResource ρA ρB n) :
    ¬ P.HasMixedQuantumFootprint m 0 := by
  intro hK
  let : NeZero n := ⟨Nat.ne_of_gt (mixedResource_component_count_pos m)⟩
  obtain ⟨k⟩ := (inferInstance : Nonempty (Fin n))
  exact (P.componentProtocol m k).not_hasQuantumFootprint_zero
    ((P.hasMixedQuantumFootprint_iff_componentwise m 0).mp hK k)

end PositiveInputs

end FiniteClassicalProtocol

theorem finitePureScoreReachable_zero_budget {d : ℕ} (hd : 0 < d) (ε : ℝ) :
    finitePureScoreReachable d 0 ε = ∅ := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro U ⟨s, P, hK, _⟩
  exact P.not_hasQuantumFootprint_zero hK

theorem finiteMixedScoreReachable_zero_budget {d : ℕ} (hd : 0 < d) (ε : ℝ) :
    finiteMixedScoreReachable d 0 ε = ∅ := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro U ⟨s, n, m, P, hK, _⟩
  exact P.not_hasMixedQuantumFootprint_zero m hK

theorem finitePurePVMScoreReachable_zero_budget {d : ℕ} (hd : 0 < d) (ε : ℝ) :
    finitePurePVMScoreReachable d 0 ε = ∅ := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro M ⟨s, P, hK, _⟩
  exact P.not_hasQuantumFootprint_zero hK

theorem finiteMixedPVMScoreReachable_zero_budget {d : ℕ} (hd : 0 < d) (ε : ℝ) :
    finiteMixedPVMScoreReachable d 0 ε = ∅ := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro M ⟨s, n, m, P, hK, _⟩
  exact P.not_hasMixedQuantumFootprint_zero m hK

end NLQCLean.ClassicalCommunication
