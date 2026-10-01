import NLQCLean.Models.ClassicalCommunication.FiniteMixed
import NLQCLean.Models.ClassicalCommunication.BranchChannels
import NLQCLean.Models.ClassicalCommunication.TargetScores
import NLQCLean.Models.ProjectiveProbability
import NLQCLean.Models.ProjectiveMixedExactness
import Mathlib.Analysis.Matrix.Order

/-!
# Finite local POVMs and reported measurement outcomes

Two actual local POVMs act on the inputs and the respective resource shares.
A finite function combines their outcomes, including repeated reported labels.
Exchanging those outcomes gives an actual two-sided classical protocol with
one-dimensional quantum messages. The local Born probabilities are preserved.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder

attribute [local implicit_reducible] Matrix

/-- An actual finite POVM on its original finite system. Zero effects and
repeated final labels are permitted. -/
structure FinitePOVM (ι σ : Type*) [Fintype ι] [Fintype σ] [DecidableEq ι] where
  effect : σ → Matrix ι ι ℂ
  positive : ∀ x, (effect x).PosSemidef
  normalized : ∑ x, effect x = 1

namespace FinitePOVM

variable {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq ι]

/-- Positivity supplies a physical square-root measurement operator. -/
theorem exists_measurementOperator (E : FinitePOVM ι σ) (x : σ) :
    ∃ A : Matrix ι ι ℂ, Aᴴ * A = E.effect x := by
  obtain ⟨A, hA, _, hAA⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    (E.positive x).isHermitian (QuasispectrumRestricts.nnreal_of_nonneg (E.positive x).nonneg)
  refine ⟨A, ?_⟩
  change star A * A = E.effect x
  rw [hA.star_eq]
  exact hAA

/-- A chosen square-root operator, with its Gram identity proved from the POVM. -/
noncomputable def measurementOperator (E : FinitePOVM ι σ) (x : σ) : Matrix ι ι ℂ :=
  Classical.choose (E.exists_measurementOperator x)

theorem measurementOperator_gram (E : FinitePOVM ι σ) (x : σ) :
    (E.measurementOperator x)ᴴ * E.measurementOperator x = E.effect x :=
  Classical.choose_spec (E.exists_measurementOperator x)

/-- The actual local instrument retains the measured system and sends a
one-dimensional quantum register. The POVM outcome is the classical message. -/
noncomputable def instrument (E : FinitePOVM ι σ) :
    FiniteKrausInstrument ι (ι × Unit) σ Unit where
  operator := fun x _ p i => E.measurementOperator x p.1 i
  normalized := by
    have hgram (x : σ) :
        (Matrix.of fun p : ι × Unit => fun i : ι => E.measurementOperator x p.1 i)ᴴ *
          (Matrix.of fun p : ι × Unit => fun i : ι => E.measurementOperator x p.1 i) =
            E.effect x := by
      ext i j
      simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_unique] using
        congrArg (fun M : Matrix ι ι ℂ => M i j) (E.measurementOperator_gram x)
    simp only [Fintype.sum_unique]
    calc
      _ = ∑ x, E.effect x := Finset.sum_congr rfl fun x _ => hgram x
      _ = 1 := E.normalized

end FinitePOVM

/-- A final decoder computes the common reported label and retains its
entire local measured system as discarded garbage. -/
def reportedLabelDecoder {κ δ : Type*} [DecidableEq κ] [DecidableEq δ]
    (i : δ) : Matrix (δ × κ) (κ × Unit) ℂ :=
  fun p q => if p.1 = i ∧ p.2 = q.1 then 1 else 0

theorem reportedLabelDecoder_isometry {κ δ : Type*}
    [Fintype κ] [Fintype δ] [DecidableEq κ] [DecidableEq δ] (i : δ) :
    IsIsometry (reportedLabelDecoder (κ := κ) i) := by
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [reportedLabelDecoder, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, ite_and]
  · have hkept : p.1 ≠ q.1 := by
      intro h
      exact hpq (Prod.ext h (Subsingleton.elim _ _))
    simp [reportedLabelDecoder, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, ite_and, hpq, Ne.symm hkept]

/-- Actual finite local measurements and their joint outcome function.
The shared resource is supplied separately, so the same measurements apply
to every component of a common-map mixed state. -/
structure FiniteLocalizationScheme
    (ιA ιB ρA ρB σA σB δ : Type*)
    [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
    [Fintype σA] [Fintype σB]
    [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB] where
  povmA : FinitePOVM (ιA × ρA) σA
  povmB : FinitePOVM (ιB × ρB) σB
  report : σA → σB → δ

namespace FiniteLocalizationScheme

variable {ιA ιB ρA ρB σA σB δ : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype σA] [Fintype σB] [Fintype δ]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq δ]
variable (L : FiniteLocalizationScheme ιA ιB ρA ρB σA σB δ)

/-- The finite label-exchange implementation of the local POVMs and f(x,y).
Both outgoing quantum registers are Unit; the resource is unchanged. -/
noncomputable def protocol (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) :
    FiniteClassicalProtocol ιA ιB ρA ρB (ιA × ρA) (ιB × ρB) Unit Unit
      σA σB Unit Unit δ δ (ιA × ρA) (ιB × ρB) where
  resource := γ
  resource_unit := hγ
  instrumentA := L.povmA.instrument
  instrumentB := L.povmB.instrument
  decA := fun x y => reportedLabelDecoder (L.report x y)
  decB := fun x y => reportedLabelDecoder (L.report x y)
  decA_isometry := fun _ _ => reportedLabelDecoder_isometry _
  decB_isometry := fun _ _ => reportedLabelDecoder_isometry _

/-- Its quantum-only footprint is exactly the Schmidt rank of the resource. -/
theorem protocol_hasQuantumFootprint_iff (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) (K : ℕ) :
    (L.protocol γ hγ).HasQuantumFootprint K ↔ schmidtRank γ ≤ K := by
  simp only [FiniteClassicalProtocol.HasQuantumFootprint, hasFootprint_iff,
    protocol, Fintype.card_unique, mul_one]

/-- The actual local measurement operator on the resource-inserted input. -/
noncomputable def jointOperator (γ : ρA × ρB → ℂ) (x : σA) (y : σB) :
    Matrix ((ιA × ρA) × (ιB × ρB)) (ιA × ιB) ℂ :=
  (L.povmA.measurementOperator x ⊗ₖ L.povmB.measurementOperator y) *
    insertResource ιA ιB γ

/-- The Born probability of the pair of local POVM outcomes, before
postprocessing. It is defined directly by the POVM effects. -/
noncomputable def outcomeProbability (γ : ρA × ρB → ℂ)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) (x : σA) (y : σB) : ℂ :=
  trace ((L.povmA.effect x ⊗ₖ L.povmB.effect y) *
    (insertResource ιA ιB γ * X * (insertResource ιA ιB γ)ᴴ))

omit [Fintype δ] [DecidableEq δ] in
/-- Retaining the measured systems as garbage gives the POVM Born probability. -/
theorem trace_jointOperator_eq_outcomeProbability
    (γ : ρA × ρB → ℂ) (X : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (x : σA) (y : σB) :
    trace (L.jointOperator γ x y * X * (L.jointOperator γ x y)ᴴ) =
      L.outcomeProbability γ X x y := by
  let I := insertResource ιA ιB γ
  let A := L.povmA.measurementOperator x ⊗ₖ L.povmB.measurementOperator y
  have hA : Aᴴ * A = L.povmA.effect x ⊗ₖ L.povmB.effect y := by
    dsimp only [A]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      L.povmA.measurementOperator_gram, L.povmB.measurementOperator_gram]
  change trace ((A * I) * X * (A * I)ᴴ) = _
  rw [Matrix.trace_mul_cycle, Matrix.conjTranspose_mul]
  calc
    _ = trace (Iᴴ * (Aᴴ * A) * (I * X)) := by simp only [Matrix.mul_assoc]
    _ = trace ((Aᴴ * A) * (I * X) * Iᴴ) := (Matrix.trace_mul_cycle _ _ _).symm
    _ = L.outcomeProbability γ X x y := by
      rw [hA, Matrix.mul_assoc]
      rfl

set_option maxHeartbeats 400000 in
/-- On each branch both outputs are precisely f(x,y); its garbage block is
the actual local POVM operator, independently of the input state. -/
theorem protocol_branchAmplitude_apply (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (x : σA) (y : σB) (a b : δ) (u : ιA × ρA) (v : ιB × ρB) (i : ιA × ιB) :
    (L.protocol γ hγ).branchAmplitude x y () () ((a, u), (b, v)) i =
      if a = L.report x y ∧ b = L.report x y then L.jointOperator γ x y (u, v) i else 0 := by
  rw [FiniteClassicalProtocol.branchAmplitude, globalIsometry_entry]
  dsimp only [protocol, FinitePOVM.instrument]
  by_cases ha : a = L.report x y <;> by_cases hb : b = L.report x y <;>
    simp [reportedLabelDecoder, ha, hb, jointOperator, Matrix.mul_apply,
      Matrix.kroneckerMap_apply, insertResource_apply, Fintype.sum_prod_type,
      ite_mul, mul_ite, mul_assoc]

/-- Every state probability is preserved, with mismatched output labels zero. -/
theorem protocol_branch_outcomeProbability (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) (x : σA) (y : σB) (a b : δ) :
    outcomeProb ((L.protocol γ hγ).branchAmplitude x y () ()) X a b =
      if a = L.report x y ∧ b = L.report x y then L.outcomeProbability γ X x y else 0 := by
  have hblock : outcomeBlock ((L.protocol γ hγ).branchAmplitude x y () ()) a b =
      if a = L.report x y ∧ b = L.report x y then L.jointOperator γ x y else 0 := by
    ext e i
    change (L.protocol γ hγ).branchAmplitude x y () () ((a, e.1), (b, e.2)) i = _
    rw [L.protocol_branchAmplitude_apply]
    split_ifs <;> rfl
  unfold outcomeProb
  rw [hblock]
  split_ifs
  · exact L.trace_jointOperator_eq_outcomeProbability γ X x y
  · simp

/-- Sum the actual POVM probabilities over all pairs assigned to a label.
No injectivity of the reporting function is required. -/
noncomputable def reportedProbability (γ : ρA × ρB → ℂ)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) (i : δ) : ℂ :=
  ∑ x, ∑ y, if L.report x y = i then L.outcomeProbability γ X x y else 0

/-- The operational joint output channel has the reported Born probabilities
on its diagonal and always produces equal labels. -/
theorem protocol_operationalChannel_diag
    (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) (a b : δ) :
    ((L.protocol γ hγ).operationalChannel X) (a, b) (a, b) =
      if a = b then L.reportedProbability γ X a else 0 := by
  simp only [FiniteClassicalProtocol.operationalChannel, LinearMap.sum_apply,
    Matrix.sum_apply, Fintype.sum_unique, channelOf_regrouped_diag,
    L.protocol_branch_outcomeProbability]
  by_cases hab : a = b
  · subst b
    simp [and_self, reportedProbability, eq_comm]
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro y _
    have h : ¬ (a = L.report x y ∧ b = L.report x y) :=
      fun h => hab (h.1.trans h.2.symm)
    exact if_neg h

/-- The finite localization success probability on the ordered target basis. -/
noncomputable def successScore
    (L : FiniteLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB))
    (γ : ρA × ρB → ℂ) (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) : ℝ :=
  (Fintype.card (ιA × ιB) : ℝ)⁻¹ * ∑ i, (L.reportedProbability γ (pvmProj M i) i).re

/-- The protocol's two-sided correct-label score is exactly the actual
finite localization success probability, with its d² input normalization. -/
theorem protocol_scorePVM
    (L : FiniteLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB))
    (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    scorePVM M (L.protocol γ hγ).operationalChannel = L.successScore γ M := by
  simp [scorePVM, L.protocol_operationalChannel_diag, successScore]

/-- Exact localization reproduces every input-state Born probability. -/
def IsExact
    (L : FiniteLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB))
    (γ : ρA × ρB → ℂ) (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) : Prop :=
  ∀ X : Matrix (ιA × ιB) (ιA × ιB) ℂ, IsState X →
    ∀ i, L.reportedProbability γ X i = trace (pvmProj M i * X)

end FiniteLocalizationScheme

end NLQCLean.ClassicalCommunication

namespace NLQCLean.MixedResource

open Matrix
open scoped ComplexOrder MatrixOrder

attribute [local implicit_reducible] Matrix

variable {ρA ρB : Type*} [Fintype ρA] [Fintype ρB]
variable [DecidableEq ρA] [DecidableEq ρB]

/-- The actual density matrix of a finite pure-state decomposition. -/
noncomputable def densityMatrix {n : ℕ} (m : MixedResource ρA ρB n) :
    Matrix (ρA × ρB) (ρA × ρB) ℂ :=
  ∑ k, (m.weight k : ℂ) • pureState (m.component k)

/-- Every finite density matrix has a normalized pure-state decomposition
on its original two resource registers. -/
noncomputable def ofState (S : Matrix (ρA × ρB) (ρA × ρB) ℂ) (hS : IsState S) :
    MixedResource ρA ρB (Fintype.card (ρA × ρB)) where
  weight := fun k => hS.1.isHermitian.eigenvalues ((Fintype.equivFin (ρA × ρB)).symm k)
  weight_nonneg := fun _ => hS.1.eigenvalues_nonneg _
  weight_sum := by
    rw [Equiv.sum_comp]
    have h : (∑ i, (hS.1.isHermitian.eigenvalues i : ℂ)) = 1 :=
      hS.1.isHermitian.trace_eq_sum_eigenvalues.symm.trans hS.2
    exact_mod_cast h
  component := fun k => pvmColumn
    (hS.1.isHermitian.eigenvectorUnitary : Matrix (ρA × ρB) (ρA × ρB) ℂ)
    ((Fintype.equivFin (ρA × ρB)).symm k)
  component_unit := fun _ => isUnitVector_pvmColumn
    (Matrix.mem_unitaryGroup_iff'.mp hS.1.isHermitian.eigenvectorUnitary.property) _

/-- The spectral decomposition represents the supplied state exactly. -/
theorem densityMatrix_ofState
    (S : Matrix (ρA × ρB) (ρA × ρB) ℂ) (hS : IsState S) :
    (ofState S hS).densityMatrix = S := by
  ext i j
  simp only [densityMatrix, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, ofState, pureState_apply, pvmColumn_apply]
  rw [Equiv.sum_comp (Fintype.equivFin (ρA × ρB)).symm
    (fun k => (hS.1.isHermitian.eigenvalues k : ℂ) *
      ((hS.1.isHermitian.eigenvectorUnitary : Matrix (ρA × ρB) (ρA × ρB) ℂ) i k *
        star ((hS.1.isHermitian.eigenvectorUnitary : Matrix (ρA × ρB) (ρA × ρB) ℂ) j k)))]
  have h := congrArg (fun M : Matrix (ρA × ρB) (ρA × ρB) ℂ => M i j)
    hS.1.isHermitian.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.mul_diagonal, Matrix.star_apply, Function.comp_apply] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  let a : ℂ := (hS.1.isHermitian.eigenvalues k : ℂ)
  let b : ℂ := (hS.1.isHermitian.eigenvectorUnitary : Matrix (ρA × ρB) (ρA × ρB) ℂ) i k
  let c : ℂ := star ((hS.1.isHermitian.eigenvectorUnitary : Matrix (ρA × ρB) (ρA × ρB) ℂ) j k)
  change a * (b * c) = b * a * c
  calc
    _ = (a * b) * c := (mul_assoc a b c).symm
    _ = (b * a) * c := congrArg (fun z : ℂ => z * c) (mul_comm a b)

/-- A Schmidt-number cap is existence of a finite decomposition whose every
component has the rank cap; it imposes no support bound on the density matrix. -/
def HasSchmidtNumberLE (S : Matrix (ρA × ρB) (ρA × ρB) ℂ) (r : ℕ) : Prop :=
  ∃ (n : ℕ) (m : MixedResource ρA ρB n), m.densityMatrix = S ∧ m.schmidtNumberLE r

end NLQCLean.MixedResource

namespace NLQCLean.ClassicalCommunication.FiniteLocalizationScheme

open Matrix
open scoped Kronecker

variable {ιA ιB ρA ρB σA σB δ : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype σA] [Fintype σB] [Fintype δ]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq δ]
variable (L : FiniteLocalizationScheme ιA ιB ρA ρB σA σB δ)

/-- Tensor the input with the shared density matrix, grouped by laboratory. -/
noncomputable def inputDensity
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    (S : Matrix (ρA × ρB) (ρA × ρB) ℂ) :
    Matrix ((ιA × ρA) × (ιB × ρB)) ((ιA × ρA) × (ιB × ρB)) ℂ :=
  fun p q => X (p.1.1, p.2.1) (q.1.1, q.2.1) * S (p.1.2, p.2.2) (q.1.2, q.2.2)

omit [Fintype ρA] [Fintype ρB] [DecidableEq ρA] [DecidableEq ρB] in
/-- Pure-state insertion is exactly the tensor-product input state. -/
theorem insertResource_mul_eq_inputDensity
    (γ : ρA × ρB → ℂ) (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    insertResource ιA ιB γ * X * (insertResource ιA ιB γ)ᴴ =
      inputDensity X (pureState γ) := by
  ext p q
  simp [inputDensity, Matrix.mul_apply, Matrix.conjTranspose_apply,
    insertResource_apply, Fintype.sum_prod_type, mul_ite, ite_mul,
    apply_ite (starRingEnd ℂ)]
  ring

/-- Direct Born probability of the local POVMs with a shared density matrix. -/
noncomputable def stateOutcomeProbability
    (S : Matrix (ρA × ρB) (ρA × ρB) ℂ)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) (x : σA) (y : σB) : ℂ :=
  trace ((L.povmA.effect x ⊗ₖ L.povmB.effect y) * inputDensity X S)

omit [Fintype δ] [DecidableEq δ] in
/-- Pure-resource probabilities agree with the direct density formula. -/
theorem stateOutcomeProbability_pureState
    (γ : ρA × ρB → ℂ) (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) (x : σA) (y : σB) :
    L.stateOutcomeProbability (pureState γ) X x y = L.outcomeProbability γ X x y := by
  rw [stateOutcomeProbability, ← insertResource_mul_eq_inputDensity]
  rfl

omit [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]
  [DecidableEq ρA] [DecidableEq ρB] in
/-- The input tensor and regrouping are linear in the resource state. -/
theorem inputDensity_densityMatrix {n : ℕ} (m : MixedResource ρA ρB n)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    inputDensity X m.densityMatrix =
      ∑ k, (m.weight k : ℂ) • inputDensity X (pureState (m.component k)) := by
  ext p q
  simp only [inputDensity, MixedResource.densityMatrix, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [Fintype δ] [DecidableEq δ] in
/-- Every local-outcome probability is affine in the actual density matrix. -/
theorem stateOutcomeProbability_densityMatrix {n : ℕ} (m : MixedResource ρA ρB n)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) (x : σA) (y : σB) :
    L.stateOutcomeProbability m.densityMatrix X x y =
      ∑ k, (m.weight k : ℂ) * L.outcomeProbability (m.component k) X x y := by
  simp only [stateOutcomeProbability, inputDensity_densityMatrix,
    Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [← L.stateOutcomeProbability_pureState (m.component k) X x y]
  rfl

/-- Reported Born probability for an arbitrary shared density matrix. -/
noncomputable def stateReportedProbability
    (S : Matrix (ρA × ρB) (ρA × ρB) ℂ)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) (i : δ) : ℂ :=
  ∑ x, ∑ y, if L.report x y = i then L.stateOutcomeProbability S X x y else 0

/-- The common-map mixture uses the same POVMs and reporting function. -/
noncomputable def mixedReportedProbability {n : ℕ} (m : MixedResource ρA ρB n)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) (i : δ) : ℂ :=
  ∑ k, (m.weight k : ℂ) * L.reportedProbability (m.component k) X i

omit [Fintype δ] in
/-- Reporting duplicated labels preserves the density-matrix probability. -/
theorem stateReportedProbability_densityMatrix {n : ℕ} (m : MixedResource ρA ρB n)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) (i : δ) :
    L.stateReportedProbability m.densityMatrix X i = L.mixedReportedProbability m X i := by
  simp only [stateReportedProbability, mixedReportedProbability, reportedProbability,
    stateOutcomeProbability_densityMatrix, Finset.mul_sum]
  have hxy (x : σA) (y : σB) :
      (if L.report x y = i then
        ∑ k, (m.weight k : ℂ) * L.outcomeProbability (m.component k) X x y else 0) =
      ∑ k, (m.weight k : ℂ) *
        (if L.report x y = i then L.outcomeProbability (m.component k) X x y else 0) := by
    by_cases h : L.report x y = i <;> simp [h]
  simp only [hxy]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  conv_rhs => rw [Finset.sum_comm]

/-- Resource components change neither POVMs nor reporting maps. -/
theorem protocol_componentProtocol (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    {n : ℕ} (m : MixedResource ρA ρB n) (k : Fin n) :
    (L.protocol γ hγ).componentProtocol m k =
      L.protocol (m.component k) (m.component_unit k) := rfl

/-- The mixed quantum footprint is precisely the Schmidt-number cap. -/
theorem protocol_hasMixedQuantumFootprint_iff (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    {n : ℕ} (m : MixedResource ρA ρB n) (r : ℕ) :
    (L.protocol γ hγ).HasMixedQuantumFootprint m r ↔ m.schmidtNumberLE r := by
  rw [FiniteClassicalProtocol.hasMixedQuantumFootprint_iff_rank_bound]
  simp only [Fintype.card_unique, mul_one]
  constructor
  · rintro ⟨R, hR, hRr⟩
    exact hR.mono hRr
  · intro hr
    exact ⟨r, hr, le_rfl⟩

/-- The honest mixed output channel reproduces every Born probability
and produces unequal reported labels with probability zero. -/
theorem protocol_mixedOperationalChannel_diag
    (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) {n : ℕ} (m : MixedResource ρA ρB n)
    (X : Matrix (ιA × ιB) (ιA × ιB) ℂ) (a b : δ) :
    ((L.protocol γ hγ).mixedOperationalChannel m X) (a, b) (a, b) =
      if a = b then L.mixedReportedProbability m X a else 0 := by
  simp only [FiniteClassicalProtocol.mixedOperationalChannel, LinearMap.sum_apply,
    LinearMap.smul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    L.protocol_componentProtocol, L.protocol_operationalChannel_diag]
  by_cases h : a = b <;> simp [h, mixedReportedProbability]

/-- Mixed localization success with common local measurements. -/
noncomputable def mixedSuccessScore
    (L : FiniteLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB))
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) : ℝ :=
  ∑ k, m.weight k * L.successScore (m.component k) M

/-- Mixed success equals the honest two-sided joint-label score. -/
theorem protocol_mixedScorePVM
    (L : FiniteLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB))
    (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    scorePVM M ((L.protocol γ hγ).mixedOperationalChannel m) = L.mixedSuccessScore m M := by
  rw [← pvmScoreRealLinear_apply, FiniteClassicalProtocol.linearScore_mixedOperationalChannel]
  simp only [L.protocol_componentProtocol, pvmScoreRealLinear_apply, L.protocol_scorePVM]
  rfl

/-- Success probability defined directly from the actual shared density matrix. -/
noncomputable def stateSuccessScore
    (L : FiniteLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB))
    (S : Matrix (ρA × ρB) (ρA × ρB) ℂ)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) : ℝ :=
  (Fintype.card (ιA × ιB) : ℝ)⁻¹ *
    ∑ i, (L.stateReportedProbability S (pvmProj M i) i).re

/-- The finite mixed score is the Born success probability of its actual density matrix. -/
theorem stateSuccessScore_densityMatrix
    (L : FiniteLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB))
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    L.stateSuccessScore m.densityMatrix M = L.mixedSuccessScore m M := by
  let k : Fin n := ⟨0, mixedResource_component_count_pos m⟩
  have h := L.protocol_mixedScorePVM (m.component k) (m.component_unit k) m M
  simpa [scorePVM, L.protocol_mixedOperationalChannel_diag, stateSuccessScore,
    L.stateReportedProbability_densityMatrix] using h

/-- Every-input exact localization for a finite common-map mixed resource. -/
def IsMixedExact
    (L : FiniteLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB))
    {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) : Prop :=
  ∀ X : Matrix (ιA × ιB) (ιA × ιB) ℂ, IsState X →
    ∀ i, L.mixedReportedProbability m X i = trace (pvmProj M i * X)

/-- Every-input exact localization for an arbitrary shared density matrix. -/
def IsStateExact
    (L : FiniteLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB))
    (S : Matrix (ρA × ρB) (ρA × ρB) ℂ)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) : Prop :=
  ∀ X : Matrix (ιA × ιB) (ιA × ιB) ℂ, IsState X →
    ∀ i, L.stateReportedProbability S X i = trace (pvmProj M i * X)

/-- Exact mixed localization induces the original two-sided channel task,
including zero total probability of unequal labels. -/
theorem protocol_twoSidedExactChannel_of_isMixedExact
    (L : FiniteLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB))
    (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ) {n : ℕ} (m : MixedResource ρA ρB n)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hex : L.IsMixedExact m M) :
    TwoSidedExactChannel ((L.protocol γ hγ).mixedOperationalChannel m) M := by
  constructor
  · intro X hX i
    rw [L.protocol_mixedOperationalChannel_diag, if_pos rfl]
    exact hex X hX i
  · intro X _
    apply Finset.sum_eq_zero
    intro p hp
    have hneq := (Finset.mem_filter.mp hp).2
    rcases p with ⟨a, b⟩
    rw [L.protocol_mixedOperationalChannel_diag, if_neg hneq]

/-- Exact pure localization induces the original joint channel task. -/
theorem protocol_twoSidedExactChannel_of_isExact
    (L : FiniteLocalizationScheme ιA ιB ρA ρB σA σB (ιA × ιB))
    (γ : ρA × ρB → ℂ) (hγ : IsUnitVector γ)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hex : L.IsExact γ M) :
    TwoSidedExactChannel (L.protocol γ hγ).operationalChannel M := by
  constructor
  · intro X hX i
    rw [L.protocol_operationalChannel_diag, if_pos rfl]
    exact hex X hX i
  · intro X _
    apply Finset.sum_eq_zero
    intro p hp
    have hneq := (Finset.mem_filter.mp hp).2
    rcases p with ⟨a, b⟩
    rw [L.protocol_operationalChannel_diag, if_neg hneq]

end NLQCLean.ClassicalCommunication.FiniteLocalizationScheme
