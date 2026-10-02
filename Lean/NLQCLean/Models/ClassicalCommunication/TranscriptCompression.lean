import NLQCLean.Models.ClassicalCommunication.CoherentConversion
import NLQCLean.Models.ClassicalCommunication.FiniteProtocolReindex
import NLQCLean.Models.ForwardCompression
import NLQCLean.LinearAlgebra.IsometryExtension

/-!
# The direct transcript parametrization of free-classical protocols

Step 5 of the proof of `thm:explicit` (`eq:explicit-quantum-variables`). A finite
free-classical protocol is put, without changing its operational channel, into the form
used by the transcript family:

* **purification**: each instrument branch keeps its Kraus label in the retained register,
  so every branch is a single operator `V_x`, and the decoders act trivially on the label,
  which joins their discarded environment;
* **retained compression**: each `V_x : ℂ^{dr} → K ⊗ ℂ^a` factors through an isometry
  `ℂ^{kA} → K` with one common `kA ≤ d r a` (the coefficient support of every branch has
  dimension at most `d r a`); the inclusion is absorbed into the conditional decoders;
* **environment compression**: each conditional decoder factors through an environment of
  one common dimension `eA ≤ d kA b`.

Branches need not be isometries individually; the instrument normalization
`Σ_x V_x† V_x = I` is preserved, and zero branches are allowed.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped Kronecker

attribute [local implicit_reducible] Matrix

private theorem sum_ite_irrel' {α V : Type*} [Fintype α] [AddCommMonoid V]
    (p : Prop) [Decidable p] (f : α → V) :
    (∑ a, if p then f a else 0) = if p then ∑ a, f a else 0 := by
  by_cases h : p <;> simp [h]

namespace FiniteKrausInstrument

variable {ι κ μ σ η : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype σ] [Fintype η]
variable [DecidableEq ι]

/-- One operator per outcome; the Kraus label joins the retained register. -/
def purify (I : FiniteKrausInstrument ι (κ × μ) σ η) :
    FiniteKrausInstrument ι ((κ × η) × μ) σ Unit where
  operator x _ := Matrix.of fun p i => I.operator x p.1.2 (p.1.1, p.2) i
  normalized := by
    rw [← I.normalized]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_unique]
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.sum_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_comm]

end FiniteKrausInstrument

/-- A decoder acting trivially on a label that joins its discarded environment. -/
def purifyDecoder {ιo ε κ η μ : Type*} [DecidableEq η] (D : Matrix (ιo × ε) (κ × μ) ℂ) :
    Matrix (ιo × (ε × η)) ((κ × η) × μ) ℂ :=
  Matrix.of fun p q => if p.2.2 = q.1.2 then D (p.1, p.2.1) (q.1.1, q.2) else 0

theorem purifyDecoder_isometry {ιo ε κ η μ : Type*} [Fintype ιo] [Fintype ε] [Fintype κ]
    [Fintype η] [Fintype μ] [DecidableEq κ] [DecidableEq η] [DecidableEq μ]
    {D : Matrix (ιo × ε) (κ × μ) ℂ} (hD : IsIsometry D) :
    IsIsometry (purifyDecoder (η := η) D) := by
  classical
  let e₁ : ιo × (ε × η) ≃ (ιo × ε) × η := (Equiv.prodAssoc ιo ε η).symm
  let e₂ : (κ × η) × μ ≃ (κ × μ) × η :=
    { toFun := fun q => ((q.1.1, q.2), q.1.2)
      invFun := fun q => ((q.1.1, q.2), q.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : purifyDecoder (η := η) D =
      (controlledMatrix (fun _ : η => D)).submatrix e₁ e₂ := by
    ext p q
    simp only [purifyDecoder, controlledMatrix, Matrix.of_apply, Matrix.submatrix_apply]
    rfl
  rw [h]
  exact (controlledMatrix_isometry _ fun _ => hD).submatrix_equiv _ _

namespace FiniteClassicalProtocol

variable {ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype σA] [Fintype σB] [Fintype ηA] [Fintype ηB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq σA] [DecidableEq σB] [DecidableEq ηA] [DecidableEq ηB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]
variable (P : FiniteClassicalProtocol
  ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB)

/-- **Purification.** Single-operator branches; Kraus labels kept and then discarded. -/
def purify : FiniteClassicalProtocol ιA ιB ρA ρB (κA × ηA) (κB × ηB) μA μB σA σB Unit Unit
    ιA' ιB' (εA × ηA) (εB × ηB) where
  resource := P.resource
  resource_unit := P.resource_unit
  instrumentA := P.instrumentA.purify
  instrumentB := P.instrumentB.purify
  decA x y := purifyDecoder (P.decA x y)
  decB x y := purifyDecoder (P.decB x y)
  decA_isometry x y := purifyDecoder_isometry (P.decA_isometry x y)
  decB_isometry x y := purifyDecoder_isometry (P.decB_isometry x y)

omit [DecidableEq σA] [DecidableEq σB] [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA]
  [DecidableEq εB] in
set_option maxHeartbeats 1600000 in
/-- The purified amplitude with environment labels `(u, e)` and `(v, f)` is the original
branch amplitude of the Kraus labels `e, f`. -/
theorem purify_branchAmplitude_apply (x : σA) (y : σB) (a : ιA') (b : ιB') (u : εA) (v : εB)
    (e : ηA) (f : ηB) (i : ιA × ιB) :
    P.purify.branchAmplitude x y () () ((a, (u, e)), (b, (v, f))) i =
      P.branchAmplitude x y e f ((a, u), (b, v)) i := by
  unfold branchAmplitude
  rw [globalIsometry_entry, globalIsometry_entry]
  simp only [purify, FiniteKrausInstrument.purify, purifyDecoder, Matrix.of_apply,
    Fintype.sum_prod_type]
  generalize P.decA x y = DA
  generalize P.decB x y = DB
  generalize P.instrumentA.operator x = VA
  generalize P.instrumentB.operator y = VB
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, sum_ite_irrel', Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

omit [DecidableEq σA] [DecidableEq σB] [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA]
  [DecidableEq εB] in
theorem purify_operationalChannel : P.purify.operationalChannel = P.operationalChannel := by
  unfold operationalChannel
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [Fintype.sum_unique]
  let G : ηA → ηB → Matrix ((ιA' × ιB') × (εA × εB)) (ιA × ιB) ℂ := fun e f =>
    (P.branchAmplitude x y e f).submatrix (outputRegroup ιA' ιB' εA εB) id
  have hslice : ∀ (u : εA) (e : ηA) (v : εB) (f : ηB),
      sliceAt ((P.purify.branchAmplitude x y () ()).submatrix
        (outputRegroup ιA' ιB' (εA × ηA) (εB × ηB)) id) ((u, e), (v, f)) =
      sliceAt (G e f) (u, v) := by
    intro u e v f
    ext p i
    exact P.purify_branchAmplitude_apply x y p.1 p.2 u v e f i
  let eqv : (εA × ηA) × (εB × ηB) ≃ ηA × (ηB × (εA × εB)) :=
    { toFun := fun w => (w.1.2, (w.2.2, (w.1.1, w.2.1)))
      invFun := fun z => ((z.2.2.1, z.1), (z.2.2.2, z.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simp only [channelOf_eq_sum_adConj]
  calc ∑ w, adConj (sliceAt ((P.purify.branchAmplitude x y () ()).submatrix
        (outputRegroup ιA' ιB' (εA × ηA) (εB × ηB)) id) w)
      = ∑ w : (εA × ηA) × (εB × ηB), adConj (sliceAt (G w.1.2 w.2.2) (w.1.1, w.2.1)) :=
        Finset.sum_congr rfl fun w _ => congrArg adConj (hslice w.1.1 w.1.2 w.2.1 w.2.2)
    _ = ∑ z : ηA × (ηB × (εA × εB)), adConj (sliceAt (G z.1 z.2.1) z.2.2) :=
        Fintype.sum_equiv eqv _ _ fun _ => rfl
    _ = _ := by simp only [Fintype.sum_prod_type, G]

end FiniteClassicalProtocol

section Compression

theorem gram_kronecker_one_mul {m n k μ : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype μ]
    [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq μ]
    {J : Matrix m k ℂ} (hJ : IsIsometry J) (B : Matrix (k × μ) n ℂ) :
    ((J ⊗ₖ (1 : Matrix μ μ ℂ)) * B)ᴴ * ((J ⊗ₖ (1 : Matrix μ μ ℂ)) * B) = Bᴴ * B := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (J ⊗ₖ _),
    (hJ.kronecker isIsometry_one).conjTranspose_mul_self, Matrix.one_mul]

variable {d r : ℕ} {κA κB μA μB σA σB εA εB ηA ηB : Type*}
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
variable [Fintype εA] [Fintype εB] [Fintype ηA] [Fintype ηB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB]
variable [DecidableEq ηA] [DecidableEq ηB]

/-- **Retained and environment compression.** A single-operator protocol has the same
operational channel as one with retained registers of dimension `kA ≤ d r a`, `kB ≤ d r b`
and decoder environments of dimension `eA ≤ d kA b`, `eB ≤ d kB a`. -/
theorem exists_compressed_transcript
    (P : FiniteClassicalProtocol (Fin d) (Fin d) (Fin r) (Fin r) κA κB μA μB σA σB Unit Unit
      (Fin d) (Fin d) εA εB) :
    ∃ kA kB eA eB : ℕ, kA ≤ d * r * Fintype.card μA ∧ kB ≤ d * r * Fintype.card μB ∧
      eA ≤ d * kA * Fintype.card μB ∧ eB ≤ d * kB * Fintype.card μA ∧
      ∃ Q : FiniteClassicalProtocol (Fin d) (Fin d) (Fin r) (Fin r) (Fin kA) (Fin kB) μA μB
          σA σB Unit Unit (Fin d) (Fin d) (Fin eA) (Fin eB),
        Q.resource = P.resource ∧ Q.operationalChannel = P.operationalChannel := by
  classical
  set kA := min (d * r * Fintype.card μA) (Fintype.card κA) with hkAdef
  set kB := min (d * r * Fintype.card μB) (Fintype.card κB) with hkBdef
  have hkA : min (Fintype.card (Fin d × Fin r) * Fintype.card μA) (Fintype.card κA) ≤ kA := by
    simp [kA]
  have hkB : min (Fintype.card (Fin d × Fin r) * Fintype.card μB) (Fintype.card κB) ≤ kB := by
    simp [kB]
  choose JA BA hJA hVA using fun x : σA =>
    exists_left_coefficient_factorization_of_le (P.instrumentA.operator x ()) hkA
      (min_le_right _ _)
  choose JB BB hJB hVB using fun y : σB =>
    exists_left_coefficient_factorization_of_le (P.instrumentB.operator y ()) hkB
      (min_le_right _ _)
  set eA := min (d * kA * Fintype.card μB) (Fintype.card εA) with heAdef
  set eB := min (d * kB * Fintype.card μA) (Fintype.card εB) with heBdef
  have heA : min (Fintype.card (Fin d) * Fintype.card (Fin kA × μB)) (Fintype.card εA) ≤ eA := by
    simp [eA, Nat.mul_assoc]
  have heB : min (Fintype.card (Fin d) * Fintype.card (Fin kB × μA)) (Fintype.card εB) ≤ eB := by
    simp [eB, Nat.mul_assoc]
  let DA0 : σA → σB → Matrix (Fin d × εA) (Fin kA × μB) ℂ := fun x y =>
    P.decA x y * (JA x ⊗ₖ (1 : Matrix μB μB ℂ))
  let DB0 : σA → σB → Matrix (Fin d × εB) (Fin kB × μA) ℂ := fun x y =>
    P.decB x y * (JB y ⊗ₖ (1 : Matrix μA μA ℂ))
  have hDA0 : ∀ x y, IsIsometry (DA0 x y) := fun x y =>
    (P.decA_isometry x y).mul ((hJA x).kronecker isIsometry_one)
  have hDB0 : ∀ x y, IsIsometry (DB0 x y) := fun x y =>
    (P.decB_isometry x y).mul ((hJB y).kronecker isIsometry_one)
  choose EA CA hEA hDA using fun x y =>
    exists_right_coefficient_factorization_of_le (DA0 x y) heA (min_le_right _ _)
  choose EB CB hEB hDB using fun x y =>
    exists_right_coefficient_factorization_of_le (DB0 x y) heB (min_le_right _ _)
  have hCA : ∀ x y, IsIsometry (CA x y) := fun x y =>
    ((isIsometry_one.kronecker (hEA x y)).mul_iff (CA x y)).mp (hDA x y ▸ hDA0 x y)
  have hCB : ∀ x y, IsIsometry (CB x y) := fun x y =>
    ((isIsometry_one.kronecker (hEB x y)).mul_iff (CB x y)).mp (hDB x y ▸ hDB0 x y)
  let instrA : FiniteKrausInstrument (Fin d × Fin r) (Fin kA × μA) σA Unit :=
    { operator := fun x _ => BA x
      normalized := by
        rw [← P.instrumentA.normalized]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ => ?_
        cases u
        rw [hVA x]
        exact (gram_kronecker_one_mul (hJA x) (BA x)).symm }
  let instrB : FiniteKrausInstrument (Fin d × Fin r) (Fin kB × μB) σB Unit :=
    { operator := fun y _ => BB y
      normalized := by
        rw [← P.instrumentB.normalized]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun u _ => ?_
        cases u
        rw [hVB y]
        exact (gram_kronecker_one_mul (hJB y) (BB y)).symm }
  let Q : FiniteClassicalProtocol (Fin d) (Fin d) (Fin r) (Fin r) (Fin kA) (Fin kB) μA μB
      σA σB Unit Unit (Fin d) (Fin d) (Fin eA) (Fin eB) :=
    { resource := P.resource
      resource_unit := P.resource_unit
      instrumentA := instrA
      instrumentB := instrB
      decA := CA
      decB := CB
      decA_isometry := hCA
      decB_isometry := hCB }
  refine ⟨kA, kB, eA, eB, min_le_left _ _, min_le_left _ _, min_le_left _ _, min_le_left _ _,
    Q, rfl, ?_⟩
  unfold FiniteClassicalProtocol.operationalChannel
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [Fintype.sum_unique]
  have hF : P.branchAmplitude x y () () =
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ EA x y) ⊗ₖ
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ EB x y)) * Q.branchAmplitude x y () () := by
    change NLQCLean.globalIsometry P.resource (P.instrumentA.operator x ())
        (P.instrumentB.operator y ()) (P.decA x y) (P.decB x y) =
      _ * NLQCLean.globalIsometry P.resource (BA x) (BB y) (CA x y) (CB x y)
    rw [hVA x, hVB y, globalIsometry_private_inclusions]
    change NLQCLean.globalIsometry P.resource (BA x) (BB y) (DA0 x y) (DB0 x y) = _
    rw [hDA x y, hDB x y]
    simp only [NLQCLean.globalIsometry, NLQCLean.decoder, Matrix.mul_kronecker_mul,
      Matrix.mul_assoc]
  have hFreg :
      (P.branchAmplitude x y () ()).submatrix (outputRegroup (Fin d) (Fin d) εA εB) id =
        ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ (EA x y ⊗ₖ EB x y)) *
          (Q.branchAmplitude x y () ()).submatrix
            (outputRegroup (Fin d) (Fin d) (Fin eA) (Fin eB)) id :=
    (congrArg (fun F : Matrix ((Fin d × εA) × (Fin d × εB)) (Fin d × Fin d) ℂ =>
      F.submatrix (outputRegroup (Fin d) (Fin d) εA εB) id) hF).trans
        (regroup_environment_inclusions (EA x y) (EB x y) _)
  rw [hFreg]
  exact (channelOf_environment_inclusion (EA x y ⊗ₖ EB x y)
    ((hEA x y).kronecker (hEB x y)) _).symm

/-- **The transcript representative.** A finite free-classical protocol on a resource of
rank-sized registers has the same operational channel as a single-operator protocol with
messages `Fin a`, `Fin b`, retained registers `kA ≤ d r a`, `kB ≤ d r b`, and decoder
environments `eA ≤ d kA b`, `eB ≤ d kB a`. The resource vector is unchanged. -/
theorem exists_transcript_representative
    (P : FiniteClassicalProtocol (Fin d) (Fin d) (Fin r) (Fin r) κA κB μA μB σA σB ηA ηB
      (Fin d) (Fin d) εA εB) :
    ∃ kA kB eA eB : ℕ, kA ≤ d * r * Fintype.card μA ∧ kB ≤ d * r * Fintype.card μB ∧
      eA ≤ d * kA * Fintype.card μB ∧ eB ≤ d * kB * Fintype.card μA ∧
      ∃ Q : FiniteClassicalProtocol (Fin d) (Fin d) (Fin r) (Fin r) (Fin kA) (Fin kB)
          (Fin (Fintype.card μA)) (Fin (Fintype.card μB)) σA σB Unit Unit (Fin d) (Fin d)
          (Fin eA) (Fin eB),
        Q.resource = P.resource ∧ Q.operationalChannel = P.operationalChannel := by
  classical
  obtain ⟨kA, kB, eA, eB, hkA, hkB, heA, heB, Q, hres, hchan⟩ :=
    exists_compressed_transcript P.purify
  refine ⟨kA, kB, eA, eB, hkA, hkB, heA, heB,
    Q.reindex (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
      (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm (Equiv.refl _) (Equiv.refl _)
      (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _), ?_, ?_⟩
  · funext p
    change Q.resource (p.1, p.2) = P.resource p
    rw [hres]
    rfl
  · rw [FiniteClassicalProtocol.operationalChannel_reindex, hchan,
      FiniteClassicalProtocol.purify_operationalChannel]

end Compression



end NLQCLean.ClassicalCommunication
