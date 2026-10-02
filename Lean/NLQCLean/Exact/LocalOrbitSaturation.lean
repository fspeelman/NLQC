import NLQCLean.Exact.TargetWitness
import NLQCLean.Invariants.LocalOrbitSeparation

/-!
# Fixed-architecture exact targets are unions of full local orbits

Input local unitaries are absorbed into the encoders and output local
unitaries into the decoders. Register dimensions are unchanged, so the exact
target set of every fixed architecture is saturated by the double
local-unitary action.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

section Absorption

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

omit [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB] [Fintype ιA'] [Fintype ιB']
  [Fintype εA] [Fintype εB] [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
  [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB] in
/-- Input local operators pass through the resource insertion. -/
theorem localKronecker_mul_insertResource (SA : Matrix ιA ιA ℂ) (SB : Matrix ιB ιB ℂ)
    (η : ρA × ρB → ℂ) :
    ((SA ⊗ₖ (1 : Matrix ρA ρA ℂ)) ⊗ₖ (SB ⊗ₖ (1 : Matrix ρB ρB ℂ))) * insertResource ιA ιB η =
      insertResource ιA ιB η * (SA ⊗ₖ SB) := by
  ext ⟨⟨a, r⟩, ⟨b, s⟩⟩ ⟨a', b'⟩
  simp only [Matrix.mul_apply, insertResource, Matrix.of_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single a' (fun x _ hx => by simp [hx]) (by simp),
    Finset.sum_eq_single r (fun x _ hx => by simp [Ne.symm hx]) (by simp),
    Finset.sum_eq_single b' (fun x _ hx => by simp [hx]) (by simp),
    Finset.sum_eq_single s (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp only [ite_true, Finset.sum_ite_eq, Finset.mem_univ]
  ring

/-- Output local operators commute with the frozen environment insertion. -/
theorem kronecker_one_mul_insertVector (L : Matrix (ιA' × ιB') (ιA' × ιB') ℂ)
    (g : εA × εB → ℂ) :
    (L ⊗ₖ (1 : Matrix (εA × εB) (εA × εB) ℂ)) * insertVector (ιA' × ιB') g =
      insertVector (ιA' × ιB') g * L := by
  ext ⟨k, e⟩ k'
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [insertVector_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single k' (fun q _ hq => by simp [hq]) (by simp)]
  rw [Finset.sum_eq_single e (fun f _ hf => by simp [Ne.symm hf]) (by simp)]
  rw [Finset.sum_eq_single k (fun q _ hq => by simp [Ne.symm hq]) (by simp)]
  simp only [ite_true, one_mul, mul_one]
  ring

omit [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB] [DecidableEq ιA'] [DecidableEq ιB'] in
/-- Local output factors, regrouped by system and environment. -/
theorem kronecker_one_submatrix_outputRegroup (LA : Matrix ιA' ιA' ℂ) (LB : Matrix ιB' ιB' ℂ) :
    ((LA ⊗ₖ (1 : Matrix εA εA ℂ)) ⊗ₖ (LB ⊗ₖ (1 : Matrix εB εB ℂ))).submatrix
        (outputRegroup ιA' ιB' εA εB) (outputRegroup ιA' ιB' εA εB) =
      (LA ⊗ₖ LB) ⊗ₖ (1 : Matrix (εA × εB) (εA × εB) ℂ) := by
  ext ⟨⟨a, b⟩, ⟨e, f⟩⟩ ⟨⟨a', b'⟩, ⟨e', f'⟩⟩
  simp only [Matrix.submatrix_apply, outputRegroup_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases he : e = e' <;> by_cases hf : f = f' <;> simp [he, hf]

omit [DecidableEq ιA'] [DecidableEq ιB'] in
/-- **Absorption of local unitaries.** Precomposing the encoders and
postcomposing the decoders with local factors multiplies the regrouped global
isometry by the corresponding product factors. -/
theorem globalIsometryRegrouped_local (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (LA : Matrix ιA' ιA' ℂ) (LB : Matrix ιB' ιB' ℂ) (SA : Matrix ιA ιA ℂ) (SB : Matrix ιB ιB ℂ) :
    globalIsometryRegrouped η (VA * (SA ⊗ₖ (1 : Matrix ρA ρA ℂ)))
        (VB * (SB ⊗ₖ (1 : Matrix ρB ρB ℂ)))
        ((LA ⊗ₖ (1 : Matrix εA εA ℂ)) * DA) ((LB ⊗ₖ (1 : Matrix εB εB ℂ)) * DB) =
      ((LA ⊗ₖ LB) ⊗ₖ (1 : Matrix (εA × εB) (εA × εB) ℂ)) *
        globalIsometryRegrouped η VA VB DA DB * (SA ⊗ₖ SB) := by
  have hbij : Function.Bijective (outputRegroup ιA' ιB' εA εB) :=
    (outputRegroup ιA' ιB' εA εB).bijective
  rw [globalIsometryRegrouped_eq, globalIsometryRegrouped_eq, decoder, decoder,
    Matrix.mul_kronecker_mul, encodedState, encodedState, Matrix.mul_kronecker_mul,
    Matrix.mul_assoc (VA ⊗ₖ VB), localKronecker_mul_insertResource,
    Matrix.submatrix_mul _ _ (outputRegroup ιA' ιB' εA εB) (outputRegroup ιA' ιB' εA εB) id hbij,
    kronecker_one_submatrix_outputRegroup]
  simp only [Matrix.mul_assoc]

end Absorption

section Saturation

variable {d : ℕ}

/-- A unitary target is a coisometry and an isometry. -/
theorem kronecker_one_isIsometry {m ρ : Type*} [Fintype m] [Fintype ρ] [DecidableEq m]
    [DecidableEq ρ] {S : Matrix m m ℂ} (hS : S ∈ Matrix.unitaryGroup m ℂ) :
    IsIsometry (S ⊗ₖ (1 : Matrix ρ ρ ℂ)) :=
  (show IsIsometry S from Matrix.mem_unitaryGroup_iff'.mp hS).kronecker
    (show IsIsometry (1 : Matrix ρ ρ ℂ) by simp [IsIsometry])

/-- **Fixed-architecture saturation.** If `U` is exactly implemented with
dimension vector `s`, then so is every `(L_A ⊗ L_B) U (S_A ⊗ S_B)` with local
unitaries, with the same dimension vector. -/
theorem mem_targetExactWitnessSet_local (s : ForwardShape)
    {z : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × ShapeBlocks d s}
    (hz : z ∈ targetExactWitnessSet d s)
    {LA LB SA SB : Matrix (Fin d) (Fin d) ℂ}
    (hLA : LA ∈ Matrix.unitaryGroup (Fin d) ℂ) (hLB : LB ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSA : SA ∈ Matrix.unitaryGroup (Fin d) ℂ) (hSB : SB ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ((LA ⊗ₖ LB) * z.1 * (SA ⊗ₖ SB),
      (z.2.1, z.2.2.1, z.2.2.2.1 * (SA ⊗ₖ 1), z.2.2.2.2.1 * (SB ⊗ₖ 1),
        (LA ⊗ₖ 1) * z.2.2.2.2.2.1, (LB ⊗ₖ 1) * z.2.2.2.2.2.2)) ∈
      targetExactWitnessSet d s := by
  rcases hz with ⟨⟨hη, hVA, hVB, hDA, hDB⟩, hg, hU, hfreeze⟩
  have hL : LA ⊗ₖ LB ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ :=
    Matrix.kronecker_mem_unitary hLA hLB
  have hS : SA ⊗ₖ SB ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ :=
    Matrix.kronecker_mem_unitary hSA hSB
  refine ⟨⟨hη, hVA.mul (kronecker_one_isIsometry hSA), hVB.mul (kronecker_one_isIsometry hSB),
    ?_, ?_⟩, hg, ?_, ?_⟩
  · exact (kronecker_one_isIsometry hLA).mul hDA
  · exact (kronecker_one_isIsometry hLB).mul hDB
  · have hLU := Matrix.mem_unitaryGroup_iff.mp hL
    have hSU := Matrix.mem_unitaryGroup_iff.mp hS
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc (LA ⊗ₖ LB) * z.1 * (SA ⊗ₖ SB) * ((SA ⊗ₖ SB)ᴴ * (z.1ᴴ * (LA ⊗ₖ LB)ᴴ))
        = (LA ⊗ₖ LB) * (z.1 * ((SA ⊗ₖ SB) * (SA ⊗ₖ SB)ᴴ) * z.1ᴴ) * (LA ⊗ₖ LB)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [show (SA ⊗ₖ SB) * (SA ⊗ₖ SB)ᴴ = 1 from hSU, Matrix.mul_one, hU, Matrix.mul_one]
          exact hLU
  · rw [globalIsometryRegrouped_local, hfreeze, ← Matrix.mul_assoc,
      kronecker_one_mul_insertVector]
    simp only [Matrix.mul_assoc]

/-- The exact targets of one fixed architecture. -/
def exactTargets (d : ℕ) (s : ForwardShape) : Set (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  Prod.fst '' targetExactWitnessSet d s

/-- The exact target set of a fixed architecture contains the full local
orbit of each of its members. -/
theorem unitaryDoubleOrbit_subset_exactTargets (s : ForwardShape)
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hU : U ∈ exactTargets d s) :
    unitaryDoubleOrbit (Fin d) (Fin d) U ⊆ exactTargets d s := by
  obtain ⟨z, hz, rfl⟩ := hU
  rintro V ⟨L, ⟨LA, hLA, LB, hLB, rfl⟩, S, ⟨SA, hSA, SB, hSB, rfl⟩, rfl⟩
  exact ⟨_, mem_targetExactWitnessSet_local s hz hLA hLB hSA hSB, rfl⟩

end Saturation

end NLQCLean
