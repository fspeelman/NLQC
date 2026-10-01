import NLQCLean.Models.Metrics
import NLQCLean.Models.ClassicalCommunication.CoherentConversion
import NLQCLean.Models.ForwardReindex

/-!
# Diamond contraction under physical input and output maps

Partial trace contracts the trace norm on every complex matrix, by the
operator-dual formula and tensoring a test operator with the identity.
Actual isometric Stinespring matrices therefore contract every amplified
trace norm. The resulting diamond-error inequality retains the factor one
half and the supremum over all finite ancillas, without restricting inputs
to Hermitian matrices or positive states.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

section PartialTrace

variable {κ ε : Type*} [Fintype κ] [Fintype ε]
variable [DecidableEq κ] [DecidableEq ε]

omit [DecidableEq κ] in
/-- The adjoint of partial trace is tensoring a test matrix with the identity. -/
theorem frobInner_ptraceB (B : Matrix κ κ ℂ)
    (X : Matrix (κ × ε) (κ × ε) ℂ) :
    frobInner B (ptraceB κ ε X) = frobInner (B ⊗ₖ (1 : Matrix ε ε ℂ)) X := by
  simp [frobInner, ptraceB_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Finset.mul_sum, apply_ite, ite_mul]
  change (∑ i : κ, ∑ j : κ, ∑ e : ε, star (B i j) * X (i, e) (j, e)) =
    ∑ i : κ, ∑ e : ε, ∑ j : κ, star (B i j) * X (i, e) (j, e)
  exact Finset.sum_congr rfl (fun i _ =>
    Finset.sum_comm (f := fun j e => star (B i j) * X (i, e) (j, e)))

/-- Partial trace is trace-norm contractive for every matrix, not only states. -/
theorem traceNorm_ptraceB_le (X : Matrix (κ × ε) (κ × ε) ℂ) :
    traceNorm (ptraceB κ ε X) ≤ traceNorm X := by
  apply traceNorm_le
  intro B hB
  rw [frobInner_ptraceB]
  exact norm_frobInner_le_traceNorm X (B ⊗ₖ (1 : Matrix ε ε ℂ))
    ((opNorm_kronecker_one_le B).trans hB)

end PartialTrace

section Stinespring

variable {ι κ ε : Type*} [Fintype ι] [Fintype κ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]

/-- An actual isometric dilation gives a trace-norm contraction on all matrices. -/
theorem traceNorm_channelOf_le {F : Matrix (κ × ε) ι ℂ}
    (hF : IsIsometry F) (X : Matrix ι ι ℂ) :
    traceNorm (channelOf F X) ≤ traceNorm X := by
  rw [channelOf_apply]
  exact (traceNorm_ptraceB_le _).trans (by
    rw [hF.traceNorm_mul_adjoint_eq, hF.traceNorm_mul_eq])

end Stinespring

section AmplificationComposition

variable {ι κ ν α : Type*} [Fintype ι] [Fintype κ] [Fintype α]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq α]

/-- Amplification respects actual linear-map composition in every finite ancilla. -/
theorem amplify_comp (Ψ : Matrix κ κ ℂ →ₗ[ℂ] Matrix ν ν ℂ)
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (X : Matrix (ι × α) (ι × α) ℂ) :
    amplify (Ψ.comp Φ) α X = amplify Ψ α (amplify Φ α X) := by
  ext p q
  rw [amplify_apply_block, amplify_apply_block]
  have hblock : (fun k l => amplify Φ α X (k, p.2) (l, q.2)) =
      Φ (fun i j => X (i, p.2) (j, q.2)) := by
    ext k l
    exact amplify_apply_block Φ X (k, p.2) (l, q.2)
  rw [hblock]
  rfl

end AmplificationComposition

/-- Keep the ancilla with the output while retaining the original environment. -/
def stinespringAncillaRegroup (κ ε α : Type*) :
    ((κ × α) × ε) ≃ ((κ × ε) × α) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv p := by rcases p with ⟨⟨k, a⟩, e⟩; rfl
  right_inv p := by rcases p with ⟨⟨k, e⟩, a⟩; rfl

/-- The genuine tensor extension of a dilation, with its output regrouped. -/
def amplifyStinespring {ι κ ε : Type*} (F : Matrix (κ × ε) ι ℂ)
    (α : Type*) [DecidableEq α] : Matrix ((κ × α) × ε) (ι × α) ℂ :=
  (F ⊗ₖ (1 : Matrix α α ℂ)).submatrix (stinespringAncillaRegroup κ ε α) id

section AmplifiedStinespring

variable {ι κ ε α : Type*}
variable [Fintype ι] [Fintype κ] [Fintype ε] [Fintype α]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ε] [DecidableEq α]

omit [DecidableEq κ] [DecidableEq ε] in
/-- Tensoring and regrouping an actual dilation preserves its isometry. -/
theorem IsIsometry.amplifyStinespring {F : Matrix (κ × ε) ι ℂ}
    (hF : IsIsometry F) : IsIsometry (amplifyStinespring F α) :=
  (hF.kronecker isIsometry_one).submatrix_equiv
    (stinespringAncillaRegroup κ ε α) (Equiv.refl (ι × α))

omit [Fintype ι] [Fintype κ] [Fintype ε] [Fintype α]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ε] in
/-- Environment slices of the tensor extension are the extended Kraus matrices. -/
theorem sliceAt_amplifyStinespring (F : Matrix (κ × ε) ι ℂ) (e : ε) :
    sliceAt (amplifyStinespring F α) e = sliceAt F e ⊗ₖ (1 : Matrix α α ℂ) := by
  ext p q
  rfl

omit [Fintype κ] [DecidableEq κ] [DecidableEq ε] in
/-- Amplification is exactly the channel of the explicit tensor dilation. -/
theorem amplify_channelOf (F : Matrix (κ × ε) ι ℂ)
    (X : Matrix (ι × α) (ι × α) ℂ) :
    amplify (channelOf F) α X = channelOf (amplifyStinespring F α) X := by
  have hF : channelOf F = ClassicalCommunication.krausMap (sliceAt F) :=
    ClassicalCommunication.channelOf_eq_sum_adConj F
  rw [hF, ClassicalCommunication.amplify_krausMap,
    ClassicalCommunication.channelOf_eq_sum_adConj, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro e _
  rw [ClassicalCommunication.amplify_adConj, sliceAt_amplifyStinespring]
  rfl

/-- Every finite amplification of an actual physical channel contracts trace norm. -/
theorem traceNorm_amplify_channelOf_le {F : Matrix (κ × ε) ι ℂ}
    (hF : IsIsometry F) (X : Matrix (ι × α) (ι × α) ℂ) :
    traceNorm (amplify (channelOf F) α X) ≤ traceNorm X := by
  rw [amplify_channelOf]
  exact traceNorm_channelOf_le hF.amplifyStinespring X

end AmplifiedStinespring

section AmplifiedInputIsometry

variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq α]

/-- Isometric input inclusion preserves the trace norm in every finite ancilla. -/
theorem traceNorm_amplify_adConj_isometry {E : Matrix κ ι ℂ}
    (hE : IsIsometry E) (X : Matrix (ι × α) (ι × α) ℂ) :
    traceNorm (amplify (adConj E) α X) = traceNorm X := by
  rw [ClassicalCommunication.amplify_adConj]
  have hEA : IsIsometry (E ⊗ₖ (1 : Matrix α α ℂ)) := hE.kronecker isIsometry_one
  rw [hEA.traceNorm_mul_adjoint_eq, hEA.traceNorm_mul_eq]

end AmplifiedInputIsometry

section DiamondContraction

variable {τ ι κ ν ε : Type*}
variable [Fintype τ] [Fintype ι] [Fintype κ] [Fintype ν] [Fintype ε]
variable [DecidableEq τ] [DecidableEq ι] [DecidableEq κ]
variable [DecidableEq ν] [DecidableEq ε]

/-- Physical output decoding and isometric input restriction contract the full
all-ancilla diamond norm of an arbitrary linear map. -/
theorem diamondNorm_stinespring_isometry_sandwich_le
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    {E : Matrix ι τ ℂ} (hE : IsIsometry E)
    {D : Matrix (ν × ε) κ ℂ} (hD : IsIsometry D) :
    diamondNorm ((channelOf D).comp (Φ.comp (adConj E))) ≤ diamondNorm Φ := by
  apply diamondNorm_le
  intro a X hX
  rw [amplify_comp, amplify_comp]
  apply (traceNorm_amplify_channelOf_le hD _).trans
  apply traceNorm_amplify_fin_le_diamondNorm
  rwa [traceNorm_amplify_adConj_isometry hE]

/-- The same physical pre/postprocessing contracts the normalized diamond error,
with its original factor one half and no restriction on ancillary inputs. -/
theorem diamondError_stinespring_isometry_sandwich_le
    (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    {E : Matrix ι τ ℂ} (hE : IsIsometry E)
    {D : Matrix (ν × ε) κ ℂ} (hD : IsIsometry D) :
    diamondError ((channelOf D).comp (Φ.comp (adConj E)))
      ((channelOf D).comp (Ψ.comp (adConj E))) ≤ diamondError Φ Ψ := by
  have hsub : (channelOf D).comp (Φ.comp (adConj E)) -
      (channelOf D).comp (Ψ.comp (adConj E)) =
      (channelOf D).comp ((Φ - Ψ).comp (adConj E)) := by
    ext X p q
    simp [LinearMap.comp_apply, map_sub]
  unfold diamondError
  rw [hsub]
  exact div_le_div_of_nonneg_right
    (diamondNorm_stinespring_isometry_sandwich_le (Φ - Ψ) hE hD) (by norm_num)

end DiamondContraction

end NLQCLean
