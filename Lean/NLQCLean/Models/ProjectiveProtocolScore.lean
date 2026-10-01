import NLQCLean.Models.ProjectiveScoreSemantics
import NLQCLean.Models.ForwardWitness

/-!
# PVM score semantics for physical protocols

Specialize the isometry results to the unchanged
one-round architecture and finite common-map mixed resources. All original
finite resource, private, message and environment dimensions are arbitrary.
-/

namespace NLQCLean
open Matrix
open scoped Matrix.Norms.Frobenius

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB]

/-- Physical pure protocol scores lie in the unit interval. -/
theorem PureProtocol.scorePVM_mem_Icc
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB (ιA × ιB) (ιA × ιB) εA εB)
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hM : IsIsometry M) :
    scorePVM M P.operationalChannel ∈ Set.Icc (0 : ℝ) 1 :=
  scorePVM_channelOf_regrouped_mem_Icc P.isIsometry_globalIsometry hM

/-- Score one is the original all-input PVM task, not a channel-to-unitary
condition. Both parties' logical output alphabets are the joint input index. -/
theorem PureProtocol.scorePVM_eq_one_iff_performsPVM [Nonempty ιA] [Nonempty ιB]
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB (ιA × ιB) (ιA × ιB) εA εB)
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hM : IsIsometry M) :
    scorePVM M P.operationalChannel = 1 ↔ P.PerformsPVM M :=
  scorePVM_eq_one_iff_twoSidedExact P.isIsometry_globalIsometry hM

omit [DecidableEq εA] in
/-- Convex affinity and physical component bounds give the same score
interval for the actual finite mixed channel; zero weights are permitted. -/
theorem MixedResource.scorePVM_mem_Icc {n : ℕ} (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ} {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ}
    {DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ} (hM : IsIsometry M) :
    scorePVM M (m.mixedChannel VA VB DA DB) ∈ Set.Icc (0 : ℝ) 1 := by
  have hc (k : Fin n) : scorePVM M (operationalChannel (m.component k) VA VB DA DB) ∈
      Set.Icc (0 : ℝ) 1 := scorePVM_channelOf_regrouped_mem_Icc
        (isIsometry_globalIsometry (m.component_unit k) hVA hVB hDA hDB) hM
  rw [MixedResource.scorePVM_mixedChannel]
  constructor
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (m.weight_nonneg k) (hc k).1
  · calc
      _ ≤ ∑ k, m.weight k * 1 := Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (hc k).2 (m.weight_nonneg k)
      _ = 1 := by simpa using m.weight_sum

section Smoothness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {r : WithTop ℕ∞}

omit [DecidableEq ρA] [DecidableEq εA] [DecidableEq εB] in
/-- Smoothness in the actual target, resource and four local maps. No
isometry constraint, garbage choice or support compression is needed. -/
theorem ContDiff.scorePVM_operationalChannel_joint
    {M : E → Matrix (ιA × ιB) (ιA × ιB) ℂ}
    {η : E → (ρA × ρB → ℂ)}
    {VA : E → Matrix (κA × μA) (ιA × ρA) ℂ}
    {VB : E → Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : E → Matrix ((ιA × ιB) × εA) (κA × μB) ℂ}
    {DB : E → Matrix ((ιA × ιB) × εB) (κB × μA) ℂ}
    (hM : ContDiff ℝ r M) (hη : ContDiff ℝ r η)
    (hVA : ContDiff ℝ r VA) (hVB : ContDiff ℝ r VB)
    (hDA : ContDiff ℝ r DA) (hDB : ContDiff ℝ r DB) :
    ContDiff ℝ r (fun x => scorePVM (M x)
      (operationalChannel (η x) (VA x) (VB x) (DA x) (DB x))) := by
  apply ContDiff.scorePVM_channelOf_joint hM
  exact ContDiff.matrixMul (ContDiff.matrixKronecker hDA hDB)
    (ContDiff.matrixMul contDiff_const
      (ContDiff.matrixMul (ContDiff.matrixKronecker hVA hVB)
        (ContDiff.insertResource hη)))

end Smoothness
end NLQCLean
