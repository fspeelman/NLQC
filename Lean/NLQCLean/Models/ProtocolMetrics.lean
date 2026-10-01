import NLQCLean.Models.ChoiMetrics
import NLQCLean.Models.ForwardReindex

/-!
# Diamond-to-score conversion for actual one-round protocols

All trace identities are proved from the existing isometries
and convex mixed channel. The bridge has no resource-rank or local-support
hypothesis and covers arbitrary finite private/register dimensions.
-/

namespace NLQCLean

open Matrix

variable {ρA ρB ιA ιB ιA' ιB' κA κB μA μB εA εB : Type*} {n : ℕ}
variable [Fintype ρA] [Fintype ρB] [Fintype ιA] [Fintype ιB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ιA] [DecidableEq ιB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
variable [Nonempty ιA] [Nonempty ιB]

omit [Nonempty ιA] [Nonempty ιB] [DecidableEq ιA'] [DecidableEq εA] in
/-- Regrouping system and environment preserves the actual protocol isometry. -/
theorem isIsometry_globalIsometryRegrouped {η : ρA × ρB → ℂ}
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ} {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix (ιA' × εA) (κA × μB) ℂ} {DB : Matrix (ιB' × εB) (κB × μA) ℂ}
    (hη : IsUnitVector η) (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB) :
    IsIsometry (globalIsometryRegrouped η VA VB DA DB) :=
  (isIsometry_globalIsometry hη hVA hVB hDA hDB).submatrix_equiv
    (outputRegroup ιA' ιB' εA εB) (Equiv.refl (ιA × ιB))

omit [DecidableEq ιA'] [DecidableEq εA] in
theorem trace_choiMatrix_operationalChannel {η : ρA × ρB → ℂ}
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ} {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix (ιA' × εA) (κA × μB) ℂ} {DB : Matrix (ιB' × εB) (κB × μA) ℂ}
    (hη : IsUnitVector η) (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB) :
    (choiMatrix (operationalChannel η VA VB DA DB)).trace = 1 :=
  trace_choiMatrix_channelOf_eq_one (isIsometry_globalIsometryRegrouped hη hVA hVB hDA hDB)

theorem PureProtocol.trace_choiMatrix_eq_one
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB) :
    (choiMatrix P.operationalChannel).trace = 1 :=
  trace_choiMatrix_operationalChannel P.resource_unit P.encA_isometry P.encB_isometry
    P.decA_isometry P.decB_isometry

/-- The pure operational metric bridge, without any assumed scalar inequality. -/
theorem PureProtocol.one_sub_scoreU_le_diamondError
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ} (hU : IsIsometry U) :
    1 - scoreU U P.operationalChannel ≤ diamondError P.operationalChannel (adConj U) :=
  NLQCLean.one_sub_scoreU_le_diamondError hU _ P.trace_choiMatrix_eq_one

theorem PureProtocol.scoreU_ge_of_diamondError_le
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ} (hU : IsIsometry U) {e : ℝ}
    (he : diamondError P.operationalChannel (adConj U) ≤ e) :
    1 - e ≤ scoreU U P.operationalChannel := by
  linarith [P.one_sub_scoreU_le_diamondError hU]

omit [DecidableEq ιA'] [DecidableEq εA] in
/-- The actual common-map mixed channel has trace-one Choi state. -/
theorem MixedResource.trace_choiMatrix_eq_one (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ} {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix (ιA' × εA) (κA × μB) ℂ} {DB : Matrix (ιB' × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB) :
    (choiMatrix (m.mixedChannel VA VB DA DB)).trace = 1 := by
  rw [MixedResource.mixedChannel, trace_choiMatrix_sum_smul]
  simp only [trace_choiMatrix_operationalChannel (m.component_unit _) hVA hVB hDA hDB, mul_one]
  exact_mod_cast m.weight_sum

omit [DecidableEq εA] in
/-- The mixed operational metric is converted before selecting any pure component. -/
theorem MixedResource.one_sub_scoreU_le_diamondError (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ} {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix (ιA' × εA) (κA × μB) ℂ} {DB : Matrix (ιB' × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ} (hU : IsIsometry U) :
    1 - scoreU U (m.mixedChannel VA VB DA DB) ≤
      diamondError (m.mixedChannel VA VB DA DB) (adConj U) :=
  NLQCLean.one_sub_scoreU_le_diamondError hU _ (m.trace_choiMatrix_eq_one hVA hVB hDA hDB)

omit [DecidableEq εA] in
theorem MixedResource.scoreU_ge_of_diamondError_le (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ} {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : Matrix (ιA' × εA) (κA × μB) ℂ} {DB : Matrix (ιB' × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ} (hU : IsIsometry U) {e : ℝ}
    (he : diamondError (m.mixedChannel VA VB DA DB) (adConj U) ≤ e) :
    1 - e ≤ scoreU U (m.mixedChannel VA VB DA DB) := by
  linarith [m.one_sub_scoreU_le_diamondError hVA hVB hDA hDB hU]

end NLQCLean
