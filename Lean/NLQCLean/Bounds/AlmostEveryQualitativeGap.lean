import NLQCLean.Bounds.GeneralTargetQualitativeGap
import NLQCLean.Bounds.AlmostEveryExact

/-!
# Unconditional almost-every fixed-target qualitative gaps

The conull set comes from exact exclusion, and charged compactness supplies a
positive gap at each budget. Each gap depends on its fixed target and budget;
no quantitative geometry input or target-uniform rate is used.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory

theorem exists_general_target_unitary_gap_of_not_mem_zero {d : ℕ} (hd : 2 ≤ d)
    (U : unitaryGroup (Fin d × Fin d) ℂ)
    (hN : ∀ K : ℕ, U ∉ pureReachable d K 0) (K : ℕ) :
    ∃ e : ℝ, 0 < e ∧
      PureScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
        (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e ∧
      MixedScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
        (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e ∧
      PureDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
        (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e ∧
      MixedDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
        (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e := by
  let : NeZero d := ⟨by omega⟩
  have hU : UnitaryTarget (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
    ⟨U.property.1, U.property.2⟩
  apply exists_general_target_unitary_gap hd
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hU ?_ K
  intro s P hexact
  let B := schmidtRank P.resource * s 4 * s 5
  have hP : P.HasFootprint B := (hasFootprint_iff B P.resource).mpr
    (by simp only [Fintype.card_fin]; exact le_rfl)
  apply hN B
  refine ⟨s, P, hP, ?_⟩
  change P.operationalChannel = adConj
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) at hexact
  rw [hexact, scoreU_adConj_self hU.1]
  norm_num

theorem exists_general_target_pvm_gap_of_not_mem_zero {d : ℕ} (hd : 2 ≤ d)
    (M : unitaryGroup (Fin d × Fin d) ℂ)
    (hN : ∀ K : ℕ, M ∉ purePVMReachable d K 0) (K : ℕ) :
    ∃ e : ℝ, 0 < e ∧
      PurePVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
        (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e ∧
      MixedPVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
        (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e ∧
      PurePVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
        (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e ∧
      MixedPVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
        (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e := by
  let : NeZero d := ⟨by omega⟩
  have hM : IsIsometry (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := M.property.1
  apply exists_general_target_pvm_gap hd
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hM ?_ K
  intro s P hexact
  let B := schmidtRank P.resource * s 4 * s 5
  have hP : P.HasFootprint B := (hasFootprint_iff B P.resource).mpr
    (by simp only [Fintype.card_fin]; exact le_rfl)
  apply hN B
  refine ⟨s, P, hP, ?_⟩
  rw [(P.scorePVM_eq_one_iff_performsPVM hM).mpr hexact]
  norm_num

/-- Almost every unitary has positive budget gaps, uniformly over original registers. -/
theorem ae_general_target_unitary_gap :
    ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (U : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
        ∀ K : ℕ, ∃ e : ℝ, 0 < e ∧
          PureScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
            (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e ∧
          MixedScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
            (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e ∧
          PureDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
            (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e ∧
          MixedDiamondGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
            (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e := by
  intro d hd
  filter_upwards [ae_not_mem_reachable_zero d hd] with U hU
  exact fun K => exists_general_target_unitary_gap_of_not_mem_zero hd U
    (fun B => (hU B).1) K

/-- Almost every ordered basis lift has positive score and joint-TV gaps. -/
theorem ae_general_target_pvm_gap :
    ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (M : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
        ∀ K : ℕ, ∃ e : ℝ, 0 < e ∧
          PurePVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
            (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e ∧
          MixedPVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
            (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e ∧
          PurePVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
            (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e ∧
          MixedPVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
            (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K e := by
  intro d hd
  filter_upwards [ae_not_mem_reachable_zero d hd] with M hM
  exact fun K => exists_general_target_pvm_gap_of_not_mem_zero hd M
    (fun B => (hM B).2.2.1) K

end NLQCLean
