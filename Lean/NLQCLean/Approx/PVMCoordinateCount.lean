import NLQCLean.Approx.PVMReverseWitness

/-!
# Coordinate counts for PVM reverse witnesses

This file counts the real coordinates in the six
raw complex blocks of a PVM reverse witness and embeds that count in a fixed
budget depending only on the logical dimension and charged footprint.
-/

namespace NLQCLean

open scoped BigOperators

namespace PVMReverseShape

variable {d K : ℕ} (s : PVMReverseShape d K)

/-- The selected flagged support has size at most `K + d²`. -/
theorem supportSize_le : s.supportSize ≤ K + d ^ 2 := by
  simpa only [supportSize, Fintype.card_prod, Fintype.card_fin, pow_two] using s.2.sum_le

/-- When there is at least one logical label, the selected flagged support is nonempty. -/
theorem supportSize_pos (hd : 0 < d) : 0 < s.supportSize := by
  let i : Fin d × Fin d := (⟨0, hd⟩, ⟨0, hd⟩)
  have hi : s.2.rank i ≤ ∑ j, s.2.rank j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact (s.2.rank_pos i).trans_le hi

/-- Every charged reverse shape has a positive footprint budget. -/
theorem one_le_budget (s : PVMReverseShape d K) : 1 ≤ K :=
  (mul_pos (mul_pos s.1.resource_pos s.1.messageA_pos) s.1.messageB_pos).trans_le
    s.1.footprint

end PVMReverseShape

namespace PVMReverseBlocks

variable {d K : ℕ}

/-- Exact real coordinate count of the resource, per-label garbage, two
encoders, and two completed reverse isometries. -/
theorem finrank_real (s : PVMReverseShape d K) :
    Module.finrank ℝ (PVMReverseBlocks s) =
      2 * s.1.r ^ 2 + 2 * (∑ i, s.2.rank i ^ 2) +
        2 * d ^ 2 * (s.1.r * s.1.mA) ^ 2 +
        2 * d ^ 2 * (s.1.r * s.1.mB) ^ 2 +
        4 * (d * K + s.supportSize) * s.supportSize := by
  have hgarbage :
      Module.finrank ℂ
          ((i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ) =
        ∑ i, s.2.rank i ^ 2 := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_pi, Fintype.card_prod,
      Fintype.card_fin]
    congr 1 with i
    ring
  rw [finrank_real_of_complex]
  simp only [PVMReverseBlocks, Module.finrank_prod, Module.finrank_pi,
    Module.finrank_matrix, Module.finrank_self, Fintype.card_prod, Fintype.card_fin,
    s.card_support]
  rw [hgarbage]
  ring

/-- The raw coordinate count has a universal bound before using the PVM
footprint floor. -/
theorem finrank_real_le (s : PVMReverseShape d K) (hd : 0 < d) :
    Module.finrank ℝ (PVMReverseBlocks s) ≤ 16 * d ^ 2 * (K + d ^ 2) ^ 2 := by
  have hA : s.1.r * s.1.mA ≤ K :=
    (Nat.le_mul_of_pos_right _ s.1.messageB_pos).trans s.1.footprint
  have hB : s.1.r * s.1.mB ≤ K := by
    have h := Nat.le_mul_of_pos_right (s.1.r * s.1.mB) s.1.messageA_pos
    exact h.trans (by
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using s.1.footprint)
  have hr : s.1.r ≤ K := (Nat.le_mul_of_pos_right _ s.1.messageA_pos).trans hA
  have hS : s.supportSize ≤ K + d ^ 2 := s.supportSize_le
  have hsq : (∑ i, s.2.rank i ^ 2) ≤ s.supportSize ^ 2 := by
    simpa only [PVMReverseShape.supportSize] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := s.2.rank)
        (fun _ _ => Nat.zero_le _))
  have hd_sq : d ≤ d ^ 2 := by
    simpa only [pow_two] using Nat.le_mul_of_pos_left d hd
  have hone_sq : 1 ≤ d ^ 2 := pow_pos hd 2
  have hd_coeff : d + 1 ≤ 2 * d ^ 2 := by omega
  have hr_bound : s.1.r ^ 2 ≤ d ^ 2 * (K + d ^ 2) ^ 2 := by
    calc
      s.1.r ^ 2 ≤ (K + d ^ 2) ^ 2 := by gcongr; omega
      _ ≤ d ^ 2 * (K + d ^ 2) ^ 2 := Nat.le_mul_of_pos_left _ hone_sq
  have hsquare_bound : (∑ i, s.2.rank i ^ 2) ≤ d ^ 2 * (K + d ^ 2) ^ 2 := by
    calc
      (∑ i, s.2.rank i ^ 2) ≤ s.supportSize ^ 2 := hsq
      _ ≤ (K + d ^ 2) ^ 2 := by gcongr
      _ ≤ d ^ 2 * (K + d ^ 2) ^ 2 := Nat.le_mul_of_pos_left _ hone_sq
  have hA_bound : d ^ 2 * (s.1.r * s.1.mA) ^ 2 ≤
      d ^ 2 * (K + d ^ 2) ^ 2 := by (gcongr; omega)
  have hB_bound : d ^ 2 * (s.1.r * s.1.mB) ^ 2 ≤
      d ^ 2 * (K + d ^ 2) ^ 2 := by (gcongr; omega)
  have hreverse : (d * K + s.supportSize) * s.supportSize ≤
      2 * d ^ 2 * (K + d ^ 2) ^ 2 := by
    calc
      (d * K + s.supportSize) * s.supportSize ≤
          (d * (K + d ^ 2) + (K + d ^ 2)) * (K + d ^ 2) := by (gcongr; omega)
      _ = (d + 1) * (K + d ^ 2) ^ 2 := by ring
      _ ≤ 2 * d ^ 2 * (K + d ^ 2) ^ 2 := by gcongr
  have hr_bound2 : 2 * s.1.r ^ 2 ≤ 2 * (d ^ 2 * (K + d ^ 2) ^ 2) :=
    Nat.mul_le_mul_left 2 hr_bound
  have hsquare_bound2 : 2 * (∑ i, s.2.rank i ^ 2) ≤
      2 * (d ^ 2 * (K + d ^ 2) ^ 2) := Nat.mul_le_mul_left 2 hsquare_bound
  have hA_bound2 : 2 * d ^ 2 * (s.1.r * s.1.mA) ^ 2 ≤
      2 * (d ^ 2 * (K + d ^ 2) ^ 2) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hA_bound
  have hB_bound2 : 2 * d ^ 2 * (s.1.r * s.1.mB) ^ 2 ≤
      2 * (d ^ 2 * (K + d ^ 2) ^ 2) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hB_bound
  have hreverse4 : 4 * (d * K + s.supportSize) * s.supportSize ≤
      4 * (2 * d ^ 2 * (K + d ^ 2) ^ 2) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 4 hreverse
  rw [finrank_real]
  calc
    2 * s.1.r ^ 2 + 2 * (∑ i, s.2.rank i ^ 2) +
          2 * d ^ 2 * (s.1.r * s.1.mA) ^ 2 +
          2 * d ^ 2 * (s.1.r * s.1.mB) ^ 2 +
          4 * (d * K + s.supportSize) * s.supportSize ≤
        2 * (d ^ 2 * (K + d ^ 2) ^ 2) +
          2 * (d ^ 2 * (K + d ^ 2) ^ 2) +
          2 * (d ^ 2 * (K + d ^ 2) ^ 2) +
          2 * (d ^ 2 * (K + d ^ 2) ^ 2) +
          4 * (2 * d ^ 2 * (K + d ^ 2) ^ 2) :=
      add_le_add
        (add_le_add (add_le_add (add_le_add hr_bound2 hsquare_bound2) hA_bound2) hB_bound2)
        hreverse4
    _ = 16 * d ^ 2 * (K + d ^ 2) ^ 2 := by ring

/-- Under the PVM floor `d² ≤ 4K`, 400 is an explicit coordinate constant. -/
theorem finrank_real_le_four_hundred (s : PVMReverseShape d K) (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) :
    Module.finrank ℝ (PVMReverseBlocks s) ≤ 400 * d ^ 2 * K ^ 2 := by
  calc
    Module.finrank ℝ (PVMReverseBlocks s) ≤ 16 * d ^ 2 * (K + d ^ 2) ^ 2 :=
      finrank_real_le s hd
    _ ≤ 16 * d ^ 2 * (5 * K) ^ 2 := by (gcongr; omega)
    _ = 400 * d ^ 2 * K ^ 2 := by ring

end PVMReverseBlocks

/-- Common integral coordinate budget for PVM witnesses.  The slack above
the count constant accommodates speed and arithmetic estimates. -/
def pvmWitnessCoordinateBudget (d K : ℕ) : ℕ := 1024 * d ^ 2 * K ^ 2

theorem pvmWitnessCoordinateBudget_pos {d K : ℕ} (hd : 0 < d) (hK : 0 < K) :
    0 < pvmWitnessCoordinateBudget d K := by
  unfold pvmWitnessCoordinateBudget
  positivity

theorem one_le_pvmWitnessCoordinateBudget {d K : ℕ} (hd : 0 < d) (hK : 0 < K) :
    1 ≤ pvmWitnessCoordinateBudget d K :=
  pvmWitnessCoordinateBudget_pos hd hK

theorem d_le_pvmWitnessCoordinateBudget {d K : ℕ} (hd : 0 < d) (hK : 0 < K) :
    d ≤ pvmWitnessCoordinateBudget d K := by
  unfold pvmWitnessCoordinateBudget
  have hd2 : d ≤ d ^ 2 := by simpa only [pow_two] using Nat.le_mul_of_pos_left d hd
  have hK2 : 1 ≤ K ^ 2 := pow_pos hK 2
  nlinarith

theorem K_le_pvmWitnessCoordinateBudget {d K : ℕ} (hd : 0 < d) (hK : 0 < K) :
    K ≤ pvmWitnessCoordinateBudget d K := by
  unfold pvmWitnessCoordinateBudget
  have hd2 : 1 ≤ d ^ 2 := pow_pos hd 2
  have hK2 : K ≤ K ^ 2 := by simpa only [pow_two] using Nat.le_mul_of_pos_left K hK
  nlinarith

namespace PVMReverseBlocks

/-- Every PVM reverse witness fits in the fixed coordinate budget after the PVM
footprint floor has been imposed. -/
theorem finrank_real_le_budget {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) :
    Module.finrank ℝ (PVMReverseBlocks s) ≤ pvmWitnessCoordinateBudget d K := by
  calc
    Module.finrank ℝ (PVMReverseBlocks s) ≤ 400 * d ^ 2 * K ^ 2 :=
      finrank_real_le_four_hundred s hd hfloor
    _ ≤ 1024 * d ^ 2 * K ^ 2 := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
    _ = pvmWitnessCoordinateBudget d K := rfl

/-- A shape supplies the positive-`K` premise needed by the fixed budget. -/
theorem one_le_coordinateBudget {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) :
    1 ≤ pvmWitnessCoordinateBudget d K :=
  one_le_pvmWitnessCoordinateBudget hd s.one_le_budget

end PVMReverseBlocks

namespace PVMReverseShape

/-- A coordinate budget for the witnesses of one shape: it bounds the real
coordinate count and the witness speed constant `d √(10 d K)`. -/
def AdmissibleBudget {d K : ℕ} (s : PVMReverseShape d K) (P : ℕ) : Prop :=
  Module.finrank ℝ (PVMReverseBlocks s) ≤ P ∧ (d : ℝ) * Real.sqrt (10 * d * K) ≤ P

theorem AdmissibleBudget.one_le {d K : ℕ} {s : PVMReverseShape d K} {P : ℕ}
    (h : s.AdmissibleBudget P) : 1 ≤ P := by
  have hr : 1 ≤ s.1.r := s.1.resource_pos
  have hf := PVMReverseBlocks.finrank_real s
  have : 2 ≤ Module.finrank ℝ (PVMReverseBlocks s) := by
    rw [hf]
    have h1 : 1 ≤ s.1.r ^ 2 := Nat.one_le_pow _ _ hr
    omega
  exact le_trans (by omega) (this.trans h.1)

end PVMReverseShape

theorem pvm_witness_speedConstant_le_budget_of_pos {d K : ℕ} (hd : 0 < d) (hK : 1 ≤ K) :
    (d : ℝ) * Real.sqrt (10 * d * K : ℝ) ≤ (pvmWitnessCoordinateBudget d K : ℝ) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hdK : (1 : ℝ) ≤ d * K := by nlinarith
  have hs : Real.sqrt (10 * d * K : ℝ) ≤ 10 * d * K :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  calc
    _ ≤ (d : ℝ) * (10 * d * K) := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg d)
    _ ≤ 1024 * (d : ℝ) ^ 2 * (K : ℝ) ^ 2 := by nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg (K : ℝ))]
    _ = _ := by simp [pvmWitnessCoordinateBudget]

/-- The fixed budget `1024 d² K²` is admissible for every shape once `d² ≤ 4K`. -/
theorem PVMReverseShape.admissibleBudget_full {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) : s.AdmissibleBudget (pvmWitnessCoordinateBudget d K) :=
  ⟨PVMReverseBlocks.finrank_real_le_budget s hd hfloor,
    pvm_witness_speedConstant_le_budget_of_pos hd s.one_le_budget⟩

end NLQCLean
