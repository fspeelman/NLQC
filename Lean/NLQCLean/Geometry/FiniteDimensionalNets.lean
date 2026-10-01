import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Volumetric finite nets

In a finite-dimensional real normed space of
dimension `n`, every subset of the closed unit ball has an `η`-net contained in the set with at
most `(1 + 2/η)^n` points. The proof compares disjoint `η/2`-balls around a separated family
with the ball of radius `1 + η/2`, then takes a separated family of maximal cardinality.
No Gaussian, sphere-measure or covering-number input is used.
-/

namespace NLQCLean

open MeasureTheory Metric Module

section Nets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A finite family whose distinct points are more than `η` apart. -/
def IsNormSeparated (η : ℝ) (F : Finset E) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F, x ≠ y → η < ‖x - y‖

/-- The volumetric packing bound. -/
theorem card_le_of_isNormSeparated {η : ℝ} (hη : 0 < η) {F : Finset E}
    (hF : ∀ x ∈ F, ‖x‖ ≤ 1) (hsep : IsNormSeparated η F) :
    (F.card : ℝ) ≤ (1 + 2 / η) ^ finrank ℝ E := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hcard : F.card ≤ 1 := Finset.card_le_one.mpr fun a _ b _ => Subsingleton.elim a b
    have h1 : (1 : ℝ) ≤ (1 + 2 / η) ^ finrank ℝ E :=
      one_le_pow₀ (by have : 0 ≤ 2 / η := by positivity
                      linarith)
    exact (by exact_mod_cast hcard : (F.card : ℝ) ≤ 1).trans h1
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := (Module.finBasis ℝ E).addHaar
  have hdisj : Set.PairwiseDisjoint (F : Set E) (fun x => ball x (η / 2)) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr fun z hzx hzy => ?_
    have h1 := hsep x hx y hy hxy
    have h2 : ‖x - y‖ ≤ ‖z - x‖ + ‖z - y‖ := by
      calc ‖x - y‖ = ‖(z - y) - (z - x)‖ := by congr 1; abel
        _ ≤ ‖z - y‖ + ‖z - x‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    rw [mem_ball, dist_eq_norm] at hzx hzy
    linarith
  have hsub : (⋃ x ∈ F, ball x (η / 2)) ⊆ ball (0 : E) (1 + η / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    rw [mem_ball, dist_eq_norm] at hzx
    rw [mem_ball, dist_zero_right]
    calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ < η / 2 + 1 := by linarith [hF x hx]
      _ = 1 + η / 2 := add_comm _ _
  have hvol := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at hvol
  simp only [Measure.addHaar_ball μ _ (by positivity : (0 : ℝ) ≤ η / 2),
    Finset.sum_const, nsmul_eq_mul,
    Measure.addHaar_ball μ _ (by positivity : (0 : ℝ) ≤ 1 + η / 2)] at hvol
  have hpos : 0 < μ (ball (0 : E) 1) := measure_ball_pos μ 0 one_pos
  have hfin : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc] at hvol
  have hreal := (ENNReal.mul_le_mul_iff_left hpos.ne' hfin).mp hvol
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hreal
  have hη2 : 0 < (η / 2) ^ finrank ℝ E := by positivity
  have hdiv : (1 + 2 / η) ^ finrank ℝ E = (1 + η / 2) ^ finrank ℝ E / (η / 2) ^ finrank ℝ E := by
    rw [← div_pow]
    congr 1
    field_simp
    ring
  rw [hdiv, le_div_iff₀ hη2]
  exact hreal

/-- Net lemma: an `η`-net of any subset of the closed unit ball, inside the set. -/
theorem exists_finset_net_of_subset_closedBall {A : Set E} (hA : ∀ x ∈ A, ‖x‖ ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ F : Finset E, (∀ y ∈ F, y ∈ A) ∧ (F.card : ℝ) ≤ (1 + 2 / η) ^ finrank ℝ E ∧
      ∀ x ∈ A, ∃ y ∈ F, ‖x - y‖ ≤ η := by
  classical
  let P : ℕ → Prop := fun k => ∃ F : Finset E, (∀ y ∈ F, y ∈ A) ∧ IsNormSeparated η F ∧ F.card = k
  let M : ℕ := ⌊(1 + 2 / η) ^ finrank ℝ E⌋₊
  have hbound : ∀ k, P k → k ≤ M := by
    rintro k ⟨F, hFA, hsep, rfl⟩
    exact Nat.le_floor (card_le_of_isNormSeparated hη (fun x hx => hA x (hFA x hx)) hsep)
  have hP0 : P 0 := ⟨∅, by simp, by simp [IsNormSeparated], rfl⟩
  obtain ⟨F, hFA, hsep, hcard⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le M) hP0
  refine ⟨F, hFA, card_le_of_isNormSeparated hη (fun x hx => hA x (hFA x hx)) hsep, ?_⟩
  intro x hx
  by_contra hfar
  simp only [not_exists, not_and, not_le] at hfar
  have hxF : x ∉ F := fun hxF => by
    have h := hfar x hxF
    rw [sub_self, norm_zero] at h
    linarith
  have hsep' : IsNormSeparated η (insert x F) := by
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact hfar b hb
    · rw [norm_sub_rev]; exact hfar a ha
    · exact hsep a ha b hb hab
  have hPk : P (Nat.findGreatest P M + 1) :=
    ⟨insert x F, fun y hy => by
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hFA y hy, hsep', by rw [Finset.card_insert_of_notMem hxF, hcard]⟩
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hbound _ hPk) hPk

end Nets

end NLQCLean
