import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite weights for Schmidt truncation

For the finite Schmidt optimization, nonnegative
weights, maximizing over subsets of at most K entries is the sum of the K
largest weights, with zero padding. No ordering or tie-breaking choice is
needed. The tensor-product estimate groups any chosen pairs by a coordinate.

-/

namespace NLQCLean

/-- Every allowed support, including the empty support. -/
def weightSupports (ι : Type*) [Fintype ι] (K : ℕ) : Finset (Finset ι) := by
  classical
  exact Finset.univ.powerset.filter (fun s ↦ s.card ≤ K)

@[simp] theorem mem_weightSupports {ι : Type*} [Fintype ι] {K : ℕ} {s : Finset ι} :
    s ∈ weightSupports ι K ↔ s.card ≤ K := by
  classical
  simp [weightSupports]

theorem weightSupports_nonempty (ι : Type*) [Fintype ι] (K : ℕ) :
    (weightSupports ι K).Nonempty :=
  ⟨∅, mem_weightSupports.mpr (by simp)⟩

/-- The maximal weight of a support of at most K entries. For nonnegative
weights this is exactly the top-K sum, including zero padding. -/
noncomputable def topWeightMass {ι : Type*} [Fintype ι] (K : ℕ) (w : ι → ℝ) : ℝ :=
  (weightSupports ι K).sup' (weightSupports_nonempty ι K) (fun s ↦ ∑ i ∈ s, w i)

theorem sum_le_topWeightMass {ι : Type*} [Fintype ι] {K : ℕ}
    (w : ι → ℝ) {s : Finset ι} (hs : s.card ≤ K) :
    ∑ i ∈ s, w i ≤ topWeightMass K w :=
  Finset.le_sup' (fun s ↦ ∑ i ∈ s, w i) (mem_weightSupports.mpr hs)

theorem topWeightMass_le {ι : Type*} [Fintype ι] {K : ℕ}
    (w : ι → ℝ) {B : ℝ} (hB : ∀ s : Finset ι, s.card ≤ K → ∑ i ∈ s, w i ≤ B) :
    topWeightMass K w ≤ B :=
  Finset.sup'_le _ _ (fun s hs ↦ hB s (mem_weightSupports.mp hs))

/-- The finite optimum is attained, including K = 0 and empty index types. -/
theorem exists_topWeightMass_support {ι : Type*} [Fintype ι] (K : ℕ) (w : ι → ℝ) :
    ∃ s : Finset ι, s.card ≤ K ∧ topWeightMass K w = ∑ i ∈ s, w i := by
  obtain ⟨s, hs, hsum⟩ := (weightSupports ι K).exists_mem_eq_sup'
    (weightSupports_nonempty ι K) (fun s ↦ ∑ i ∈ s, w i)
  exact ⟨s, mem_weightSupports.mp hs, hsum⟩

theorem topWeightMass_nonneg {ι : Type*} [Fintype ι] (K : ℕ) (w : ι → ℝ) :
    0 ≤ topWeightMass K w := by
  simpa using sum_le_topWeightMass w (s := ∅) (by simp : (∅ : Finset ι).card ≤ K)

theorem topWeightMass_le_sum {ι : Type*} [Fintype ι] (K : ℕ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) : topWeightMass K w ≤ ∑ i, w i := by
  apply topWeightMass_le
  intro s _
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ ↦ hw i)

/-- The flat-spectrum bound used by the SWAP test. -/
theorem topWeightMass_le_mul {ι : Type*} [Fintype ι] (K : ℕ) (w : ι → ℝ)
    {b : ℝ} (hb : 0 ≤ b) (hw : ∀ i, w i ≤ b) : topWeightMass K w ≤ K * b := by
  apply topWeightMass_le
  intro s hs
  calc
    ∑ i ∈ s, w i ≤ ∑ _i ∈ s, b := Finset.sum_le_sum (fun i _ ↦ hw i)
    _ = (s.card : ℝ) * b := by simp
    _ ≤ K * b := mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hb

/-- The optimization is independent of the chosen enumeration. -/
theorem topWeightMass_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (K : ℕ) (w : κ → ℝ) :
    topWeightMass K (fun i ↦ w (e i)) = topWeightMass K w := by
  apply le_antisymm
  · apply topWeightMass_le
    intro s hs
    have hcard : (s.map e.toEmbedding).card ≤ K := by simpa using hs
    simpa using sum_le_topWeightMass w hcard
  · obtain ⟨s, hs, hsum⟩ := exists_topWeightMass_support K w
    rw [hsum]
    have hcard : (s.map e.symm.toEmbedding).card ≤ K := by simpa using hs
    simpa using sum_le_topWeightMass (fun i ↦ w (e i)) hcard

/-- Fractional selection of total mass at most K cannot beat the top-K
sum. This sorted version is the elementary threshold argument underlying
the spectral overlap bound. -/
theorem sum_mul_le_topWeightMass_of_antitone {n : ℕ} (K : ℕ) (w p : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw_mono : Antitone w)
    (hp : ∀ i, 0 ≤ p i) (hp_one : ∀ i, p i ≤ 1) (hp_sum : ∑ i, p i ≤ K) :
    ∑ i, w i * p i ≤ topWeightMass K w := by
  classical
  by_cases hn : n ≤ K
  · calc
      ∑ i, w i * p i ≤ ∑ i, w i := Finset.sum_le_sum (fun i _ ↦
        (mul_le_mul_of_nonneg_left (hp_one i) (hw i)).trans_eq (mul_one _))
      _ ≤ topWeightMass K w := sum_le_topWeightMass w (by simpa using hn)
  · have hK : K < n := Nat.lt_of_not_ge hn
    let t := w ⟨K, hK⟩
    let s : Finset (Fin n) := Finset.univ.filter (fun i ↦ i.val < K)
    have hs : s.card = K := by
      simp [s, Fin.card_filter_val_lt, Nat.min_eq_right hK.le]
    have hpoint (i : Fin n) :
        w i * p i ≤ (if i.val < K then w i - t else 0) + t * p i := by
      by_cases hi : i.val < K
      · have hwi : t ≤ w i := hw_mono (show i ≤ ⟨K, hK⟩ from hi.le)
        simp only [ite_eq_left hi]
        nlinarith [mul_nonneg (sub_nonneg.mpr hwi) (sub_nonneg.mpr (hp_one i))]
      · have hwi : w i ≤ t := hw_mono (show (⟨K, hK⟩ : Fin n) ≤ i from Nat.le_of_not_gt hi)
        simp only [ite_eq_right hi, zero_add]
        exact mul_le_mul_of_nonneg_right hwi (hp i)
    have hdelta : (∑ i : Fin n, if i.val < K then w i - t else 0) =
        (∑ i ∈ s, w i) - K * t := by
      rw [← Finset.sum_filter, Finset.sum_sub_distrib]
      change (∑ i ∈ s, w i) - (∑ _i ∈ s, t) = (∑ i ∈ s, w i) - K * t
      simp [hs]
    have hbound := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hpoint i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hdelta] at hbound
    have hmass := mul_le_mul_of_nonneg_left hp_sum (hw ⟨K, hK⟩)
    calc
      ∑ i, w i * p i ≤ ∑ i ∈ s, w i := by dsimp [t] at hbound ⊢; nlinarith
      _ ≤ topWeightMass K w := sum_le_topWeightMass w hs.le

/-- The fractional-selection bound for arbitrary finite nonnegative weights.
This will be applied to the squared lengths of eigenvectors projected onto
the support of a rank-K test matrix. -/
theorem sum_mul_le_topWeightMass {ι : Type*} [Fintype ι] (K : ℕ) (w p : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 ≤ p i) (hp_one : ∀ i, p i ≤ 1)
    (hp_sum : ∑ i, p i ≤ K) : ∑ i, w i * p i ≤ topWeightMass K w := by
  classical
  let f : Fin (Fintype.card ι) → ℝᵒᵈ := fun i ↦ w ((Fintype.equivFin ι).symm i)
  let e : Fin (Fintype.card ι) ≃ ι := (Tuple.sort f).trans (Fintype.equivFin ι).symm
  have hmono : Antitone (fun i ↦ w (e i)) := Tuple.monotone_sort f
  have hsum : ∑ i, p (e i) ≤ K := (e.sum_comp p).trans_le hp_sum
  have h := sum_mul_le_topWeightMass_of_antitone K (fun i ↦ w (e i)) (fun i ↦ p (e i))
    (fun i ↦ hw _) hmono (fun i ↦ hp _) (fun i ↦ hp_one _) hsum
  rw [topWeightMass_reindex e] at h
  exact (e.sum_comp (fun i ↦ w i * p i)).symm.trans_le h

/-- R:group: K selected pairs have weight at most the top-K mass of the
second factor when the first factor is a probability vector. -/
theorem sum_product_weights_le_right {ι κ : Type*} [Fintype ι] [Fintype κ]
    {K : ℕ} (a : ι → ℝ) (b : κ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ j, 0 ≤ b j) (ha_sum : ∑ i, a i = 1)
    {s : Finset (ι × κ)} (hs : s.card ≤ K) :
    ∑ p ∈ s, a p.1 * b p.2 ≤ topWeightMass K b := by
  classical
  let t := s.image Prod.snd
  have hsub : s ⊆ Finset.univ ×ˢ t := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ hp⟩
  calc
    ∑ p ∈ s, a p.1 * b p.2 ≤ ∑ p ∈ Finset.univ ×ˢ t, a p.1 * b p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ mul_nonneg (ha _) (hb _))
    _ = ∑ j ∈ t, b j := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ha_sum, one_mul]
    _ ≤ topWeightMass K b := sum_le_topWeightMass b ((Finset.card_image_le).trans hs)

/-- The symmetric grouping estimate. -/
theorem sum_product_weights_le_left {ι κ : Type*} [Fintype ι] [Fintype κ]
    {K : ℕ} (a : ι → ℝ) (b : κ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ j, 0 ≤ b j) (hb_sum : ∑ j, b j = 1)
    {s : Finset (ι × κ)} (hs : s.card ≤ K) :
    ∑ p ∈ s, a p.1 * b p.2 ≤ topWeightMass K a := by
  classical
  let t := s.image Prod.fst
  have hsub : s ⊆ t ×ˢ Finset.univ := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_univ _⟩
  calc
    ∑ p ∈ s, a p.1 * b p.2 ≤ ∑ p ∈ t ×ˢ Finset.univ, a p.1 * b p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ mul_nonneg (ha _) (hb _))
    _ = ∑ i ∈ t, a i := by simp_rw [Finset.sum_product, ← Finset.mul_sum, hb_sum, mul_one]
    _ ≤ topWeightMass K a := sum_le_topWeightMass a ((Finset.card_image_le).trans hs)

/-- For squared Schmidt weights, tensoring two probability vectors
cannot increase the top-K mass. -/
theorem topWeightMass_product_le_min {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ℕ) (a : ι → ℝ) (b : κ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ j, 0 ≤ b j) (ha_sum : ∑ i, a i = 1) (hb_sum : ∑ j, b j = 1) :
    topWeightMass K (fun p : ι × κ ↦ a p.1 * b p.2) ≤
      min (topWeightMass K a) (topWeightMass K b) := by
  apply topWeightMass_le
  intro s hs
  exact le_min (sum_product_weights_le_left a b ha hb hb_sum hs)
    (sum_product_weights_le_right a b ha hb ha_sum hs)

end NLQCLean
