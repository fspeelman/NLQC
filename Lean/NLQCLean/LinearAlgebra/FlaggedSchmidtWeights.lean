import NLQCLean.LinearAlgebra.SchmidtTruncation

/-!
# Grouped weights for flagged Schmidt truncation

For finite selection, a top-`K` support of triples
`(label, environment coordinate, Schmidt coordinate)` can be grouped by its
first two coordinates without increasing its cardinality.  Probability
normalization of the label-dependent Schmidt weights then bounds the selected
triple mass by the retained environment mass.

No ordering or tie-breaking choice is exposed, so the statements also cover
zero weights and repeated coefficients.
-/

namespace NLQCLean

/-- The environment coordinates of `S` carrying the specified label. -/
def groupedFiberSupport {δ e : Type*} [DecidableEq δ] [DecidableEq e]
    (S : Finset (δ × e)) (i : δ) : Finset e :=
  (S.filter fun p ↦ p.1 = i).image Prod.snd

@[simp] theorem mem_groupedFiberSupport {δ e : Type*} [DecidableEq δ] [DecidableEq e]
    {S : Finset (δ × e)} {i : δ} {x : e} :
    x ∈ groupedFiberSupport S i ↔ (i, x) ∈ S := by
  simp [groupedFiberSupport]

/-- Splitting a pair support by its label preserves its cardinality exactly. -/
theorem sum_card_groupedFiberSupport {δ e : Type*} [Fintype δ]
    [DecidableEq δ] [DecidableEq e] (S : Finset (δ × e)) :
    ∑ i, (groupedFiberSupport S i).card = S.card := by
  classical
  have hcard (i : δ) :
      (groupedFiberSupport S i).card = (S.filter fun p ↦ p.1 = i).card := by
    apply Finset.card_image_of_injOn
    intro p hp q hq hpq
    have hpi : p.1 = i := (Finset.mem_filter.mp hp).2
    have hqi : q.1 = i := (Finset.mem_filter.mp hq).2
    exact Prod.ext (hpi.trans hqi.symm) hpq
  calc
    ∑ i, (groupedFiberSupport S i).card =
        ∑ i, (S.filter fun p ↦ p.1 = i).card :=
      Finset.sum_congr rfl fun i _ ↦ hcard i
    _ = S.card := by
      symm
      simpa using
        (Finset.card_eq_sum_card_fiberwise
          (s := S) (t := (Finset.univ : Finset δ)) (f := Prod.fst)
          (fun _ _ ↦ Finset.mem_univ _))

/-- A sum over a pair support is the sum over its exact label fibers. -/
theorem sum_groupedFiberSupport {δ e R : Type*} [Fintype δ]
    [DecidableEq δ] [DecidableEq e] [AddCommMonoid R]
    (S : Finset (δ × e)) (c : δ → e → R) :
    ∑ i, ∑ x ∈ groupedFiberSupport S i, c i x =
      ∑ p ∈ S, c p.1 p.2 := by
  classical
  rw [← Finset.sum_fiberwise S (fun p : δ × e ↦ p.1) (fun p ↦ c p.1 p.2)]
  apply Finset.sum_congr rfl
  intro i _
  let T := S.filter fun p ↦ p.1 = i
  have hinj : Set.InjOn (fun p : δ × e ↦ p.2) (T : Set (δ × e)) := by
    intro p hp q hq hpq
    have hpi : p.1 = i := (Finset.mem_filter.mp hp).2
    have hqi : q.1 = i := (Finset.mem_filter.mp hq).2
    exact Prod.ext (hpi.trans hqi.symm) hpq
  change ∑ x ∈ T.image (fun p : δ × e ↦ p.2), c i x = ∑ p ∈ T, c p.1 p.2
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

/-- One total top-`K` selection for label-dependent probability weights.

The selected triples are grouped to a support in `δ × e`.  Its cardinality is
at most `K`, and its `c`-mass dominates the top-`K` mass of
`c i x * λ i a`. -/
theorem exists_grouped_topWeightMass_support
    {δ e a : Type*} [Fintype δ] [Fintype e] [Fintype a]
    (K : ℕ) (c : δ → e → ℝ) (lam : δ → a → ℝ)
    (hc : ∀ i x, 0 ≤ c i x) (hlam : ∀ i x, 0 ≤ lam i x)
    (hlam_sum : ∀ i, ∑ x, lam i x = 1) :
    ∃ S : Finset (δ × e), S.card ≤ K ∧
      topWeightMass K (fun p : δ × (e × a) ↦ c p.1 p.2.1 * lam p.1 p.2.2) ≤
        ∑ p ∈ S, c p.1 p.2 := by
  classical
  let w : δ × (e × a) → ℝ := fun p ↦ c p.1 p.2.1 * lam p.1 p.2.2
  let reassoc : (δ × e) × a ≃ δ × (e × a) := Equiv.prodAssoc δ e a
  obtain ⟨J, hJcard, hJmass⟩ :=
    exists_topWeightMass_support K (fun p : (δ × e) × a ↦ w (reassoc p))
  let S : Finset (δ × e) := J.image Prod.fst
  refine ⟨S, (Finset.card_image_le.trans hJcard), ?_⟩
  have hsub : J ⊆ S ×ˢ (Finset.univ : Finset a) := by
    intro p hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem Prod.fst hp, Finset.mem_univ _⟩
  have hselected :
      ∑ p ∈ J, w (reassoc p) ≤ ∑ p ∈ S, c p.1 p.2 := by
    calc
      ∑ p ∈ J, w (reassoc p) ≤
          ∑ p ∈ S ×ˢ (Finset.univ : Finset a), w (reassoc p) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ ↦ mul_nonneg (hc p.1.1 p.1.2) (hlam p.1.1 p.2))
      _ = ∑ p ∈ S, c p.1 p.2 := by
        rw [Finset.sum_product]
        change (∑ p ∈ S, ∑ x, c p.1 p.2 * lam p.1 x) = _
        simp_rw [← Finset.mul_sum, hlam_sum, mul_one]
  rw [← topWeightMass_reindex reassoc K w, hJmass]
  exact hselected

/-- Fiber form of `exists_grouped_topWeightMass_support`.  The exact fiber
cardinality identity makes the single total rank budget explicit. -/
theorem exists_grouped_topWeightMass_fibers
    {δ e a : Type*} [Fintype δ] [Fintype e] [Fintype a]
    (K : ℕ) (c : δ → e → ℝ) (lam : δ → a → ℝ)
    (hc : ∀ i x, 0 ≤ c i x) (hlam : ∀ i x, 0 ≤ lam i x)
    (hlam_sum : ∀ i, ∑ x, lam i x = 1) :
    ∃ s : δ → Finset e, (∑ i, (s i).card) ≤ K ∧
      topWeightMass K (fun p : δ × (e × a) ↦ c p.1 p.2.1 * lam p.1 p.2.2) ≤
        ∑ i, ∑ x ∈ s i, c i x := by
  classical
  obtain ⟨S, hScard, hmass⟩ :=
    exists_grouped_topWeightMass_support K c lam hc hlam hlam_sum
  refine ⟨groupedFiberSupport S, ?_, ?_⟩
  · rw [sum_card_groupedFiberSupport]
    exact hScard
  · rw [sum_groupedFiberSupport]
    exact hmass

end NLQCLean
