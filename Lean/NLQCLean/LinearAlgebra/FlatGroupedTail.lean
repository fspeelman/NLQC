import NLQCLean.LinearAlgebra.FlatProductTail

/-!
# Top-mass tails of grouped products with flat fibres

* `sum_mul_le_topWeightMass_of_fractional`: a fractional selection `0 ≤ x ≤ 1` of total
  weight at most `m` captures at most the top-`m` mass of nonnegative weights.
* `topWeightMass_grouped_le_of_flat`: if each group `p` carries a weight
  `a p` spread over `D` fibre entries `b p e ≥ β` summing to one, then the
  top-`K` mass of the products, for `K ≤ m D`, misses at least `β D` times the
  mass of `a` outside its top `m` entries.
-/

namespace NLQCLean

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Fractional top mass.** -/
theorem sum_mul_le_topWeightMass_of_fractional (a x : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i ≤ 1) (m : ℕ) (hm : ∑ i, x i ≤ m) :
    ∑ i, a i * x i ≤ topWeightMass m a := by
  obtain ⟨T, hTcard, hT⟩ := exists_topWeightMass_support m a
  have hopt : ∀ S : Finset ι, S.card ≤ m → ∑ i ∈ S, a i ≤ ∑ i ∈ T, a i :=
    fun S hS => hT ▸ sum_le_topWeightMass a hS
  rw [hT]
  have hsplit (f : ι → ℝ) : ∑ i, f i = ∑ i ∈ T, f i + ∑ i ∈ Tᶜ, f i :=
    (Finset.sum_add_sum_compl T f).symm
  have hTax : ∑ i ∈ T, a i * x i ≤ ∑ i ∈ T, a i :=
    Finset.sum_le_sum fun i _ => by nlinarith [ha i, hx1 i]
  by_cases hfull : T.card = m
  · have hex : ∀ p ∉ T, ∀ q ∈ T, a p ≤ a q := by
      intro p hp q hq
      have hcard : (insert p (T.erase q)).card ≤ m := by
        have hpos : 0 < T.card := Finset.card_pos.mpr ⟨q, hq⟩
        rw [Finset.card_insert_of_notMem (fun h => hp (Finset.mem_of_mem_erase h)),
          Finset.card_erase_of_mem hq]
        omega
      have h := hopt _ hcard
      rw [Finset.sum_insert (fun h => hp (Finset.mem_of_mem_erase h)),
        Finset.sum_erase_eq_sub hq] at h
      linarith
    rcases T.eq_empty_or_nonempty with hTe | hTn
    · have hm0 : m = 0 := by rw [← hfull, hTe, Finset.card_empty]
      rw [hm0, Nat.cast_zero] at hm
      have hx : ∀ i, x i = 0 := fun i =>
        le_antisymm ((Finset.single_le_sum (fun j _ => hx0 j) (Finset.mem_univ i)).trans hm)
          (hx0 i)
      simp [hx, hTe]
    · set θ := T.inf' hTn a
      have hθT : ∀ q ∈ T, θ ≤ a q := fun q hq => Finset.inf'_le _ hq
      have hθout : ∀ p ∉ T, a p ≤ θ := fun p hp => Finset.le_inf' _ _ fun q hq => hex p hp q hq
      obtain ⟨q₀, hq₀⟩ := hTn
      have hθ0 : 0 ≤ θ := by
        have := hθT q₀ hq₀
        exact le_trans (by
          rw [show θ = T.inf' ⟨q₀, hq₀⟩ a from rfl]
          exact Finset.le_inf' _ _ fun q _ => ha q) le_rfl
      have hout : ∑ i ∈ Tᶜ, a i * x i ≤ θ * ∑ i ∈ Tᶜ, x i := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (hθout i (Finset.mem_compl.mp hi)) (hx0 i)
      have hxs : ∑ i ∈ Tᶜ, x i ≤ ∑ i ∈ T, (1 - x i) := by
        have h1 := hsplit x
        have h2 : ∑ i ∈ T, (1 - x i) = (T.card : ℝ) - ∑ i ∈ T, x i := by
          rw [Finset.sum_sub_distrib]
          simp
        rw [h2, hfull]
        linarith
      have hin : θ * ∑ i ∈ T, (1 - x i) ≤ ∑ i ∈ T, a i * (1 - x i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (hθT i hi) (sub_nonneg.mpr (hx1 i))
      have hT1 : ∑ i ∈ T, a i * x i + ∑ i ∈ T, a i * (1 - x i) = ∑ i ∈ T, a i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsplit (fun i => a i * x i)]
      nlinarith [mul_le_mul_of_nonneg_left hxs hθ0]
  · have hz : ∀ p ∉ T, a p = 0 := by
      intro p hp
      have h := hopt (insert p T) (by rw [Finset.card_insert_of_notMem hp]; omega)
      rw [Finset.sum_insert hp] at h
      linarith [ha p]
    rw [hsplit (fun i => a i * x i)]
    have : ∑ i ∈ Tᶜ, a i * x i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hz i (Finset.mem_compl.mp hi), zero_mul]
    linarith

variable {P E : Type*} [Fintype P] [Fintype E] [DecidableEq P] [DecidableEq E]

/-- **Grouped products with flat fibres.** -/
theorem topWeightMass_grouped_le_of_flat (a : P → ℝ) (b : P → E → ℝ) (ha : ∀ p, 0 ≤ a p)
    {β : ℝ} (hβ : 0 ≤ β) (hb : ∀ p e, β ≤ b p e) (hb1 : ∀ p, ∑ e, b p e = 1)
    {K m : ℕ} (hK : K ≤ m * Fintype.card E) :
    topWeightMass K (fun q : P × E => a q.1 * b q.1 q.2) ≤
      ∑ p, a p - β * Fintype.card E * (∑ p, a p - topWeightMass m a) := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card E) with hE | hE
  · have hEe : IsEmpty E := Fintype.card_eq_zero_iff.mp hE
    have h0 : ∀ p, ∑ e, b p e = 0 := fun p => Finset.sum_of_isEmpty _
    rcases isEmpty_or_nonempty P with h | ⟨⟨p⟩⟩
    · have hT : topWeightMass K (fun q : P × E => a q.1 * b q.1 q.2) = 0 := by
        apply le_antisymm
        · apply topWeightMass_le
          intro s _
          simp [Finset.eq_empty_of_isEmpty s]
        · exact topWeightMass_nonneg _ _
      simp [hT, Finset.sum_of_isEmpty]
    · exact absurd ((h0 p).symm.trans (hb1 p)) zero_ne_one
  have hD : (0 : ℝ) < Fintype.card E := by exact_mod_cast hE
  apply topWeightMass_le
  intro S hS
  let χ : P → E → ℝ := fun p e => if (p, e) ∈ S then 1 else 0
  have hχ0 : ∀ p e, 0 ≤ χ p e := fun p e => by simp only [χ]; split_ifs <;> norm_num
  have hχ1 : ∀ p e, χ p e ≤ 1 := fun p e => by simp only [χ]; split_ifs <;> norm_num
  have hSsum : ∑ q ∈ S, a q.1 * b q.1 q.2 = ∑ p, a p * ∑ e, χ p e * b p e := by
    have h1 : ∑ q ∈ S, a q.1 * b q.1 q.2 =
        ∑ q : P × E, if q ∈ S then a q.1 * b q.1 q.2 else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [h1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [χ]
    split_ifs <;> ring
  have hcount : ∑ p, ∑ e, χ p e = S.card := by
    have h1 : ∑ p, ∑ e, χ p e = ∑ q : P × E, if q ∈ S then (1 : ℝ) else 0 := by
      rw [Fintype.sum_prod_type]
    rw [h1, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hfib : ∀ p, ∑ e, χ p e * b p e ≤ 1 - β * (Fintype.card E - ∑ e, χ p e) := by
    intro p
    have h1 : ∑ e, χ p e * b p e = ∑ e, b p e - ∑ e, (1 - χ p e) * b p e := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring
    have h2 : β * (Fintype.card E - ∑ e, χ p e) ≤ ∑ e, (1 - χ p e) * b p e := by
      have h3 : β * (Fintype.card E - ∑ e, χ p e) = ∑ e, (1 - χ p e) * β := by
        rw [← Finset.sum_mul, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        ring
      rw [h3]
      exact Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hb p e)
        (sub_nonneg.mpr (hχ1 p e))
    rw [h1, hb1 p]
    linarith
  let x : P → ℝ := fun p => (∑ e, χ p e) / Fintype.card E
  have hx0 : ∀ p, 0 ≤ x p := fun p => div_nonneg (Finset.sum_nonneg fun e _ => hχ0 p e) hD.le
  have hx1 : ∀ p, x p ≤ 1 := by
    intro p
    rw [div_le_one hD]
    calc ∑ e, χ p e ≤ ∑ _e : E, (1 : ℝ) := Finset.sum_le_sum fun e _ => hχ1 p e
      _ = Fintype.card E := by simp
  have hxm : ∑ p, x p ≤ m := by
    rw [← Finset.sum_div, hcount, div_le_iff₀ hD]
    have : (S.card : ℝ) ≤ K := by exact_mod_cast hS
    have hK' : (K : ℝ) ≤ m * Fintype.card E := by exact_mod_cast hK
    linarith
  have hknap := sum_mul_le_topWeightMass_of_fractional a x ha hx0 hx1 m hxm
  have hn : ∑ p, a p * ∑ e, χ p e = Fintype.card E * ∑ p, a p * x p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [x]
    field_simp
  rw [hSsum]
  calc ∑ p, a p * ∑ e, χ p e * b p e
      ≤ ∑ p, a p * (1 - β * (Fintype.card E - ∑ e, χ p e)) :=
        Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hfib p) (ha p)
    _ = ∑ p, a p - β * Fintype.card E * ∑ p, a p + β * ∑ p, a p * ∑ e, χ p e := by
        have hpt : ∀ p, a p * (1 - β * (Fintype.card E - ∑ e, χ p e)) =
            a p - β * Fintype.card E * a p + β * (a p * ∑ e, χ p e) := fun p => by ring
        simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ ≤ _ := by
        rw [hn]
        have : β * (Fintype.card E * ∑ p, a p * x p) ≤ β * (Fintype.card E * topWeightMass m a) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hknap hD.le) hβ
        nlinarith

end NLQCLean
