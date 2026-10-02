import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear differential equations on intervals

For a continuous family of bounded linear operators `A` on an interval `J`
and an initial value at `t₀ ∈ J`, the equation `y' = A(t) y` has exactly one
solution on `J`, and that solution is continuously differentiable
(`fact:linear-ode`). Local Picard–Lindelöf steps of uniform length on compact
subintervals are glued; uniqueness uses the Gronwall-based Mathlib theorem.
-/

noncomputable section

namespace NLQCLean

open Set Metric Filter
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `y` solves `y' = A(t) y` within `J` at every point of `J`. -/
def IsLinearODESol (A : ℝ → E →L[ℝ] E) (J : Set ℝ) (y : ℝ → E) : Prop :=
  ∀ t ∈ J, HasDerivWithinAt y (A t (y t)) J t

section Local

/-- **One Picard–Lindelöf step.** On an interval of length at most
`1 / (2C)`, where `C` bounds the operator norm, a solution exists for every
initial value. -/
theorem exists_isLinearODESol_step (A : ℝ → E →L[ℝ] E) {lo hi s : ℝ} (hs : s ∈ Icc lo hi)
    {C : ℝ≥0} (hA : ContinuousOn A (Icc lo hi)) (hbound : ∀ t ∈ Icc lo hi, ‖A t‖₊ ≤ C)
    (hlen : (C : ℝ) * (hi - lo) ≤ 1 / 2) (x : E) :
    ∃ y : ℝ → E, y s = x ∧ IsLinearODESol A (Icc lo hi) y := by
  let R : ℝ≥0 := ⟨‖x‖ + 1, by positivity⟩
  let L : ℝ≥0 := C * (‖x‖₊ + R)
  have hR : (R : ℝ) = ‖x‖ + 1 := rfl
  have hL : (L : ℝ) = C * (‖x‖ + (‖x‖ + 1)) := by
    simp only [L, NNReal.coe_mul, NNReal.coe_add, coe_nnnorm, hR]
  have hpl : IsPicardLindelof (fun t z => A t z) (⟨s, hs⟩ : Icc lo hi) x R 0 L C := by
    refine ⟨fun t ht => ((A t).lipschitzWith.weaken (hbound t ht)).lipschitzOnWith,
      fun z _ => hA.clm_apply continuousOn_const, fun t ht z hz => ?_, ?_⟩
    · have hz' : ‖z‖ ≤ ‖x‖ + R := by
        have := norm_le_of_mem_closedBall hz
        have h2 : ‖z‖ ≤ ‖x‖ + ‖z - x‖ := by
          calc ‖z‖ = ‖x + (z - x)‖ := by abel_nf
            _ ≤ ‖x‖ + ‖z - x‖ := norm_add_le _ _
        rw [mem_closedBall, dist_eq_norm] at hz
        linarith
      calc ‖A t z‖ ≤ ‖A t‖ * ‖z‖ := (A t).le_opNorm z
        _ ≤ C * (‖x‖ + R) := by
          gcongr
          exact_mod_cast hbound t ht
        _ = L := by rw [hL, hR]
    · have hmax : max (hi - s) (s - lo) ≤ hi - lo := max_le (by linarith [hs.1]) (by linarith [hs.2])
      have hmax0 : 0 ≤ max (hi - s) (s - lo) := le_max_of_le_left (by linarith [hs.2])
      simp only [NNReal.coe_zero, sub_zero]
      calc (L : ℝ) * max (hi - s) (s - lo) ≤ L * (hi - lo) :=
            mul_le_mul_of_nonneg_left hmax L.2
        _ = (‖x‖ + (‖x‖ + 1)) * (C * (hi - lo)) := by rw [hL]; ring
        _ ≤ (‖x‖ + (‖x‖ + 1)) * (1 / 2) := by gcongr
        _ ≤ R := by rw [hR]; nlinarith [norm_nonneg x]
  obtain ⟨y, hy0, hy⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨y, hy0, hy⟩

end Local

section Gluing

omit [CompleteSpace E] in
/-- Two solutions on adjacent closed intervals agreeing at the junction glue
to a solution on the union. -/
theorem isLinearODESol_glue (A : ℝ → E →L[ℝ] E) {a τ b : ℝ} (haτ : a ≤ τ) (hτb : τ ≤ b)
    {y z : ℝ → E} (hy : IsLinearODESol A (Icc a τ) y) (hz : IsLinearODESol A (Icc τ b) z)
    (hyz : y τ = z τ) :
    IsLinearODESol A (Icc a b) (fun t => if t ≤ τ then y t else z t) := by
  set w : ℝ → E := fun t => if t ≤ τ then y t else z t
  have hwy : ∀ t ∈ Icc a τ, w t = y t := fun t ht => ite_eq_left ht.2
  have hwz : ∀ t ∈ Icc τ b, w t = z t := by
    intro t ht
    by_cases h : t ≤ τ
    · have : t = τ := le_antisymm h ht.1
      subst this
      simp [w, hyz]
    · exact ite_eq_right h
  intro t ht
  rcases lt_trichotomy t τ with h | h | h
  · have hmem : Icc a τ ∈ 𝓝[Icc a b] t := by
      refine mem_nhdsWithin.mpr ⟨Iio τ, isOpen_Iio, h, fun u hu => ⟨hu.2.1, le_of_lt hu.1⟩⟩
    have hd : HasDerivWithinAt w (A t (y t)) (Icc a τ) t :=
      (hy t ⟨ht.1, h.le⟩).congr_of_mem hwy ⟨ht.1, h.le⟩
    rw [hwy t ⟨ht.1, h.le⟩]
    exact hd.mono_of_mem_nhdsWithin hmem
  · subst h
    have h1 : HasDerivWithinAt w (A t (w t)) (Icc a t) t := by
      have := (hy t ⟨haτ, le_rfl⟩).congr_of_mem hwy ⟨haτ, le_rfl⟩
      rwa [← hwy t ⟨haτ, le_rfl⟩] at this
    have h2 : HasDerivWithinAt w (A t (w t)) (Icc t b) t := by
      have := (hz t ⟨le_rfl, hτb⟩).congr_of_mem hwz ⟨le_rfl, hτb⟩
      rwa [← hwz t ⟨le_rfl, hτb⟩] at this
    rw [← Icc_union_Icc_eq_Icc haτ hτb]
    exact h1.union h2
  · have hmem : Icc τ b ∈ 𝓝[Icc a b] t := by
      refine mem_nhdsWithin.mpr ⟨Ioi τ, isOpen_Ioi, h, fun u hu => ⟨le_of_lt hu.1, hu.2.2⟩⟩
    have hd := (hz t ⟨h.le, ht.2⟩).congr_of_mem hwz ⟨h.le, ht.2⟩
    rw [← hwz t ⟨h.le, ht.2⟩] at hd
    exact hd.mono_of_mem_nhdsWithin hmem

omit [CompleteSpace E] in
/-- A solution restricts to every subinterval. -/
theorem IsLinearODESol.mono {A : ℝ → E →L[ℝ] E} {J K : Set ℝ} {y : ℝ → E}
    (hy : IsLinearODESol A J y) (hKJ : K ⊆ J) : IsLinearODESol A K y :=
  fun t ht => (hy t (hKJ ht)).mono hKJ

end Gluing

section Compact

omit [CompleteSpace E] in
/-- Continuous operator families are bounded on compact intervals. -/
theorem exists_nnnorm_bound (A : ℝ → E →L[ℝ] E) {a b : ℝ} (hA : ContinuousOn A (Icc a b)) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ t ∈ Icc a b, ‖A t‖₊ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  refine ⟨⟨max C 1, le_max_of_le_right zero_le_one⟩, ?_, fun t ht => ?_⟩
  · change (0 : ℝ) < max C 1
    exact lt_max_of_lt_right zero_lt_one
  · change ‖A t‖ ≤ max C 1
    exact (hC t ht).trans (le_max_left _ _)

/-- **Existence to the right** on a compact interval. -/
theorem exists_isLinearODESol_Icc_right (A : ℝ → E →L[ℝ] E) {t₀ b : ℝ} (hb : t₀ ≤ b)
    (hA : ContinuousOn A (Icc t₀ b)) (x : E) :
    ∃ y : ℝ → E, y t₀ = x ∧ IsLinearODESol A (Icc t₀ b) y := by
  obtain ⟨C, hC, hbound⟩ := exists_nnnorm_bound A hA
  set h : ℝ := 1 / (2 * C) with hh
  have hpos : 0 < h := by positivity
  have hCh : (C : ℝ) * h = 1 / 2 := by rw [hh]; field_simp
  let τ : ℕ → ℝ := fun k => min b (t₀ + k * h)
  have hτ0 : τ 0 = t₀ := by simp [τ, hb]
  have hτmono : ∀ k, τ k ≤ τ (k + 1) := fun k => min_le_min le_rfl (by push_cast; nlinarith)
  have hτge : ∀ k, t₀ ≤ τ k := fun k => le_min hb (by nlinarith [k.cast_nonneg (α := ℝ)])
  have hτle : ∀ k, τ k ≤ b := fun k => min_le_left _ _
  have hstep : ∀ k, (C : ℝ) * (τ (k + 1) - τ k) ≤ 1 / 2 := by
    intro k
    have : τ (k + 1) - τ k ≤ h := by
      simp only [τ]
      rcases le_total b (t₀ + k * h) with hk | hk
      · rw [min_eq_left hk, min_eq_left (le_trans hk (by push_cast; nlinarith))]
        simp [hpos.le]
      · rw [min_eq_right hk]
        have := min_le_right b (t₀ + ((k + 1 : ℕ) : ℝ) * h)
        push_cast at this ⊢
        linarith
    calc (C : ℝ) * (τ (k + 1) - τ k) ≤ C * h := by gcongr
      _ = 1 / 2 := hCh
  have hind : ∀ k, ∃ y : ℝ → E, y t₀ = x ∧ IsLinearODESol A (Icc t₀ (τ k)) y := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => x, rfl, ?_⟩
      rw [hτ0, Icc_self]
      intro t ht
      rw [mem_singleton_iff] at ht
      rw [ht]
      have hnot : ¬ AccPt t₀ (𝓟 {t₀}) := by
        rw [accPt_iff_clusterPt, inf_principal]
        simp [ClusterPt]
      exact HasFDerivWithinAt.of_not_accPt hnot
    | succ k ih =>
      obtain ⟨y, hy0, hy⟩ := ih
      obtain ⟨z, hz0, hz⟩ := exists_isLinearODESol_step A ⟨le_rfl, hτmono k⟩
        (hA.mono (Icc_subset_Icc (hτge k) (hτle (k + 1))))
        (fun t ht => hbound t ⟨(hτge k).trans ht.1, ht.2.trans (hτle (k + 1))⟩)
        (hstep k) (y (τ k))
      refine ⟨fun t => if t ≤ τ k then y t else z t, by simp [hτge k, hy0], ?_⟩
      exact isLinearODESol_glue A (hτge k) (hτmono k) hy hz hz0.symm
  obtain ⟨N, hN⟩ := exists_nat_ge ((b - t₀) / h)
  obtain ⟨y, hy0, hy⟩ := hind N
  have hτN : τ N = b := by
    apply min_eq_left
    have : (b - t₀) / h * h ≤ N * h := by gcongr
    rw [div_mul_cancel₀ _ hpos.ne'] at this
    linarith
  rw [hτN] at hy
  exact ⟨y, hy0, hy⟩

/-- **Existence to the left**, by time reversal. -/
theorem exists_isLinearODESol_Icc_left (A : ℝ → E →L[ℝ] E) {a t₀ : ℝ} (ha : a ≤ t₀)
    (hA : ContinuousOn A (Icc a t₀)) (x : E) :
    ∃ y : ℝ → E, y t₀ = x ∧ IsLinearODESol A (Icc a t₀) y := by
  let B : ℝ → E →L[ℝ] E := fun t => -A (-t)
  have hB : ContinuousOn B (Icc (-t₀) (-a)) := by
    refine (hA.comp continuousOn_neg ?_).neg
    intro t ht
    exact ⟨le_neg.mp ht.2, neg_le.mp ht.1⟩
  obtain ⟨z, hz0, hz⟩ := exists_isLinearODESol_Icc_right B (neg_le_neg ha) hB x
  refine ⟨fun t => z (-t), by simpa using hz0, fun t ht => ?_⟩
  have hmaps : MapsTo Neg.neg (Icc a t₀) (Icc (-t₀) (-a)) :=
    fun u hu => ⟨neg_le_neg hu.2, neg_le_neg hu.1⟩
  have h := (hz (-t) (hmaps ht)).scomp t (hasDerivAt_neg t).hasDerivWithinAt hmaps
  simp only [B, neg_neg, Function.comp_def] at h
  simpa using h

/-- **Existence on a compact interval** around the initial time. -/
theorem exists_isLinearODESol_Icc (A : ℝ → E →L[ℝ] E) {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hA : ContinuousOn A (Icc a b)) (x : E) :
    ∃ y : ℝ → E, y t₀ = x ∧ IsLinearODESol A (Icc a b) y := by
  obtain ⟨yl, hyl0, hyl⟩ := exists_isLinearODESol_Icc_left A ht₀.1
    (hA.mono (Icc_subset_Icc le_rfl ht₀.2)) x
  obtain ⟨yr, hyr0, hyr⟩ := exists_isLinearODESol_Icc_right A ht₀.2
    (hA.mono (Icc_subset_Icc ht₀.1 le_rfl)) x
  exact ⟨_, by simp [hyl0], isLinearODESol_glue A ht₀.1 ht₀.2 hyl hyr (hyl0.trans hyr0.symm)⟩

omit [CompleteSpace E] in
/-- **Uniqueness on a compact interval.** -/
theorem IsLinearODESol.eqOn_Icc {A : ℝ → E →L[ℝ] E} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hA : ContinuousOn A (Icc a b)) {y z : ℝ → E}
    (hy : IsLinearODESol A (Icc a b) y) (hz : IsLinearODESol A (Icc a b) z)
    (h0 : y t₀ = z t₀) : EqOn y z (Icc a b) := by
  obtain ⟨C, -, hbound⟩ := exists_nnnorm_bound A hA
  have hyc : ContinuousOn y (Icc a b) := fun t ht => (hy t ht).continuousWithinAt
  have hzc : ContinuousOn z (Icc a b) := fun t ht => (hz t ht).continuousWithinAt
  have hlip : ∀ t ∈ Icc a b, LipschitzOnWith C (fun w => A t w) univ := fun t ht =>
    ((A t).lipschitzWith.weaken (hbound t ht)).lipschitzOnWith
  have hright : EqOn y z (Icc t₀ b) := by
    refine ODE_solution_unique_of_mem_Icc_right (v := fun t w => A t w) (s := fun _ => univ)
      (K := C) (fun t ht => hlip t ⟨ht₀.1.trans ht.1, ht.2.le⟩)
      (hyc.mono (Icc_subset_Icc ht₀.1 le_rfl)) ?_ (fun _ _ => mem_univ _)
      (hzc.mono (Icc_subset_Icc ht₀.1 le_rfl)) ?_ (fun _ _ => mem_univ _) h0
    · intro t ht
      have hmem : Icc a b ∈ 𝓝[Ici t] t :=
        mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc (ht₀.1.trans ht.1) le_rfl)
      exact (hy t ⟨ht₀.1.trans ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin hmem
    · intro t ht
      have hmem : Icc a b ∈ 𝓝[Ici t] t :=
        mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc (ht₀.1.trans ht.1) le_rfl)
      exact (hz t ⟨ht₀.1.trans ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin hmem
  have hleft : EqOn y z (Icc a t₀) := by
    refine ODE_solution_unique_of_mem_Icc_left (v := fun t w => A t w) (s := fun _ => univ)
      (K := C) (fun t ht => hlip t ⟨ht.1.le, ht.2.trans ht₀.2⟩)
      (hyc.mono (Icc_subset_Icc le_rfl ht₀.2)) ?_ (fun _ _ => mem_univ _)
      (hzc.mono (Icc_subset_Icc le_rfl ht₀.2)) ?_ (fun _ _ => mem_univ _) h0
    · intro t ht
      have hmem : Icc a b ∈ 𝓝[Iic t] t :=
        mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc le_rfl (ht.2.trans ht₀.2))
      exact (hy t ⟨ht.1.le, ht.2.trans ht₀.2⟩).mono_of_mem_nhdsWithin hmem
    · intro t ht
      have hmem : Icc a b ∈ 𝓝[Iic t] t :=
        mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc le_rfl (ht.2.trans ht₀.2))
      exact (hz t ⟨ht.1.le, ht.2.trans ht₀.2⟩).mono_of_mem_nhdsWithin hmem
  intro t ht
  rcases le_total t t₀ with h | h
  · exact hleft ⟨ht.1, h⟩
  · exact hright ⟨h, ht.2⟩

end Compact

section Interval

variable {A : ℝ → E →L[ℝ] E} {J : Set ℝ}

omit [CompleteSpace E] in
/-- Every derivative holds within a set having no other point near `t`. -/
theorem hasDerivWithinAt_of_subset_singleton {f : ℝ → E} {f' : E} {s : Set ℝ} {t : ℝ}
    (hs : s ⊆ {t}) : HasDerivWithinAt f f' s t := by
  have hnot : ¬ AccPt t (𝓟 s) := by
    rw [accPt_iff_nhds]
    push Not
    exact ⟨univ, univ_mem, fun u hu => hs hu.2⟩
  exact HasFDerivWithinAt.of_not_accPt hnot

omit [CompleteSpace E] in
/-- **Uniqueness on an interval.** -/
theorem IsLinearODESol.eqOn (hJ : J.OrdConnected) (hA : ContinuousOn A J) {t₀ : ℝ}
    (ht₀ : t₀ ∈ J) {y z : ℝ → E} (hy : IsLinearODESol A J y) (hz : IsLinearODESol A J z)
    (h0 : y t₀ = z t₀) : EqOn y z J := by
  intro t ht
  have hsub : Icc (min t₀ t) (max t₀ t) ⊆ J := hJ.uIcc_subset ht₀ ht
  exact (hy.mono hsub).eqOn_Icc ⟨min_le_left _ _, le_max_left _ _⟩ (hA.mono hsub)
    (hz.mono hsub) h0 ⟨min_le_right _ _, le_max_right _ _⟩

/-- **Existence on an interval.** -/
theorem exists_isLinearODESol (hJ : J.OrdConnected) (hA : ContinuousOn A J) {t₀ : ℝ}
    (ht₀ : t₀ ∈ J) (x : E) : ∃ y : ℝ → E, y t₀ = x ∧ IsLinearODESol A J y := by
  classical
  have hsol : ∀ t, ∃ w : ℝ → E, w t₀ = x ∧
      (t ∈ J → IsLinearODESol A (Icc (min t₀ t) (max t₀ t)) w) := by
    intro t
    by_cases ht : t ∈ J
    · obtain ⟨w, hw0, hw⟩ := exists_isLinearODESol_Icc A
        (⟨min_le_left _ _, le_max_left _ _⟩ : t₀ ∈ Icc (min t₀ t) (max t₀ t))
        (hA.mono (hJ.uIcc_subset ht₀ ht)) x
      exact ⟨w, hw0, fun _ => hw⟩
    · exact ⟨fun _ => x, rfl, fun h => absurd h ht⟩
  choose w hw0 hw using hsol
  let y : ℝ → E := fun t => w t t
  -- `y` agrees with every compact-interval solution through `t₀`.
  have hagree : ∀ {a b : ℝ} (v : ℝ → E), Icc a b ⊆ J → t₀ ∈ Icc a b → v t₀ = x →
      IsLinearODESol A (Icc a b) v → EqOn y v (Icc a b) := by
    intro a b v hab hab0 hv0 hv u hu
    have huJ : u ∈ J := hab hu
    have hsub : Icc (min t₀ u) (max t₀ u) ⊆ Icc a b :=
      Icc_subset_Icc (le_min hab0.1 hu.1) (max_le hab0.2 hu.2)
    exact ((hw u huJ).eqOn_Icc ⟨min_le_left _ _, le_max_left _ _⟩
      (hA.mono (hsub.trans hab)) (hv.mono hsub) ((hw0 u).trans hv0.symm))
      ⟨min_le_right _ _, le_max_right _ _⟩
  have hy0 : y t₀ = x := hw0 t₀
  refine ⟨y, hy0, fun t ht => ?_⟩
  -- Derivative on the two sides of `t`, then union.
  have hleft : HasDerivWithinAt y (A t (y t)) (J ∩ Iic t) t := by
    by_cases hl : ∃ u ∈ J, u < t
    · obtain ⟨u, huJ, hut⟩ := hl
      set a := min u t₀
      set b := max t t₀
      have haJ : a ∈ J := by rcases min_choice u t₀ with h | h <;> simp only [a, h] <;> assumption
      have hbJ : b ∈ J := by rcases max_choice t t₀ with h | h <;> simp only [b, h] <;> assumption
      have hab : Icc a b ⊆ J := hJ.out haJ hbJ
      have ht0 : t₀ ∈ Icc a b := ⟨min_le_right _ _, le_max_right _ _⟩
      have htI : t ∈ Icc a b := ⟨(min_le_left _ _).trans hut.le, le_max_left _ _⟩
      obtain ⟨v, hv0, hv⟩ := exists_isLinearODESol_Icc A ht0 (hA.mono hab) x
      have heq := hagree v hab ht0 hv0 hv
      have hd : HasDerivWithinAt y (A t (y t)) (Icc a b) t := by
        rw [heq htI]
        exact (hv t htI).congr_of_mem heq htI
      have hmem : Icc a b ∈ 𝓝[J ∩ Iic t] t := by
        refine mem_nhdsWithin.mpr ⟨Ioi u, isOpen_Ioi, hut, fun v hv => ?_⟩
        exact ⟨(min_le_left _ _).trans hv.1.le, hv.2.2.trans (le_max_left _ _)⟩
      exact hd.mono_of_mem_nhdsWithin hmem
    · push Not at hl
      exact hasDerivWithinAt_of_subset_singleton fun u hu =>
        le_antisymm hu.2 (hl u hu.1)
  have hright : HasDerivWithinAt y (A t (y t)) (J ∩ Ici t) t := by
    by_cases hr : ∃ u ∈ J, t < u
    · obtain ⟨u, huJ, htu⟩ := hr
      set a := min t t₀
      set b := max u t₀
      have haJ : a ∈ J := by rcases min_choice t t₀ with h | h <;> simp only [a, h] <;> assumption
      have hbJ : b ∈ J := by rcases max_choice u t₀ with h | h <;> simp only [b, h] <;> assumption
      have hab : Icc a b ⊆ J := hJ.out haJ hbJ
      have ht0 : t₀ ∈ Icc a b := ⟨min_le_right _ _, le_max_right _ _⟩
      have htI : t ∈ Icc a b := ⟨min_le_left _ _, htu.le.trans (le_max_left _ _)⟩
      obtain ⟨v, hv0, hv⟩ := exists_isLinearODESol_Icc A ht0 (hA.mono hab) x
      have heq := hagree v hab ht0 hv0 hv
      have hd : HasDerivWithinAt y (A t (y t)) (Icc a b) t := by
        rw [heq htI]
        exact (hv t htI).congr_of_mem heq htI
      have hmem : Icc a b ∈ 𝓝[J ∩ Ici t] t := by
        refine mem_nhdsWithin.mpr ⟨Iio u, isOpen_Iio, htu, fun v hv => ?_⟩
        exact ⟨(min_le_left _ _).trans hv.2.2, hv.1.le.trans (le_max_left _ _)⟩
      exact hd.mono_of_mem_nhdsWithin hmem
    · push Not at hr
      exact hasDerivWithinAt_of_subset_singleton fun u hu =>
        le_antisymm (hr u hu.1) hu.2
  have hJ' : J = (J ∩ Iic t) ∪ (J ∩ Ici t) := by
    rw [← inter_union_distrib_left, Iic_union_Ici, inter_univ]
  rw [hJ']
  exact hleft.union hright

/-- **`fact:linear-ode`.** On an interval `J`, for a continuous operator family
`A` and initial data at `t₀ ∈ J`, the equation `y' = A(t) y` has a solution,
it is continuously differentiable on `J` (its derivative `A(t) y(t)` is
continuous), and every solution with the same initial value agrees with it
on `J`. -/
theorem linearODE_existsUnique (hJ : J.OrdConnected) (hA : ContinuousOn A J) {t₀ : ℝ}
    (ht₀ : t₀ ∈ J) (x : E) :
    ∃ y : ℝ → E, y t₀ = x ∧ IsLinearODESol A J y ∧
      ContinuousOn (fun t => A t (y t)) J ∧
      ∀ z : ℝ → E, z t₀ = x → IsLinearODESol A J z → EqOn z y J := by
  obtain ⟨y, hy0, hy⟩ := exists_isLinearODESol hJ hA ht₀ x
  refine ⟨y, hy0, hy, ?_, fun z hz0 hz => hz.eqOn hJ hA ht₀ hy (hz0.trans hy0.symm)⟩
  exact hA.clm_apply fun t ht => (hy t ht).continuousWithinAt

end Interval

section MatrixForm

open scoped Matrix

variable {n : Type*} [Fintype n]

/-- Matrix multiplication as a real continuous linear map on `ℂ^n`. -/
def mulVecCLM (M : Matrix n n ℂ) : (n → ℂ) →L[ℝ] (n → ℂ) :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin M).restrictScalars ℝ)

@[simp] theorem mulVecCLM_apply (M : Matrix n n ℂ) (v : n → ℂ) : mulVecCLM M v = M *ᵥ v := rfl

/-- `M ↦ (v ↦ M v)` is real linear, hence continuous. -/
def mulVecCLMLinear : Matrix n n ℂ →ₗ[ℝ] ((n → ℂ) →L[ℝ] (n → ℂ)) where
  toFun := mulVecCLM
  map_add' M N := by
    ext v i
    simp only [mulVecCLM_apply, add_apply, Matrix.add_mulVec, Pi.add_apply]
  map_smul' r M := by
    ext v i
    simp only [mulVecCLM_apply, smul_apply, RingHom.id_apply,
      Matrix.smul_mulVec, Pi.smul_apply]

theorem continuous_mulVecCLM : Continuous (mulVecCLM : Matrix n n ℂ → _) :=
  (mulVecCLMLinear (n := n)).continuous_of_finiteDimensional

/-- **`fact:linear-ode`, matrix form.** For `A : J → ℂ^{n×n}` continuous on an
interval `J`, `t₀ ∈ J` and `y₀ ∈ ℂ^n`, the equation `y' = A(t) y` with
`y(t₀) = y₀` has exactly one continuously differentiable solution on `J`. -/
theorem linearODE_existsUnique_matrix {J : Set ℝ} (hJ : J.OrdConnected)
    {A : ℝ → Matrix n n ℂ} (hA : ContinuousOn A J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (y₀ : n → ℂ) :
    ∃ y : ℝ → n → ℂ, y t₀ = y₀ ∧ (∀ t ∈ J, HasDerivWithinAt y (A t *ᵥ y t) J t) ∧
      ContinuousOn (fun t => A t *ᵥ y t) J ∧
      ∀ z : ℝ → n → ℂ, z t₀ = y₀ → (∀ t ∈ J, HasDerivWithinAt z (A t *ᵥ z t) J t) →
        EqOn z y J := by
  have hA' : ContinuousOn (fun t => mulVecCLM (A t)) J := continuous_mulVecCLM.comp_continuousOn hA
  obtain ⟨y, hy0, hy, hyc, huniq⟩ := linearODE_existsUnique hJ hA' ht₀ y₀
  exact ⟨y, hy0, hy, hyc, fun z hz0 hz => huniq z hz0 hz⟩

end MatrixForm

end NLQCLean
