import NLQCLean.Semialgebraic.OneVariableContinuity

/-!
# Curve selection

If `p` lies in the closure of a semialgebraic set `A`, a semialgebraic path
starts at `p` and immediately enters `A`. Choose semialgebraically a point
`z(r) ∈ A` within distance `r` of `p`; each coordinate of `z` is continuous on
some `(0, ε)`, and `t ↦ z(εt/2)` extends continuously by `p` at `t = 0`.
-/

noncomputable section

namespace NLQCLean

open Set Filter Topology

variable {m : ℕ}

theorem sum_sq_lt_of_dist_lt {p b : Fin m → ℝ} {r : ℝ} (hr : 0 < r)
    (h : dist p b < r / (m + 1)) : ∑ i, (b i - p i) ^ 2 < r ^ 2 := by
  have hε : 0 < r / (m + 1) := by positivity
  have hi : ∀ i, (b i - p i) ^ 2 ≤ (r / (m + 1)) ^ 2 := by
    intro i
    have := (dist_pi_lt_iff hε).mp h i
    rw [Real.dist_eq, abs_sub_comm] at this
    exact (sq_le_sq' (by linarith [abs_lt.mp this]) (abs_lt.mp this).2.le)
  calc ∑ i, (b i - p i) ^ 2 ≤ ∑ _i : Fin m, (r / (m + 1)) ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = m * (r / (m + 1)) ^ 2 := by simp
    _ < r ^ 2 := by
      rw [div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith [mul_pos (mul_pos hr hr) (show (0 : ℝ) < (m : ℝ) ^ 2 + m + 1 by positivity)]

theorem abs_lt_of_sum_sq_lt {a : Fin m → ℝ} {s : ℝ} (hs : 0 ≤ s) (h : ∑ i, a i ^ 2 < s ^ 2)
    (i : Fin m) : |a i| < s :=
  abs_lt_of_sq_lt_sq ((Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)).trans_lt h) hs

/-- **Curve selection.** -/
theorem curve_selection {A : Set (Fin m → ℝ)} (hA : SAOn A) {p : Fin m → ℝ} (hp : p ∈ closure A) :
    ∃ c : ℝ → Fin m → ℝ, IsSAPath c ∧ c 0 = p ∧ ∀ t ∈ Ioc (0 : ℝ) 1, c t ∈ A := by
  classical
  let T : Set (Fin 1 ⊕ Fin m → ℝ) := {w | 0 < w (Sum.inl 0) ∧ w ∘ Sum.inr ∈ A ∧
    ∑ i, (w (Sum.inr i) - p i) ^ 2 < w (Sum.inl 0) ^ 2}
  have hT : SAOn T :=
    ((SAOn.pos (MvPolynomial.X (Sum.inl 0))).inter ((hA.comap Sum.inr).inter
      (SAOn.lt (∑ i, (MvPolynomial.X (Sum.inr i) - MvPolynomial.C (p i)) ^ 2)
        (MvPolynomial.X (Sum.inl 0) ^ 2)))).congr fun w => by simp [T]
  obtain ⟨φ, hgraph, hspec⟩ := exists_saChoice_sum hT
  let z : ℝ → Fin m → ℝ := fun r => φ fun _ => r
  have hz : ∀ r, 0 < r → z r ∈ A ∧ ∑ i, (z r i - p i) ^ 2 < r ^ 2 := by
    intro r hr
    obtain ⟨b, hbA, hb⟩ := Metric.mem_closure_iff.mp hp (r / (m + 1)) (by positivity)
    have := hspec (fun _ => r) ⟨b, hr, hbA, sum_sq_lt_of_dist_lt hr hb⟩
    exact ⟨this.2.1, this.2.2⟩
  -- each coordinate is continuous near `0⁺`
  have hcoord : ∀ i, ∃ ε > 0, ContinuousOn (fun r => z r i) (Ioo 0 ε) := by
    intro i
    refine exists_continuousOn_Ioo_of_saOn_graph ?_
    let e : Fin 1 ⊕ Fin m → Fin 2 ⊕ Fin m := Sum.elim (fun _ => Sum.inl 0) Sum.inr
    have hB : SAOn {u : Fin 2 ⊕ Fin m → ℝ | u ∘ e ∈ {w : Fin 1 ⊕ Fin m → ℝ |
        w ∘ Sum.inr = φ (w ∘ Sum.inl)} ∧ u (Sum.inr i) = u (Sum.inl 1) ∧ 0 < u (Sum.inl 0)} :=
      (hgraph.comap e).inter ((SAOn.eq (MvPolynomial.X (Sum.inr i)) (MvPolynomial.X (Sum.inl 1))).inter
        (SAOn.pos (MvPolynomial.X (Sum.inl 0)))) |>.congr fun u => by simp
    refine (SAOn.exists_sum hB).congr fun x => ?_
    simp only [mem_ofPred_eq]
    have h1 : ∀ y : Fin m → ℝ, Sum.elim x y ∘ e ∘ Sum.inr = y := fun y => rfl
    have h2 : ∀ y : Fin m → ℝ, Sum.elim x y ∘ e ∘ Sum.inl = fun _ => x 0 := fun y => rfl
    constructor
    · rintro ⟨y, hy, hyi, hx0⟩
      refine ⟨hx0, ?_⟩
      change (Sum.elim x y ∘ e) ∘ Sum.inr = φ ((Sum.elim x y ∘ e) ∘ Sum.inl) at hy
      change y i = x 1 at hyi
      rw [← hyi]
      exact congrFun hy i
    · rintro ⟨hx0, hx1⟩
      refine ⟨z (x 0), rfl, hx1.symm, hx0⟩
  choose ε hε hcont using hcoord
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ ∀ i, δ < ε i :=
    eventually_mem_nhdsWithin.and (Filter.eventually_all.mpr fun i =>
      nhdsWithin_le_nhds (Iio_mem_nhds (hε i)))
  obtain ⟨ε₀, hε₀, hε₀i⟩ := hev.exists
  have hzc : ContinuousOn z (Ioo 0 ε₀) :=
    continuousOn_pi.mpr fun i => (hcont i).mono (Ioo_subset_Ioo_right (hε₀i i).le)
  set δ := ε₀ / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  let c : ℝ → Fin m → ℝ := fun t => if t ≤ 0 then p else z (δ * t)
  have hcpos : ∀ t, 0 < t → c t = z (δ * t) := fun t ht => by simp [c, not_le.mpr ht]
  refine ⟨c, ⟨?_, ?_⟩, by simp [c], fun t ht => ?_⟩
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0
      rw [Metric.continuousWithinAt_iff]
      intro η hη
      refine ⟨η / δ, by positivity, fun t ht' hdist => ?_⟩
      have hc0 : c 0 = p := by simp [c]
      rw [hc0]
      rcases eq_or_lt_of_le ht'.1 with h0 | htpos
      · subst h0
        simpa [hc0] using hη
      · rw [hcpos t htpos]
        rw [Real.dist_eq, sub_zero, abs_of_pos htpos, lt_div_iff₀ hδ0] at hdist
        have hzt := (hz (δ * t) (by positivity)).2
        refine (dist_pi_lt_iff hη).mpr fun i => ?_
        rw [Real.dist_eq]
        have := abs_lt_of_sum_sq_lt (by positivity) hzt i
        linarith [mul_comm t δ]
    · have hin : δ * t ∈ Ioo 0 ε₀ := ⟨by positivity, by nlinarith [ht.2]⟩
      have hcz : ContinuousAt (fun s => z (δ * s)) t :=
        (hzc.continuousAt (Ioo_mem_nhds hin.1 hin.2)).comp (continuous_const.mul continuous_id).continuousAt
      have heq : c =ᶠ[𝓝 t] fun s => z (δ * s) := by
        filter_upwards [Ioi_mem_nhds hpos] with s hs
        exact hcpos s hs
      exact (hcz.congr heq.symm).continuousWithinAt
  · -- the graph
    let Q : Fin 1 ⊕ Fin m → MvPolynomial (Option (Fin m)) ℝ :=
      Sum.elim (fun _ => MvPolynomial.C δ * MvPolynomial.X none) fun i => MvPolynomial.X (some i)
    have hpos : SAOn {h : Option (Fin m) → ℝ | 0 < h none ∧ h none ≤ 1 ∧
        (fun j => MvPolynomial.eval h (Q j)) ∈ {w : Fin 1 ⊕ Fin m → ℝ |
          w ∘ Sum.inr = φ (w ∘ Sum.inl)}} :=
      (SAOn.pos (MvPolynomial.X none)).inter ((SAOn.le (MvPolynomial.X none) 1).inter
        (hgraph.preimage Q)) |>.congr fun h => by simp
    have hzero : SAOn {h : Option (Fin m) → ℝ | h none = 0 ∧ ∀ i, h (some i) = p i} :=
      (SAOn.zero (MvPolynomial.X none)).inter (SAOn.fintype_iInter fun i =>
        SAOn.eq (MvPolynomial.X (some i)) (MvPolynomial.C (p i))) |>.congr fun h => by simp
    refine (hzero.union hpos).congr fun h => ?_
    simp only [mem_union, mem_ofPred_eq, pathGraph, mem_Icc]
    have hQ1 : (fun j => MvPolynomial.eval h (Q j)) ∘ Sum.inr = fun i => h (some i) := by
      funext i
      simp [Q]
    have hQ2 : (fun j => MvPolynomial.eval h (Q j)) ∘ Sum.inl = fun _ => δ * h none := by
      funext i
      simp [Q]
    rw [hQ1, hQ2]
    constructor
    · rintro (⟨h0, hp'⟩ | ⟨hpos', hle, hφ⟩)
      · refine ⟨⟨h0.ge, by rw [h0]; exact zero_le_one⟩, fun i => ?_⟩
        simp [c, h0, hp' i]
      · refine ⟨⟨hpos'.le, hle⟩, fun i => ?_⟩
        rw [hcpos _ hpos']
        exact congrFun hφ i
    · rintro ⟨⟨h0, h1⟩, hc⟩
      rcases eq_or_lt_of_le h0 with h0' | hpos'
      · left
        refine ⟨h0'.symm, fun i => ?_⟩
        rw [hc i, ← h0']
        simp [c]
      · right
        refine ⟨hpos', h1, ?_⟩
        funext i
        rw [hc i, hcpos _ hpos']
  · rw [hcpos t ht.1]
    exact (hz _ (by nlinarith [ht.1])).1

end NLQCLean
