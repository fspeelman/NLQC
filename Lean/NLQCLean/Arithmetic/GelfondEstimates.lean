import NLQCLean.Arithmetic.GelfondLiouville

/-!
# Elementary estimates for Gelfond's method

* If `G ∣ Q` in `ℤ[i][X]` then `|Q(ζ)| ≤ |G(ζ)| 2^q (q+1) A` for `|ζ| = 1` (Mignotte's bound for
  the quotient through the Mahler measure);
* a Lipschitz bound for polynomials on the disc of radius `2`;
* some root `β` of `G` satisfies `|ζ - β|^g ≤ |G(ζ)|`.
-/

namespace NLQCLean.Gelfond

open Polynomial GaussianInt

theorem supNorm_le_of_coeff_le {p : ℂ[X]} {A : ℝ} (hA : ∀ k, ‖p.coeff k‖ ≤ A) : p.supNorm ≤ A := by
  obtain ⟨i, hi⟩ := p.exists_eq_supNorm
  rw [hi]; exact hA i

/-- **Quotient bound.** -/
theorem norm_eval_le_of_dvd {G Q : GaussianInt[X]} (hG0 : G ≠ 0) (hdvd : G ∣ Q) {q : ℕ} {A : ℝ}
    (hq : Q.natDegree ≤ q) (hA : ∀ k, ‖(Q.coeff k : ℂ)‖ ≤ A) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖(Q.map toComplex).eval ζ‖ ≤ ‖(G.map toComplex).eval ζ‖ * (2 ^ q * ((q + 1) * A)) := by
  obtain ⟨W, rfl⟩ := hdvd
  have hA0 : 0 ≤ A := (_root_.norm_nonneg _).trans (hA 0)
  by_cases hW : W = 0
  · simp [hW]; positivity
  set Gc := G.map toComplex
  set Wc := W.map toComplex
  have hGc1 : 1 ≤ Gc.mahlerMeasure := by
    refine one_le_mahlerMeasure_of_one_le_norm_leadingCoeff ?_
    rw [leadingCoeff_map_of_injective toComplex_injective]
    exact one_le_norm_toComplex (leadingCoeff_ne_zero.mpr hG0)
  have hQc : (G * W).map toComplex = Wc * Gc := by rw [Polynomial.map_mul, mul_comm]
  have hWdeg : Wc.natDegree ≤ q := by
    have h1 : Wc.natDegree ≤ (G * W).natDegree := by
      rw [natDegree_map_eq_of_injective toComplex_injective, natDegree_mul hG0 hW]; omega
    exact h1.trans hq
  have hMQ : ((G * W).map toComplex).mahlerMeasure ≤ (q + 1) * A := by
    refine (mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm _).trans ?_
    have hdeg : (((G * W).map toComplex).natDegree : ℝ) + 1 ≤ q + 1 := by
      rw [natDegree_map_eq_of_injective toComplex_injective]; exact_mod_cast Nat.succ_le_succ hq
    have hsup : ((G * W).map toComplex).supNorm ≤ A :=
      supNorm_le_of_coeff_le fun k => by rw [coeff_map]; exact hA k
    calc √(((G * W).map toComplex).natDegree + 1 : ℝ) * ((G * W).map toComplex).supNorm
        ≤ √((q : ℝ) + 1) * A := by gcongr; exact supNorm_nonneg _
      _ ≤ (q + 1) * A := by
          gcongr
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith
  have hWk : ∀ k, ‖Wc.coeff k‖ ≤ (Wc.natDegree.choose k : ℝ) * ((q + 1) * A) := fun k =>
    (norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure k Wc Gc hGc1).trans
      (by rw [← hQc]; exact mul_le_mul_of_nonneg_left hMQ (by positivity))
  have hWval : ‖Wc.eval ζ‖ ≤ 2 ^ q * ((q + 1) * A) := by
    rw [eval_eq_sum_range]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.range (Wc.natDegree + 1), ‖Wc.coeff k * ζ ^ k‖
        ≤ ∑ k ∈ Finset.range (Wc.natDegree + 1), (Wc.natDegree.choose k : ℝ) * ((q + 1) * A) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, norm_pow, hζ, one_pow, mul_one]; exact hWk k
      _ = 2 ^ Wc.natDegree * ((q + 1) * A) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose Wc.natDegree
      _ ≤ 2 ^ q * ((q + 1) * A) := by gcongr; norm_num
  rw [Polynomial.map_mul, eval_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left hWval (_root_.norm_nonneg _)

/-- **Lipschitz bound** on the disc of radius `2`. -/
theorem norm_eval_sub_eval_le {p : ℂ[X]} {q : ℕ} {A : ℝ} (hq : p.natDegree ≤ q)
    (hA : ∀ k, ‖p.coeff k‖ ≤ A) {x y : ℂ} (hx : ‖x‖ ≤ 2) (hy : ‖y‖ ≤ 2) :
    ‖p.eval x - p.eval y‖ ≤ ‖x - y‖ * ((q + 1) * (q * (A * 2 ^ q))) := by
  have hA0 : 0 ≤ A := (_root_.norm_nonneg _).trans (hA 0)
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hq), eval_eq_sum_range' (Nat.lt_succ_of_le hq),
    ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (q + 1),
      ‖p.coeff k * x ^ k - p.coeff k * y ^ k‖ ≤ ‖x - y‖ * (q * (A * 2 ^ q)) := by
    intro k hk
    have hk' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [← mul_sub, norm_mul, ← Commute.geom_sum₂_mul (Commute.all x y) k, norm_mul]
    have hgeom : ‖∑ i ∈ Finset.range k, x ^ i * y ^ (k - 1 - i)‖ ≤ q * 2 ^ q := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i ∈ Finset.range k, ‖x ^ i * y ^ (k - 1 - i)‖
          ≤ ∑ _i ∈ Finset.range k, (2 : ℝ) ^ q := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' := Finset.mem_range.mp hi
            rw [norm_mul, norm_pow, norm_pow]
            calc ‖x‖ ^ i * ‖y‖ ^ (k - 1 - i) ≤ 2 ^ i * 2 ^ (k - 1 - i) := by gcongr
              _ = 2 ^ (k - 1) := by rw [← pow_add]; congr 1; omega
              _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = k * 2 ^ q := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ q * 2 ^ q := by gcongr
    calc ‖p.coeff k‖ * (‖∑ i ∈ Finset.range k, x ^ i * y ^ (k - 1 - i)‖ * ‖x - y‖)
        ≤ A * ((q * 2 ^ q) * ‖x - y‖) := by gcongr; exact hA k
      _ = ‖x - y‖ * (q * (A * 2 ^ q)) := by ring
  calc ∑ k ∈ Finset.range (q + 1), ‖p.coeff k * x ^ k - p.coeff k * y ^ k‖
      ≤ ∑ _k ∈ Finset.range (q + 1), ‖x - y‖ * (q * (A * 2 ^ q)) := Finset.sum_le_sum hterm
    _ = ‖x - y‖ * ((q + 1) * (q * (A * 2 ^ q))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

theorem pow_card_le_norm_prod (s : Multiset ℂ) (ζ : ℂ) {m : ℝ} (hm : 0 ≤ m)
    (h : ∀ b ∈ s, m ≤ ‖ζ - b‖) : m ^ Multiset.card s ≤ ‖(s.map fun b => ζ - b).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, pow_succ, mul_comm]
    exact mul_le_mul (h a (Multiset.mem_cons_self a s))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb)) (by positivity) (_root_.norm_nonneg _)

/-- **Nearest root.** -/
theorem exists_root_near {G : GaussianInt[X]} (hG0 : G ≠ 0) (hdeg : 0 < G.natDegree) (ζ : ℂ) :
    ∃ β : ℂ, (G.map toComplex).eval β = 0 ∧
      ‖ζ - β‖ ^ G.natDegree ≤ ‖(G.map toComplex).eval ζ‖ := by
  classical
  set Gc := G.map toComplex
  have hGc0 : Gc ≠ 0 := (Polynomial.map_ne_zero_iff toComplex_injective).mpr hG0
  have hsplit : Gc.Splits := IsAlgClosed.splits Gc
  have hcard : Gc.roots.card = Gc.natDegree := hsplit.natDegree_eq_card_roots.symm
  have hdegc : Gc.natDegree = G.natDegree := natDegree_map_eq_of_injective toComplex_injective _
  have hne : Gc.roots ≠ 0 := by
    intro h; rw [h, Multiset.card_zero] at hcard; omega
  obtain ⟨β, hβ, hmin⟩ := Multiset.exists_min_image (fun β => ‖ζ - β‖) hne
  refine ⟨β, (mem_roots hGc0).mp hβ, ?_⟩
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have heval : Gc.eval ζ = Gc.leadingCoeff * (Gc.roots.map fun b => ζ - b).prod := by
    conv_lhs => rw [← hfac]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    simp
  have hlc : 1 ≤ ‖Gc.leadingCoeff‖ := by
    rw [leadingCoeff_map_of_injective toComplex_injective]
    exact one_le_norm_toComplex (leadingCoeff_ne_zero.mpr hG0)
  have hprod : ‖ζ - β‖ ^ G.natDegree ≤ ‖(Gc.roots.map fun b => ζ - b).prod‖ := by
    rw [← hdegc, ← hcard]
    exact pow_card_le_norm_prod _ ζ (_root_.norm_nonneg _) hmin
  rw [heval, norm_mul]
  exact hprod.trans (le_mul_of_one_le_left (_root_.norm_nonneg _) hlc)

end NLQCLean.Gelfond
