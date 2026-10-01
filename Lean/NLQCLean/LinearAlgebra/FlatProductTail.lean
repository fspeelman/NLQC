import NLQCLean.LinearAlgebra.FlatSupport
import NLQCLean.LinearAlgebra.SchmidtOverlap

/-!
# Flat spectra and the product top-mass tail

* `sum_sq_sqrt_schmidtWeights_sub_le`: if `W Wᴴ = c² I`, then
  `∑ (√p_i − c)² ≤ ‖M − W‖²` for the Schmidt weights `p` of `M`. Row singular vectors and
  the reverse triangle inequality replace a Mirsky/Hoffman–Wielandt theorem.
* `exists_flat_support`: at most `D/4` weights fall below `1/(4D)`, so `⌈D/2⌉` flat indices exist.
* `topWeightMass_product_le_of_flat`: with `q` flat indices of weight `≥ c`,
  `Λ_K(p ⊗ z) ≤ 1 − cq + cq Λ_s(z)` whenever `K ≤ q s`. Finite supports only.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

section Spectrum

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem norm_sq_toLp_row (A : Matrix m n ℂ) (i : m) :
    ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ n)‖ ^ 2 = ((A * Aᴴ) i i).re := by
  rw [EuclideanSpace.norm_sq_eq, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ‖A i j‖ ^ 2 = (A i j * Aᴴ j i).re
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

omit [DecidableEq n] in
/-- flat-spectrum estimate, via Schmidt row coordinates. -/
theorem sum_sq_sqrt_schmidtWeights_sub_le (M W : Matrix m n ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hW : W * Wᴴ = ((c ^ 2 : ℝ) : ℂ) • (1 : Matrix m m ℂ)) :
    ∑ i, (Real.sqrt (schmidtWeights M i) - c) ^ 2 ≤ ‖M - W‖ ^ 2 := by
  obtain ⟨V, hV, hV', hgram⟩ := exists_schmidt_coordinates M
  have hZZ : (Vᴴ * W) * (Vᴴ * W)ᴴ = ((c ^ 2 : ℝ) : ℂ) • (1 : Matrix m m ℂ) := by
    calc (Vᴴ * W) * (Vᴴ * W)ᴴ = Vᴴ * (W * Wᴴ) * V := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = ((c ^ 2 : ℝ) : ℂ) • (Vᴴ * V) := by
          rw [hW, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = _ := by rw [hV.conjTranspose_mul_self]
  have hX (i : m) : ‖(WithLp.toLp 2 ((Vᴴ * M) i) : EuclideanSpace ℂ n)‖ ^ 2 =
      schmidtWeights M i := by
    rw [norm_sq_toLp_row, hgram]
    simp
  have hZ (i : m) : ‖(WithLp.toLp 2 ((Vᴴ * W) i) : EuclideanSpace ℂ n)‖ = c := by
    apply (sq_eq_sq₀ (norm_nonneg _) hc).mp
    rw [norm_sq_toLp_row, hZZ, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Complex.ofReal_re]
  have hY : ∑ i, ‖(WithLp.toLp 2 ((Vᴴ * (M - W)) i) : EuclideanSpace ℂ n)‖ ^ 2 =
      ‖M - W‖ ^ 2 := by
    rw [← hV'.frobNorm_mul_eq (M - W), frobNorm_sq]
    exact Finset.sum_congr rfl fun i _ =>
      (EuclideanSpace.norm_sq_eq _).trans (Finset.sum_congr rfl fun j _ => rfl)
  rw [← hY]
  refine Finset.sum_le_sum fun i _ => ?_
  have hx' : Real.sqrt (schmidtWeights M i) =
      ‖(WithLp.toLp 2 ((Vᴴ * M) i) : EuclideanSpace ℂ n)‖ := by
    rw [← hX i, Real.sqrt_sq (norm_nonneg _)]
  have heq : (WithLp.toLp 2 ((Vᴴ * M) i) : EuclideanSpace ℂ n) -
      WithLp.toLp 2 ((Vᴴ * W) i) = WithLp.toLp 2 ((Vᴴ * (M - W)) i) := by
    ext j
    simp [Matrix.mul_sub]
  have h := abs_norm_sub_norm_le (WithLp.toLp 2 ((Vᴴ * M) i) : EuclideanSpace ℂ n)
    (WithLp.toLp 2 ((Vᴴ * W) i))
  rw [heq, hZ i] at h
  rw [hx', ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

end Spectrum

/-- counting: at most `D/4` weights lie below `1/(4D)`, so `⌈D/2⌉` flat weights exist. -/
theorem exists_flat_support {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (hd : 2 ≤ d)
    (hcard : Fintype.card ι = d ^ 2) (w : ι → ℝ)
    (h : ∑ i, (Real.sqrt (w i) - 1 / d) ^ 2 ≤ 1 / 16) :
    ∃ S : Finset ι, S.card = flatSupportCount d ∧ ∀ i ∈ S, 1 / (4 * (d : ℝ) ^ 2) ≤ w i := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set Bad := Finset.univ.filter (fun i => w i < 1 / (4 * (d : ℝ) ^ 2)) with hBad
  have hterm : ∀ i ∈ Bad, 1 / (4 * (d : ℝ) ^ 2) ≤ (Real.sqrt (w i) - 1 / d) ^ 2 := by
    intro i hi
    have hlt := (Finset.mem_filter.mp hi).2
    have hsq : (1 / (2 * (d : ℝ))) ^ 2 = 1 / (4 * (d : ℝ) ^ 2) := by
      field_simp
      ring
    have hs : Real.sqrt (w i) < 1 / (2 * d) :=
      (Real.sqrt_lt' (by positivity)).mpr (hsq ▸ hlt)
    have hs0 := Real.sqrt_nonneg (w i)
    have hhalf : 1 / (d : ℝ) = 2 * (1 / (2 * d)) := by
      field_simp
    have h1 : 1 / (2 * (d : ℝ)) ≤ 1 / d - Real.sqrt (w i) := by linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    rw [hsq] at h2
    nlinarith
  have hbad : (Bad.card : ℝ) * (1 / (4 * (d : ℝ) ^ 2)) ≤ 1 / 16 := by
    calc (Bad.card : ℝ) * (1 / (4 * (d : ℝ) ^ 2)) = ∑ _i ∈ Bad, 1 / (4 * (d : ℝ) ^ 2) := by
          simp [Finset.sum_const]
      _ ≤ ∑ i ∈ Bad, (Real.sqrt (w i) - 1 / d) ^ 2 := Finset.sum_le_sum hterm
      _ ≤ ∑ i, (Real.sqrt (w i) - 1 / d) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
      _ ≤ 1 / 16 := h
  have hbadR : 4 * (Bad.card : ℝ) ≤ (d : ℝ) ^ 2 := by
    have hpos : (0 : ℝ) < 4 * (d : ℝ) ^ 2 := by positivity
    rw [mul_one_div, div_le_iff₀ hpos] at hbad
    nlinarith
  have hbadN : 4 * Bad.card ≤ d ^ 2 := by exact_mod_cast hbadR
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (fun i => w i < 1 / (4 * (d : ℝ) ^ 2))
  rw [Finset.card_univ, hcard, ← hBad] at hsplit
  have hD : 4 ≤ d ^ 2 := by nlinarith
  have hq : flatSupportCount d ≤
      (Finset.univ.filter (fun i => ¬ w i < 1 / (4 * (d : ℝ) ^ 2))).card := by
    unfold flatSupportCount
    generalize d ^ 2 = D at hbadN hsplit hD
    omega
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hq
  exact ⟨S, hScard, fun i hi => not_lt.mp (Finset.mem_filter.mp (hSsub hi)).2⟩

section Tail

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- product tail: flat indices force most top-K product mass into the second factor. -/
theorem topWeightMass_product_le_of_flat {K q s : ℕ} (hq : 0 < q) (hKs : K ≤ q * s)
    {c : ℝ} (hc : 0 < c) (p : ι → ℝ) (z : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hz : ∀ j, 0 ≤ z j)
    (hp1 : ∑ i, p i = 1) (hz1 : ∑ j, z j = 1) (S : Finset ι) (hS : S.card = q)
    (hpS : ∀ i ∈ S, c ≤ p i) :
    topWeightMass K (fun x : ι × κ => p x.1 * z x.2) ≤
      1 - c * q + c * q * topWeightMass s z := by
  apply topWeightMass_le
  intro T hT
  let ind : ι → ℝ := fun i => if i ∈ S then c else 0
  have hsplit : ∑ x ∈ T, p x.1 * z x.2 =
      ∑ x ∈ T, (p x.1 - ind x.1) * z x.2 + ∑ x ∈ T, ind x.1 * z x.2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hnn : ∀ i, 0 ≤ p i - ind i := by
    intro i
    by_cases hi : i ∈ S
    · simp [ind, hi, hpS i hi]
    · simp [ind, hi, hp i]
  have hind_sum : ∑ i, ind i = c * q := by
    simp only [ind]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, hS,
      nsmul_eq_mul]
    ring
  have h1 : ∑ x ∈ T, (p x.1 - ind x.1) * z x.2 ≤ 1 - c * q := by
    calc ∑ x ∈ T, (p x.1 - ind x.1) * z x.2 ≤ ∑ x : ι × κ, (p x.1 - ind x.1) * z x.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun x _ _ => mul_nonneg (hnn _) (hz _)
      _ = (∑ i, (p i - ind i)) * ∑ j, z j := by
          rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      _ = 1 - c * q := by
          rw [hz1, mul_one, Finset.sum_sub_distrib, hp1, hind_sum]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  let T' := T.filter (fun x => x.1 ∈ S)
  let mc : κ → ℝ := fun j => ((T'.filter (fun x => x.2 = j)).card : ℝ)
  have hrewrite : ∑ x ∈ T, ind x.1 * z x.2 = c * ∑ j, mc j * z j := by
    calc ∑ x ∈ T, ind x.1 * z x.2 = ∑ x ∈ T', c * z x.2 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : x.1 ∈ S <;> simp [ind, hx]
      _ = c * ∑ x ∈ T', z x.2 := by rw [Finset.mul_sum]
      _ = c * ∑ j, mc j * z j := by
          congr 1
          rw [← Finset.sum_fiberwise T' (fun x => x.2)]
          refine Finset.sum_congr rfl fun j _ => ?_
          calc ∑ x ∈ T'.filter (fun x => x.2 = j), z x.2 =
              ∑ _x ∈ T'.filter (fun x => x.2 = j), z j :=
                Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]
            _ = mc j * z j := by simp [mc]
  have hm_le : ∀ j, mc j ≤ q := by
    intro j
    have hcardle : (T'.filter (fun x => x.2 = j)).card ≤ S.card := by
      apply Finset.card_le_card_of_injOn (fun x => x.1)
      · intro x hx
        simp only [T', Finset.mem_coe, Finset.mem_filter] at hx
        exact hx.1.2
      · intro x hx y hy hxy
        simp only [T', Finset.mem_coe, Finset.mem_filter] at hx hy
        exact Prod.ext hxy (hx.2.trans hy.2.symm)
    simp only [mc]
    exact_mod_cast hS ▸ hcardle
  have hm_sum : ∑ j, mc j ≤ K := by
    have hcard : ∑ j, (T'.filter (fun x => x.2 = j)).card = T'.card :=
      (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ x.2)).symm
    have hT'le : T'.card ≤ K := (Finset.card_filter_le _ _).trans hT
    calc ∑ j, mc j = ((∑ j, (T'.filter (fun x => x.2 = j)).card : ℕ) : ℝ) := by
          simp [mc]
      _ ≤ K := by rw [hcard]; exact_mod_cast hT'le
  have htop := sum_mul_le_topWeightMass s z (fun j => mc j / q) hz
    (fun j => div_nonneg (Nat.cast_nonneg _) hq'.le)
    (fun j => (div_le_one hq').mpr (hm_le j))
    (by
      rw [← Finset.sum_div, div_le_iff₀ hq']
      have hKsR : (K : ℝ) ≤ s * q := by exact_mod_cast hKs.trans (le_of_eq (Nat.mul_comm q s))
      linarith)
  have hdiv : ∑ j, z j * (mc j / q) = (∑ j, mc j * z j) / q := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmz : ∑ j, mc j * z j ≤ topWeightMass s z * q := by
    rw [← div_le_iff₀ hq', ← hdiv]
    exact htop
  have h2 : ∑ x ∈ T, ind x.1 * z x.2 ≤ c * q * topWeightMass s z := by
    rw [hrewrite]
    calc c * ∑ j, mc j * z j ≤ c * (topWeightMass s z * q) := mul_le_mul_of_nonneg_left hmz hc.le
      _ = c * q * topWeightMass s z := by ring
  rw [hsplit]
  linarith

end Tail

end NLQCLean
