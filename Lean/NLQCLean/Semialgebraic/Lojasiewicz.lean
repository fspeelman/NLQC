import NLQCLean.Semialgebraic.OneVariableContinuity

/-!
# The semialgebraic Łojasiewicz inequality

**Growth of one-variable functions.** A positive function whose graph over `(0, ∞)` is
semialgebraic is at least `c rᵐ` near `0⁺`. Its value at `r` is a root of a nonzero
polynomial `P(r, y)` from a finite family (`exists_adapted_family`); writing
`P = Σ aⱼ(r) yʲ` with lowest nonzero coefficient `a_{j₀}`, the relation `P(r, y) = 0` gives
`|a_{j₀}(r)| ≤ y Σ |aⱼ(r)|` for `y ≤ 1`, and `|a_{j₀}(r)| ≥ α r^m` near `0`.

**Łojasiewicz.** On a compact semialgebraic `K`, let `f, g` be continuous with semialgebraic
graphs, `f ≥ 0` and `f = 0 ⇒ g = 0`. Then `|g|^N ≤ C f` on `K` for some `C > 0`, `N ≥ 1`
(Bochnak–Coste–Roy, Corollary 2.6.7). Apply the growth bound to
`ψ(s) = min {f x : x ∈ K, |g x| ≥ s}`, whose graph is semialgebraic by Tarski–Seidenberg.
-/

noncomputable section

namespace NLQCLean

open Set Filter Topology Polynomial Sundog.TarskiQE

/-! ### Univariate lower bounds -/

/-- A nonzero real polynomial is at least `α rᵐ` in absolute value just right of `0`. -/
theorem Polynomial.exists_pow_le_abs_eval {p : ℝ[X]} (hp : p ≠ 0) :
    ∃ α > 0, ∃ m : ℕ, ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ → α * r ^ m ≤ |p.eval r| := by
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
  have hq0 : q.eval 0 ≠ 0 := fun h => hq (Polynomial.dvd_iff_isRoot.mpr h)
  have hq0' : 0 < |q.eval 0| := abs_pos.mpr hq0
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp q.continuous.continuousAt
    (|q.eval 0| / 2) (by positivity)
  refine ⟨|q.eval 0| / 2, by positivity, rootMultiplicity 0 p, δ, hδ, fun r hr hrδ => ?_⟩
  have hd : |q.eval r - q.eval 0| < |q.eval 0| / 2 := by
    have := hball (x := r) (by rw [Real.dist_eq, sub_zero, abs_of_pos hr]; exact hrδ)
    rwa [Real.dist_eq] at this
  have hqr : |q.eval 0| / 2 ≤ |q.eval r| := by
    have := abs_sub_abs_le_abs_sub (q.eval 0) (q.eval r)
    rw [abs_sub_comm] at hd
    linarith
  have hev : p.eval r = r ^ rootMultiplicity 0 p * q.eval r := by
    conv_lhs => rw [hpq]
    rw [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_zero]
  rw [hev, abs_mul, abs_pow, abs_of_pos hr, mul_comm]
  exact mul_le_mul_of_nonneg_left hqr (pow_pos hr _).le

/-- One-parameter polynomials as univariate polynomials. -/
def finOneToPoly (a : MvPolynomial (Fin 1) ℝ) : ℝ[X] :=
  MvPolynomial.aeval (fun _ => Polynomial.X) a

theorem eval_finOneToPoly (a : MvPolynomial (Fin 1) ℝ) (r : ℝ) :
    (finOneToPoly a).eval r = MvPolynomial.eval (fun _ => r) a := by
  unfold finOneToPoly
  induction a using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, eval_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X, eval_mul, eval_X, hp,
      MvPolynomial.eval_X]

theorem finOneToPoly_ne_zero {a : MvPolynomial (Fin 1) ℝ} (ha : a ≠ 0) : finOneToPoly a ≠ 0 := by
  intro h
  apply ha
  refine MvPolynomial.funext fun x => ?_
  have hx : x = fun _ => x 0 := funext fun j => by rw [Subsingleton.elim j 0]
  rw [hx, ← eval_finOneToPoly, h, eval_zero, map_zero]

/-! ### Roots of one-parameter families -/

/-- A positive root `y` of the specialization of a nonzero `P` at a small parameter `r` is at
least `c rᵐ`. -/
theorem exists_pow_le_of_spec_root {P : ParamPoly 1} (hP : P ≠ 0) :
    ∃ c > 0, ∃ m : ℕ, ∃ δ > 0, δ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r < δ → ∀ y : ℝ, 0 < y →
      (spec (fun _ => r) P).eval y = 0 → c * r ^ m ≤ y := by
  classical
  set j₀ := P.natTrailingDegree
  set n := P.natDegree + 1
  have hlead : P.coeff j₀ ≠ 0 := by
    rw [← Polynomial.trailingCoeff]
    exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hP
  obtain ⟨α, hα, m, δ₁, hδ₁, hlow⟩ :=
    Polynomial.exists_pow_le_abs_eval (finOneToPoly_ne_zero hlead)
  -- a bound for the coefficient sum on `[0, 1]`
  have hcont : ContinuousOn (fun r : ℝ => ∑ j ∈ Finset.range n,
      |(finOneToPoly (P.coeff j)).eval r|) (Icc 0 1) :=
    (continuous_finsetSum _ fun j _ => (Polynomial.continuous _).abs).continuousOn
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set B := |B₀| + 1 with hB
  have hBpos : 0 < B := by positivity
  have hsumB : ∀ r ∈ Icc (0 : ℝ) 1, ∑ j ∈ Finset.range n,
      |MvPolynomial.eval (fun _ => r) (P.coeff j)| ≤ B := by
    intro r hr
    have h := hB₀ r hr
    simp only [eval_finOneToPoly] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)] at h
    linarith [le_abs_self B₀]
  refine ⟨min 1 (α / B), lt_min one_pos (div_pos hα hBpos), m, min δ₁ 1, lt_min hδ₁ one_pos,
    min_le_right _ _, fun r hr hrδ y hy hroot => ?_⟩
  have hr1 : r < 1 := hrδ.trans_le (min_le_right _ _)
  have hrm : r ^ m ≤ 1 := pow_le_one₀ hr.le hr1.le
  by_cases hy1 : 1 ≤ y
  · calc min 1 (α / B) * r ^ m ≤ 1 * 1 :=
          mul_le_mul (min_le_left _ _) hrm (pow_pos hr _).le zero_le_one
      _ ≤ y := by linarith
  push Not at hy1
  set a : ℕ → ℝ := fun j => MvPolynomial.eval (fun _ => r) (P.coeff j) with ha
  have hcoeff : ∀ j, (spec (fun _ => r) P).coeff j = a j := fun j => by
    simp [spec, ha, Polynomial.coeff_map]
  have hdeg : (spec (fun _ => r) P).natDegree < n := by
    unfold spec
    exact Nat.lt_succ_of_le (Polynomial.natDegree_map_le)
  have hsum : ∑ j ∈ Finset.range n, a j * y ^ j = 0 := by
    rw [← hroot, eval_eq_sum_range' hdeg]
    simp only [hcoeff]
  have hj₀ : j₀ ∈ Finset.range n :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.natTrailingDegree_le_natDegree P))
  have hsplit := Finset.add_sum_erase _ (fun j => a j * y ^ j) hj₀
  rw [hsum] at hsplit
  have hterm : ∀ j ∈ (Finset.range n).erase j₀, |a j * y ^ j| ≤ |a j| * y ^ (j₀ + 1) := by
    intro j hj
    have hjne := Finset.ne_of_mem_erase hj
    rcases lt_or_gt_of_ne hjne with hlt | hgt
    · have h0 : a j = 0 := by
        simp only [ha]
        rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt, map_zero]
      simp [h0]
    · rw [abs_mul, abs_of_pos (pow_pos hy _)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hy.le hy1.le hgt) (abs_nonneg _)
  have hmain : |a j₀| * y ^ j₀ ≤ y ^ (j₀ + 1) * B := by
    have heq : a j₀ * y ^ j₀ = -∑ j ∈ (Finset.range n).erase j₀, a j * y ^ j := by linarith
    have h1 : |a j₀| * y ^ j₀ ≤ ∑ j ∈ (Finset.range n).erase j₀, |a j| * y ^ (j₀ + 1) := by
      calc |a j₀| * y ^ j₀ = |a j₀ * y ^ j₀| := by rw [abs_mul, abs_of_pos (pow_pos hy _)]
        _ = |∑ j ∈ (Finset.range n).erase j₀, a j * y ^ j| := by rw [heq, abs_neg]
        _ ≤ ∑ j ∈ (Finset.range n).erase j₀, |a j * y ^ j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := Finset.sum_le_sum hterm
    refine h1.trans ?_
    rw [← Finset.sum_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      fun j _ _ => abs_nonneg _).trans ?_
    exact hsumB r ⟨hr.le, hr1.le⟩
  have hayB : |a j₀| ≤ y * B := by
    have hpos : 0 < y ^ j₀ := pow_pos hy _
    have : |a j₀| * y ^ j₀ ≤ (y * B) * y ^ j₀ := by
      calc |a j₀| * y ^ j₀ ≤ y ^ (j₀ + 1) * B := hmain
        _ = (y * B) * y ^ j₀ := by ring
    exact le_of_mul_le_mul_right this hpos
  have hlow' : α * r ^ m ≤ |a j₀| := by
    have := hlow r hr (hrδ.trans_le (min_le_left _ _))
    rwa [eval_finOneToPoly] at this
  calc min 1 (α / B) * r ^ m ≤ α / B * r ^ m :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_pos hr _).le
    _ = (α * r ^ m) / B := by ring
    _ ≤ (y * B) / B := div_le_div_of_nonneg_right (hlow'.trans hayB) hBpos.le
    _ = y := by field_simp

/-- The bound is uniform over a finite set of nonzero one-parameter polynomials. -/
theorem exists_pow_le_of_spec_root_finset (S : Finset (ParamPoly 1)) (hS : ∀ P ∈ S, P ≠ 0) :
    ∃ c > 0, ∃ m : ℕ, ∃ δ > 0, δ ≤ 1 ∧ ∀ P ∈ S, ∀ r : ℝ, 0 < r → r < δ → ∀ y : ℝ, 0 < y →
      (spec (fun _ => r) P).eval y = 0 → c * r ^ m ≤ y := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, 0, 1, one_pos, le_rfl, by simp⟩
  | insert P S hPS ih =>
    obtain ⟨c₁, hc₁, m₁, δ₁, hδ₁, hδ₁1, h₁⟩ := ih fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ)
    obtain ⟨c₂, hc₂, m₂, δ₂, hδ₂, hδ₂1, h₂⟩ :=
      exists_pow_le_of_spec_root (hS P (Finset.mem_insert_self P S))
    refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max m₁ m₂, min δ₁ δ₂, lt_min hδ₁ hδ₂,
      (min_le_left _ _).trans hδ₁1, fun Q hQ r hr hrδ y hy hroot => ?_⟩
    have hr1 : r ≤ 1 := (hrδ.trans_le ((min_le_left _ _).trans hδ₁1)).le
    rcases Finset.mem_insert.mp hQ with rfl | hQS
    · calc min c₁ c₂ * r ^ max m₁ m₂ ≤ c₂ * r ^ m₂ :=
            mul_le_mul (min_le_right _ _) (pow_le_pow_of_le_one hr.le hr1 (le_max_right _ _))
              (pow_pos hr _).le hc₂.le
        _ ≤ y := h₂ r hr (hrδ.trans_le (min_le_right _ _)) y hy hroot
    · calc min c₁ c₂ * r ^ max m₁ m₂ ≤ c₁ * r ^ m₁ :=
            mul_le_mul (min_le_left _ _) (pow_le_pow_of_le_one hr.le hr1 (le_max_left _ _))
              (pow_pos hr _).le hc₁.le
        _ ≤ y := h₁ Q hQS r hr (hrδ.trans_le (min_le_left _ _)) y hy hroot

/-- **Growth of one-variable semialgebraic functions.** A positive function with semialgebraic
graph over `(0, ∞)` is at least `c rᵐ` near `0⁺`. -/
theorem exists_pow_le_of_saOn_graph {f : ℝ → ℝ}
    (hf : SAOn {h : Fin 2 → ℝ | 0 < h 0 ∧ h 1 = f (h 0)}) (hpos : ∀ r, 0 < r → 0 < f r) :
    ∃ c > 0, ∃ m : ℕ, ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ → c * r ^ m ≤ f r := by
  classical
  obtain ⟨F, -, hslot⟩ := exists_adapted_family hf
  let G : Set (Fin 2 → ℝ) := {h | 0 < h 0 ∧ h 1 = f (h 0)}
  let c : ℝ → Fin 1 → ℝ := fun r _ => r
  have hsnoc : ∀ r y, (Fin.snoc (c r) y : Fin 2 → ℝ) ∈ G ↔ 0 < r ∧ y = f r := by
    intro r y
    simp [G, c, Fin.snoc]
  have hroot : ∀ r, 0 < r → f r ∈ rootSet F (c r) := by
    intro r hr
    by_contra hnot
    obtain ⟨y', hne, hy'⟩ := exists_ne_slotIndex_eq hnot
    have := (hslot (c r) y' (f r) hy').mpr ((hsnoc r (f r)).mpr ⟨hr, rfl⟩)
    exact hne ((hsnoc r y').mp this).2
  obtain ⟨c₀, hc₀, m, δ, hδ, -, hbound⟩ :=
    exists_pow_le_of_spec_root_finset (F.toFinset.filter fun P => P ≠ 0) fun P hP =>
      (Finset.mem_filter.mp hP).2
  refine ⟨c₀, hc₀, m, δ, hδ, fun r hr hrδ => ?_⟩
  obtain ⟨P, hPF, hP0, hPr⟩ := hroot r hr
  have hPne : P ≠ 0 := by
    rintro rfl
    exact hP0 (by simp [spec])
  exact hbound P (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hPF, hPne⟩) r hr hrδ (f r)
    (hpos r hr) hPr

/-! ### The Łojasiewicz inequality -/

section Lojasiewicz

variable {ι : Type} [Fintype ι]

/-- Coordinates of the auxiliary space: parameters `(s, y)`, a point `x` and two values. -/
private abbrev LIdx (ι : Type) := Fin 2 ⊕ (ι ⊕ Fin 2)

private def graphEmbed (k : Fin 2) : Option ι → LIdx ι :=
  fun o => o.elim (Sum.inr (Sum.inr k)) fun i => Sum.inr (Sum.inl i)

private def ptOf (w : LIdx ι → ℝ) : ι → ℝ := fun i => w (Sum.inr (Sum.inl i))

/-- Points with `s² ≤ g(x)²` and `f(x)` compared with `y`, before projection. -/
private theorem saOn_lojasiewicz_aux {K : Set (ι → ℝ)} {f g : (ι → ℝ) → ℝ}
    (hfsa : SAOn {z : Option ι → ℝ | (fun i => z (some i)) ∈ K ∧
      z none = f (fun i => z (some i))})
    (hgsa : SAOn {z : Option ι → ℝ | (fun i => z (some i)) ∈ K ∧
      z none = g (fun i => z (some i))})
    (strict : Bool) :
    SAOn {h : Fin 2 → ℝ | ∃ x ∈ K, h 0 ^ 2 ≤ g x ^ 2 ∧
      (if strict then f x < h 1 else f x = h 1)} := by
  classical
  let u : LIdx ι := Sum.inr (Sum.inr 0)
  let v : LIdx ι := Sum.inr (Sum.inr 1)
  let sC : LIdx ι := Sum.inl 0
  let yC : LIdx ι := Sum.inl 1
  have hF := hfsa.comap (graphEmbed (ι := ι) 0)
  have hG := hgsa.comap (graphEmbed (ι := ι) 1)
  have hsq := SAOn.le (MvPolynomial.X sC ^ 2 : MvPolynomial (LIdx ι) ℝ) (MvPolynomial.X v ^ 2)
  have hcmp : SAOn {w : LIdx ι → ℝ |
      if strict then w u < w yC else w u = w yC} := by
    cases strict
    · exact (SAOn.eq (MvPolynomial.X u) (MvPolynomial.X yC)).congr fun w => by simp
    · exact (SAOn.lt (MvPolynomial.X u) (MvPolynomial.X yC)).congr fun w => by simp
  have hA := SAOn.exists_sum (ι := Fin 2) (κ := ι ⊕ Fin 2) (((hF.inter hG).inter hsq).inter hcmp)
  refine hA.congr fun h => ?_
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.comp_def, graphEmbed,
    Option.elim, MvPolynomial.eval_pow, MvPolynomial.eval_X]
  constructor
  · rintro ⟨z, ⟨⟨⟨hxK, hu⟩, -, hv⟩, hle⟩, hc⟩
    refine ⟨fun i => z (Sum.inl i), hxK, ?_, ?_⟩
    · simpa [sC, v, hv] using hle
    · simpa [u, yC, hu] using hc
  · rintro ⟨x, hxK, hle, hc⟩
    refine ⟨Sum.elim x ![f x, g x], ⟨⟨⟨hxK, ?_⟩, hxK, ?_⟩, ?_⟩, ?_⟩
    · simp
    · simp
    · simpa [sC, v] using hle
    · simpa [u, yC] using hc

/-- **The semialgebraic Łojasiewicz inequality.** On a compact set, let `f, g` be continuous
with semialgebraic graphs, `f ≥ 0`, and `g = 0` wherever `f = 0`. Then `|g|^N ≤ C f`. -/
theorem lojasiewicz_inequality {K : Set (ι → ℝ)} (hK : IsCompact K)
    {f g : (ι → ℝ) → ℝ} (hf : ContinuousOn f K) (hg : ContinuousOn g K)
    (hfsa : SAOn {z : Option ι → ℝ | (fun i => z (some i)) ∈ K ∧
      z none = f (fun i => z (some i))})
    (hgsa : SAOn {z : Option ι → ℝ | (fun i => z (some i)) ∈ K ∧
      z none = g (fun i => z (some i))})
    (hf0 : ∀ x ∈ K, 0 ≤ f x) (hzero : ∀ x ∈ K, f x = 0 → g x = 0) :
    ∃ C > 0, ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, |g x| ^ N ≤ C * f x := by
  classical
  by_cases hall : ∀ x ∈ K, g x = 0
  · refine ⟨1, one_pos, 1, one_pos, fun x hx => ?_⟩
    rw [hall x hx, abs_zero, pow_one, one_mul]
    exact hf0 x hx
  push Not at hall
  obtain ⟨x₁, hx₁K, hgx₁⟩ := hall
  obtain ⟨x₀, hx₀K, hmax⟩ := hK.exists_isMaxOn ⟨x₁, hx₁K⟩ hg.abs
  set M := |g x₀| with hMdef
  have hM : 0 < M := lt_of_lt_of_le (abs_pos.mpr hgx₁) (hmax hx₁K)
  have hle_M : ∀ x ∈ K, |g x| ≤ M := fun x hx => hmax hx
  let S : ℝ → Set (ι → ℝ) := fun s => K ∩ (fun x => |g x|) ⁻¹' Ici s
  have hSc : ∀ s, IsCompact (S s) := fun s =>
    hK.of_isClosed_subset (hg.abs.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
      inter_subset_left
  have hx₀S : ∀ s ≤ M, x₀ ∈ S s := fun s hs => ⟨hx₀K, hs⟩
  have hmin : ∀ s ≤ M, ∃ x ∈ S s, IsMinOn f (S s) x := fun s hs =>
    (hSc s).exists_isMinOn ⟨x₀, hx₀S s hs⟩ (hf.mono inter_subset_left)
  let ψ : ℝ → ℝ := fun s => if 0 < s ∧ s < M then sInf (f '' S s) else 1
  have hfpos : ∀ s, 0 < s → ∀ x ∈ S s, 0 < f x := by
    intro s hs x hx
    refine lt_of_le_of_ne (hf0 x hx.1) fun h0 => ?_
    have hg0 := hzero x hx.1 h0.symm
    have : s ≤ |g x| := hx.2
    rw [hg0, abs_zero] at this
    linarith
  have hψchar : ∀ s y, 0 < s → s < M →
      (y = ψ s ↔ (∃ x ∈ S s, f x = y) ∧ ∀ x ∈ S s, y ≤ f x) := by
    intro s y hs hsM
    obtain ⟨xs, hxs, hxmin⟩ := hmin s hsM.le
    have hleast : IsLeast (f '' S s) (f xs) :=
      ⟨⟨xs, hxs, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hxmin hx⟩
    have hψ : ψ s = f xs := by
      simp only [ψ, ite_eq_left (And.intro hs hsM)]
      exact hleast.csInf_eq
    rw [hψ]
    constructor
    · rintro rfl
      exact ⟨⟨xs, hxs, rfl⟩, fun x hx => hxmin hx⟩
    · rintro ⟨⟨x, hx, rfl⟩, hlow⟩
      exact le_antisymm (hlow xs hxs) (hxmin hx)
  have hψpos : ∀ s, 0 < s → 0 < ψ s := by
    intro s hs
    by_cases hsM : s < M
    · obtain ⟨xs, hxs, hxmin⟩ := hmin s hsM.le
      have := (hψchar s (f xs) hs hsM).mpr ⟨⟨xs, hxs, rfl⟩, fun x hx => hxmin hx⟩
      rw [← this]
      exact hfpos s hs xs hxs
    · simp only [ψ, ite_eq_right (fun h : 0 < s ∧ s < M => hsM h.2)]
      exact one_pos
  -- the graph of `ψ` is semialgebraic
  have hE1 := saOn_lojasiewicz_aux hfsa hgsa false
  have hE2 := saOn_lojasiewicz_aux hfsa hgsa true
  have hgraph : SAOn {h : Fin 2 → ℝ | 0 < h 0 ∧ h 1 = ψ (h 0)} := by
    have hA := ((((SAOn.pos (MvPolynomial.X (0 : Fin 2))).inter
      (SAOn.lt (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.C M))).inter hE1).inter hE2.compl).union
      ((SAOn.le (MvPolynomial.C M) (MvPolynomial.X (0 : Fin 2))).inter
        (SAOn.eq (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.C 1)))
    refine hA.congr fun h => ?_
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq,
      MvPolynomial.eval_X, MvPolynomial.eval_C, Bool.false_eq_true, ite_false, ite_true]
    have hsq : ∀ x, 0 < h 0 → (h 0 ^ 2 ≤ g x ^ 2 ↔ x ∈ (fun x => |g x|) ⁻¹' Ici (h 0)) := by
      intro x hh
      simp only [Set.mem_preimage, Set.mem_Ici]
      rw [sq_le_sq, abs_of_pos hh]
    constructor
    · rintro (⟨⟨⟨hh0, hhM⟩, ⟨x, hxK, hxs, hxf⟩⟩, hno⟩ | ⟨hMh, hh1⟩)
      · refine ⟨hh0, (hψchar (h 0) (h 1) hh0 hhM).mpr ⟨⟨x, ⟨hxK, (hsq x hh0).mp hxs⟩, hxf⟩, ?_⟩⟩
        intro x' hx'
        by_contra hlt
        push Not at hlt
        exact hno ⟨x', hx'.1, (hsq x' hh0).mpr hx'.2, hlt⟩
      · refine ⟨hM.trans_le hMh, ?_⟩
        simp only [ψ, ite_eq_right (fun hh : 0 < h 0 ∧ h 0 < M => (not_lt.mpr hMh) hh.2), hh1]
    · rintro ⟨hh0, hhψ⟩
      by_cases hhM : h 0 < M
      · left
        obtain ⟨⟨x, hx, hxf⟩, hlow⟩ := (hψchar (h 0) (h 1) hh0 hhM).mp hhψ
        refine ⟨⟨⟨hh0, hhM⟩, ⟨x, hx.1, (hsq x hh0).mpr hx.2, hxf⟩⟩, ?_⟩
        rintro ⟨x', hx'K, hx's, hlt⟩
        exact (not_lt.mpr (hlow x' ⟨hx'K, (hsq x' hh0).mp hx's⟩)) hlt
      · right
        refine ⟨not_lt.mp hhM, ?_⟩
        rw [hhψ]
        simp only [ψ, ite_eq_right (fun hh : 0 < h 0 ∧ h 0 < M => hhM hh.2)]
  obtain ⟨c, hc, m, δ, hδ, hgrowth⟩ := exists_pow_le_of_saOn_graph hgraph hψpos
  set δ₁ := min (min δ M) 1 with hδ₁
  have hδ₁pos : 0 < δ₁ := lt_min (lt_min hδ hM) one_pos
  have hδ₁δ : δ₁ ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₁M : δ₁ ≤ M := (min_le_left _ _).trans (min_le_right _ _)
  have hδ₁1 : δ₁ ≤ 1 := min_le_right _ _
  -- the lower bound of `f` on `S s`
  have hfS : ∀ s, 0 < s → s < δ₁ → ∀ x ∈ S s, c * s ^ m ≤ f x := by
    intro s hs hsδ x hx
    have hsM : s < M := hsδ.trans_le hδ₁M
    have hψ := (hψchar s (ψ s) hs hsM).mp rfl
    exact (hgrowth s hs (hsδ.trans_le hδ₁δ)).trans (hψ.2 x hx)
  set η := c * (δ₁ / 2) ^ m with hη
  have hηpos : 0 < η := by positivity
  refine ⟨max (1 / c) (M ^ (m + 1) / η), lt_max_of_lt_left (by positivity), m + 1,
    Nat.succ_pos m, fun x hx => ?_⟩
  have hgx := abs_nonneg (g x)
  rcases eq_or_lt_of_le hgx with hzero' | hpos
  · rw [← hzero', zero_pow (Nat.succ_ne_zero m)]
    exact mul_nonneg (le_max_of_le_left (by positivity)) (hf0 x hx)
  by_cases hsmall : |g x| < δ₁
  · have hlow := hfS (|g x|) hpos hsmall x ⟨hx, show |g x| ∈ Ici (|g x|) from Set.mem_Ici.mpr le_rfl⟩
    have hg1 : |g x| ≤ 1 := hsmall.le.trans hδ₁1
    calc |g x| ^ (m + 1) ≤ |g x| ^ m := pow_le_pow_of_le_one hgx hg1 (Nat.le_succ m)
      _ = (1 / c) * (c * |g x| ^ m) := by field_simp
      _ ≤ (1 / c) * f x := mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ max (1 / c) (M ^ (m + 1) / η) * f x :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (hf0 x hx)
  · push Not at hsmall
    have hlow : η ≤ f x :=
      hfS (δ₁ / 2) (by positivity) (by linarith) x ⟨hx, by
        change δ₁ / 2 ≤ |g x|
        linarith⟩
    calc |g x| ^ (m + 1) ≤ M ^ (m + 1) := pow_le_pow_left₀ hgx (hle_M x hx) _
      _ = (M ^ (m + 1) / η) * η := by field_simp
      _ ≤ (M ^ (m + 1) / η) * f x := mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ max (1 / c) (M ^ (m + 1) / η) * f x :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (hf0 x hx)

end Lojasiewicz

end NLQCLean
