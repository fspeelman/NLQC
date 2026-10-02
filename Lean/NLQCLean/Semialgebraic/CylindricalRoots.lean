import NLQCLean.Semialgebraic.Definable
import NLQCLean.Semialgebraic.FiniteRealOrder
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Roots of a parametric family of polynomials

For a finite list `F` of polynomials in a last variable `y` with coefficients
polynomial in parameters `g ∈ ℝⁿ`, `rootSet F g` is the finite set of real
roots at `g` of the members not vanishing identically at `g`. The number of
roots below a height, the number of roots, and the *slot* of a height (which
root it is, or which gap between consecutive roots it lies in) are all
semialgebraic in `(g, y)`. Every member has constant sign along each slot.

If the family is closed under `∂_y` and the number of roots is constant on a
set `D` of parameters, the `i`-th root depends continuously on `g ∈ D`: near
each root sits a simple root of an iterated derivative, which persists under
perturbation, and counting forces these to be all the roots.
-/

noncomputable section

namespace NLQCLean

open Polynomial Sundog.TarskiQE Filter Topology

variable {n : ℕ}

/-- Polynomials in a last variable with coefficients polynomial in `n` parameters. -/
abbrev ParamPoly (n : ℕ) := Polynomial (MvPolynomial (Fin n) ℝ)

/-- Real roots at `g` of the members of `F` that do not vanish identically at `g`. -/
def rootSet (F : List (ParamPoly n)) (g : Fin n → ℝ) : Set ℝ :=
  {y | ∃ P ∈ F, spec g P ≠ 0 ∧ (spec g P).IsRoot y}

theorem rootSet_finite (F : List (ParamPoly n)) (g : Fin n → ℝ) : (rootSet F g).Finite := by
  classical
  have h : rootSet F g ⊆ ⋃ P ∈ F, ((spec g P).roots.toFinset : Set ℝ) := by
    rintro y ⟨P, hP, h0, hy⟩
    exact Set.mem_biUnion hP (by simpa [Polynomial.mem_roots h0] using hy)
  exact (F.finite_toSet.biUnion fun P _ => (Finset.finite_toSet _)).subset h

/-! ### Lifting to `n + 1` variables -/

/-- The `(n+1)`-variate polynomial with the last variable as `y`. -/
def liftLast (P : ParamPoly n) : MvPolynomial (Fin (n + 1)) ℝ :=
  P.eval₂ (MvPolynomial.rename Fin.castSucc).toRingHom (MvPolynomial.X (Fin.last n))

theorem eval_liftLast (P : ParamPoly n) (g : Fin n → ℝ) (y : ℝ) :
    MvPolynomial.eval (Fin.snoc g y) (liftLast P) = (spec g P).eval y := by
  unfold liftLast spec
  rw [Polynomial.eval_map, Polynomial.hom_eval₂]
  congr 1
  · ext q
    · show MvPolynomial.eval (Fin.snoc g y) (MvPolynomial.rename Fin.castSucc (MvPolynomial.C q)) = _
      simp
    · show MvPolynomial.eval (Fin.snoc g y) (MvPolynomial.rename Fin.castSucc (MvPolynomial.X q)) = _
      rw [MvPolynomial.rename_X, MvPolynomial.eval_X, MvPolynomial.eval_X, Fin.snoc_castSucc]
  · simp

theorem eval_liftLast' (P : ParamPoly n) (h : Fin (n + 1) → ℝ) :
    MvPolynomial.eval h (liftLast P) = (spec (Fin.init h) P).eval (h (Fin.last n)) := by
  conv_lhs => rw [← Fin.snoc_init_self h]
  exact eval_liftLast P _ _

theorem continuous_snoc_left (y : ℝ) : Continuous fun g : Fin n → ℝ => (Fin.snoc g y : Fin (n + 1) → ℝ) := by
  refine continuous_pi fun j => ?_
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [Fin.snoc_last]
    exact continuous_const
  · simp only [Fin.snoc_castSucc]
    exact continuous_apply j

theorem continuous_spec_eval (P : ParamPoly n) (y : ℝ) :
    Continuous fun g : Fin n → ℝ => (spec g P).eval y := by
  have h := (MvPolynomial.continuous_eval (liftLast P)).comp (continuous_snoc_left (n := n) y)
  refine h.congr fun g => ?_
  simp only [Function.comp_apply]
  exact eval_liftLast P g y

theorem spec_ne_zero_iff (P : ParamPoly n) (g : Fin n → ℝ) :
    spec g P ≠ 0 ↔ ∃ i ∈ P.support, MvPolynomial.eval g (P.coeff i) ≠ 0 := by
  constructor
  · intro h
    by_contra hall
    push Not at hall
    apply h
    ext i
    rw [spec, Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hi : i ∈ P.support
    · exact hall i hi
    · rw [Polynomial.notMem_support_iff.mp hi, map_zero]
  · rintro ⟨i, -, hi⟩ h0
    apply hi
    have := congrArg (fun p => Polynomial.coeff p i) h0
    simpa [spec, Polynomial.coeff_map] using this

theorem saOn_spec_ne_zero (P : ParamPoly n) : SAOn {g : Fin n → ℝ | spec g P ≠ 0} := by
  refine (SAOn.finset_iUnion P.support fun i _ => SAOn.ne_zero (P.coeff i)).congr fun g => ?_
  simp [spec_ne_zero_iff]

/-! ### Semialgebraic root data -/

/-- Points `(g, y)` with `y` a root at `g`. -/
def rootGraph (F : List (ParamPoly n)) : Set (Fin (n + 1) → ℝ) :=
  {h | h (Fin.last n) ∈ rootSet F (Fin.init h)}

theorem saOn_rootGraph (F : List (ParamPoly n)) : SAOn (rootGraph F) := by
  classical
  have hP : ∀ P ∈ F, SAOn {h : Fin (n + 1) → ℝ | spec (Fin.init h) P ≠ 0 ∧
      MvPolynomial.eval h (liftLast P) = 0} := fun P _ =>
    ((saOn_spec_ne_zero P).comap Fin.castSucc).inter (SAOn.zero (liftLast P))
  refine (SAOn.list_iUnion F hP).congr fun h => ?_
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, rootGraph, rootSet,
    eval_liftLast', Polynomial.IsRoot.def]

/-- Number of roots at `init h` below the last coordinate. -/
def belowSet (F : List (ParamPoly n)) (i : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {h | i ≤ countBelow (rootSet F (Fin.init h)) (h (Fin.last n))}

/-- Drop the second-to-last coordinate. -/
def dropPenult (n : ℕ) : Fin (n + 1) → Fin (n + 2) :=
  Fin.lastCases (Fin.last (n + 1)) fun j => j.castSucc.castSucc

theorem snoc_comp_dropPenult (h : Fin (n + 1) → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin (n + 2) → ℝ) ∘ dropPenult n = Fin.snoc (Fin.init h) z := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [dropPenult]
  · simp [dropPenult, Fin.init]

theorem saOn_belowSet (F : List (ParamPoly n)) : ∀ i, SAOn (belowSet F i)
  | 0 => SAOn.univ.congr fun h => by simp [belowSet]
  | i + 1 => by
    have hA : SAOn {w : Fin (n + 2) → ℝ | w (Fin.last (n + 1)) < w (Fin.last n).castSucc ∧
        w ∘ dropPenult n ∈ rootGraph F ∧ w ∘ dropPenult n ∈ belowSet F i} :=
      ((SAOn.lt (MvPolynomial.X (Fin.last (n + 1))) (MvPolynomial.X (Fin.last n).castSucc)).congr
        (fun w => by simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X]; exact Iff.rfl)).inter
        (((saOn_rootGraph F).comap (dropPenult n)).inter ((saOn_belowSet F i).comap (dropPenult n)))
    refine (SAOn.exists_snoc hA).congr fun h => ?_
    simp only [Set.mem_ofPred_eq, snoc_comp_dropPenult, belowSet, rootGraph, Fin.snoc_last,
      Fin.init_snoc, Fin.snoc_castSucc]
    rw [succ_le_countBelow_iff (rootSet_finite F _)]
    constructor
    · rintro ⟨z, hz1, hz2, hz3⟩
      exact ⟨z, hz2, hz1, hz3⟩
    · rintro ⟨z, hz2, hz1, hz3⟩
      exact ⟨z, hz1, hz2, hz3⟩

theorem saOn_le_ncard_rootSet (F : List (ParamPoly n)) (k : ℕ) :
    SAOn {g : Fin n → ℝ | k ≤ (rootSet F g).ncard} := by
  refine (SAOn.exists_snoc (saOn_belowSet F k)).congr fun g => ?_
  simp only [Set.mem_ofPred_eq, belowSet, Fin.init_snoc, Fin.snoc_last]
  exact (le_ncard_iff_exists_countBelow (rootSet_finite F g)).symm

theorem saOn_ncard_rootSet_eq (F : List (ParamPoly n)) (k : ℕ) :
    SAOn {g : Fin n → ℝ | (rootSet F g).ncard = k} :=
  ((saOn_le_ncard_rootSet F k).diff (saOn_le_ncard_rootSet F (k + 1))).congr fun g => by
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_le]
    omega

open Classical in
/-- The slot of `y` at `g`: `2i+1` for the `i`-th root, `2i` for the gap below it. -/
def slotIndex (F : List (ParamPoly n)) (g : Fin n → ℝ) (y : ℝ) : ℕ :=
  2 * countBelow (rootSet F g) y + if y ∈ rootSet F g then 1 else 0

/-- Points `(g, y)` with `y` in slot `j` at `g`. -/
def slotSet (F : List (ParamPoly n)) (j : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {h | slotIndex F (Fin.init h) (h (Fin.last n)) = j}

theorem slotIndex_eq_iff (F : List (ParamPoly n)) (g : Fin n → ℝ) (y : ℝ) (j : ℕ) :
    slotIndex F g y = j ↔ countBelow (rootSet F g) y = j / 2 ∧ (y ∈ rootSet F g ↔ j % 2 = 1) := by
  classical
  unfold slotIndex
  by_cases hr : y ∈ rootSet F g
  · rw [ite_eq_left hr]
    simp only [hr, true_iff]
    omega
  · rw [ite_eq_right hr]
    simp only [hr, false_iff]
    omega

theorem saOn_slotSet (F : List (ParamPoly n)) (j : ℕ) : SAOn (slotSet F j) := by
  classical
  have hex : SAOn {h : Fin (n + 1) → ℝ |
      countBelow (rootSet F (Fin.init h)) (h (Fin.last n)) = j / 2} :=
    ((saOn_belowSet F (j / 2)).diff (saOn_belowSet F (j / 2 + 1))).congr fun h => by
      simp only [Set.mem_sdiff, belowSet, Set.mem_ofPred_eq, not_le]
      omega
  by_cases hj : j % 2 = 1
  · refine (hex.inter (saOn_rootGraph F)).congr fun h => ?_
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, slotSet, slotIndex_eq_iff, rootGraph, hj,
      iff_true]
  · refine (hex.diff (saOn_rootGraph F)).congr fun h => ?_
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, slotSet, slotIndex_eq_iff, rootGraph, hj,
      iff_false]

/-! ### Signs along slots -/

theorem eq_of_slotIndex_eq_of_mem {F : List (ParamPoly n)} {g : Fin n → ℝ} {y y' : ℝ}
    (hy : y ∈ rootSet F g) (h : slotIndex F g y = slotIndex F g y') : y = y' := by
  classical
  unfold slotIndex at h
  by_cases hy' : y' ∈ rootSet F g
  · rw [ite_eq_left hy, ite_eq_left hy'] at h
    exact eq_of_countBelow_eq (rootSet_finite F g) hy hy' (by omega)
  · rw [ite_eq_left hy, ite_eq_right hy'] at h
    omega

theorem not_mem_Icc_of_slotIndex_eq {F : List (ParamPoly n)} {g : Fin n → ℝ} {y y' z : ℝ}
    (hy : y ∉ rootSet F g) (h : slotIndex F g y = slotIndex F g y') (_hyy' : y ≤ y')
    (hz : z ∈ Set.Icc y y') : z ∉ rootSet F g := by
  classical
  intro hzr
  have hfin := rootSet_finite F g
  unfold slotIndex at h
  by_cases hy' : y' ∈ rootSet F g
  · rw [ite_eq_right hy, ite_eq_left hy'] at h
    omega
  · rw [ite_eq_right hy, ite_eq_right hy'] at h
    have hzy : y < z := lt_of_le_of_ne hz.1 fun e => hy (e ▸ hzr)
    have hzy' : z < y' := lt_of_le_of_ne hz.2 fun e => hy' (e ▸ hzr)
    have h1 := countBelow_mono hfin hzy.le
    have h2 := countBelow_lt hfin hzr hzy'
    omega

/-- Every member of the family has constant sign along a slot. -/
theorem sign_eq_of_slotIndex_eq {F : List (ParamPoly n)} {g : Fin n → ℝ} {P : ParamPoly n}
    (hP : P ∈ F) {y y' : ℝ} (h : slotIndex F g y = slotIndex F g y') :
    SignType.sign ((spec g P).eval y) = SignType.sign ((spec g P).eval y') := by
  by_cases h0 : spec g P = 0
  · rw [h0]
    simp
  by_cases hy : y ∈ rootSet F g
  · rw [eq_of_slotIndex_eq_of_mem hy h]
  have hy' : y' ∉ rootSet F g := fun hy' => hy ((eq_of_slotIndex_eq_of_mem hy' h.symm).symm ▸ hy')
  have hroot : ∀ {a b : ℝ}, a ∉ rootSet F g → slotIndex F g a = slotIndex F g b → a ≤ b →
      ∀ z ∈ Set.Icc a b, ¬ (spec g P).IsRoot z := fun ha hab hle z hz hzr =>
    not_mem_Icc_of_slotIndex_eq ha hab hle hz ⟨P, hP, h0, hzr⟩
  rcases le_total y y' with hle | hle
  · exact sign_eq_of_no_root_Icc _ hle (hroot hy h hle)
  · exact (sign_eq_of_no_root_Icc _ hle (hroot hy' h.symm hle)).symm

/-! ### Continuity of the roots -/

/-- Closure under the derivative in `y` (up to vanishing). -/
def DerivClosed (F : List (ParamPoly n)) : Prop :=
  ∀ P ∈ F, Polynomial.derivative P ≠ 0 → Polynomial.derivative P ∈ F

theorem spec_iterate_derivative (g : Fin n → ℝ) (P : ParamPoly n) (l : ℕ) :
    spec g (Polynomial.derivative^[l] P) = Polynomial.derivative^[l] (spec g P) := by
  unfold spec
  rw [Polynomial.iterate_derivative_map]

theorem iterate_derivative_mem {F : List (ParamPoly n)} (hF : DerivClosed F) {P : ParamPoly n}
    (hP : P ∈ F) : ∀ l, Polynomial.derivative^[l] P ≠ 0 → Polynomial.derivative^[l] P ∈ F
  | 0, _ => hP
  | l + 1, h => by
    rw [Function.iterate_succ_apply'] at h ⊢
    have hl : Polynomial.derivative^[l] P ≠ 0 := fun h0 => h (by rw [h0, map_zero])
    exact hF _ (iterate_derivative_mem hF hP l hl) h

/-- Every root is a simple root of some member. -/
theorem exists_simple_root {F : List (ParamPoly n)} (hF : DerivClosed F) {g : Fin n → ℝ} {y : ℝ}
    (hy : y ∈ rootSet F g) :
    ∃ Q ∈ F, (spec g Q).IsRoot y ∧ (Polynomial.derivative (spec g Q)).eval y ≠ 0 := by
  obtain ⟨P, hP, h0, hr⟩ := hy
  set p := spec g P
  set m := p.rootMultiplicity y
  have hm : 0 < m := (Polynomial.rootMultiplicity_pos h0).mpr hr
  have hnz : (Polynomial.derivative^[m] p).eval y ≠ 0 := by
    rw [Polynomial.eval_iterate_derivative_rootMultiplicity, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero y h0)
  have hne : ∀ l ≤ m, Polynomial.derivative^[l] P ≠ 0 := by
    intro l hl h0'
    apply hnz
    have : Polynomial.derivative^[m] p = 0 := by
      rw [show m = (m - l) + l by omega, Function.iterate_add_apply, ← spec_iterate_derivative,
        h0']
      simp [spec]
    rw [this, Polynomial.eval_zero]
  refine ⟨Polynomial.derivative^[m - 1] P,
    iterate_derivative_mem hF hP _ (hne _ (Nat.sub_le m 1)), ?_, ?_⟩
  · rw [spec_iterate_derivative]
    exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (Nat.sub_lt hm one_pos)
  · rw [spec_iterate_derivative, ← Function.iterate_succ_apply' Polynomial.derivative,
      Nat.succ_eq_add_one, Nat.sub_add_cancel hm]
    exact hnz

/-- A simple root changes sign. -/
theorem exists_sign_change {q : ℝ[X]} {a : ℝ} (hq : q.IsRoot a)
    (hd : (Polynomial.derivative q).eval a ≠ 0) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → q.eval (a - ε) * q.eval (a + ε) < 0 := by
  have hcont : Continuous fun x => (Polynomial.derivative q).eval x :=
    (Polynomial.derivative q).continuous
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.mp
      (hcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds hneg))
    refine ⟨ε₀ / 2, by positivity, fun ε hε hle => ?_⟩
    have hanti : StrictAntiOn (fun x => q.eval x) (Set.Icc (a - ε) (a + ε)) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc _ _) q.continuous.continuousOn fun x hx => ?_
      rw [Polynomial.deriv]
      refine hball ?_
      rw [interior_Icc] at hx
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have h1 := hanti ⟨le_refl _, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith : a - ε < a)
    have h2 := hanti ⟨by linarith, by linarith⟩ ⟨by linarith, le_refl _⟩ (by linarith : a < a + ε)
    simp only [hq.eq_zero] at h1 h2
    exact mul_neg_of_pos_of_neg h1 h2
  · obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.mp
      (hcont.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hpos))
    refine ⟨ε₀ / 2, by positivity, fun ε hε hle => ?_⟩
    have hmono : StrictMonoOn (fun x => q.eval x) (Set.Icc (a - ε) (a + ε)) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc _ _) q.continuous.continuousOn fun x hx => ?_
      rw [Polynomial.deriv]
      refine hball ?_
      rw [interior_Icc] at hx
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have h1 := hmono ⟨le_refl _, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith : a - ε < a)
    have h2 := hmono ⟨by linarith, by linarith⟩ ⟨by linarith, le_refl _⟩ (by linarith : a < a + ε)
    simp only [hq.eq_zero] at h1 h2
    exact mul_neg_of_neg_of_pos h1 h2

/-- A sign change gives a root in between. -/
theorem exists_root_of_mul_neg {q : ℝ[X]} {a b : ℝ} (hab : a ≤ b) (h : q.eval a * q.eval b < 0) :
    ∃ c ∈ Set.Ioo a b, q.IsRoot c := by
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo' hab q.continuous.continuousOn
      (Set.mem_Ioo.mpr ⟨hb, ha⟩)
    exact ⟨c, hc, hc0⟩
  · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo hab q.continuous.continuousOn
      (Set.mem_Ioo.mpr ⟨ha, hb⟩)
    exact ⟨c, hc, hc0⟩

/-- The `i`-th root at `g`. -/
def rootFn (F : List (ParamPoly n)) (g : Fin n → ℝ) (i : ℕ) : ℝ := nthElem (rootSet F g) i

theorem ncard_Iio_fin {k : ℕ} (i : Fin k) : (Set.Iio i).ncard = i := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_Iio, Fin.card_Iio]

/-- **Continuity of roots.** For a derivative-closed family, on a set of
parameters with a constant number `k` of roots, each root is continuous. -/
theorem continuousOn_rootFn {F : List (ParamPoly n)} (hF : DerivClosed F)
    {D : Set (Fin n → ℝ)} {k : ℕ} (hD : ∀ g ∈ D, (rootSet F g).ncard = k) {i : ℕ} (hi : i < k) :
    ContinuousOn (fun g => rootFn F g i) D := by
  intro g₀ hg₀
  have hk₀ := hD g₀ hg₀
  have hfin₀ := rootSet_finite F g₀
  let a : Fin k → ℝ := fun j => rootFn F g₀ j
  have ha_mem : ∀ j : Fin k, a j ∈ rootSet F g₀ := fun j =>
    (nthElem_spec hfin₀ (hk₀ ▸ j.2)).1
  have ha_mono : StrictMono a := fun j j' hjj' =>
    nthElem_lt_nthElem hfin₀ hjj' (hk₀ ▸ j'.2)
  choose Q hQF hQroot hQd using fun j : Fin k => exists_simple_root hF (ha_mem j)
  choose ε₀ hε₀ hchange using fun j : Fin k => exists_sign_change (hQroot j) (hQd j)
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro η hη
  -- a common window radius
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < η ∧ (∀ j, ε ≤ ε₀ j) ∧
      ∀ j j' : Fin k, j < j' → 2 * ε < a j' - a j := by
    have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
    have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < η := nhdsWithin_le_nhds (Iio_mem_nhds hη)
    have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j, ε ≤ ε₀ j :=
      Filter.eventually_all.mpr fun j => nhdsWithin_le_nhds (Iic_mem_nhds (hε₀ j))
    have e4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j j' : Fin k, j < j' → 2 * ε < a j' - a j := by
      refine Filter.eventually_all.mpr fun j => Filter.eventually_all.mpr fun j' => ?_
      by_cases hjj' : j < j'
      · have hpos : 0 < (a j' - a j) / 2 := by linarith [ha_mono hjj']
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hpos)] with ε hε _
        simp only [Set.mem_Iio] at hε
        linarith
      · exact Filter.Eventually.of_forall fun ε h => absurd h hjj'
    exact e1.and (e2.and (e3.and e4))
  obtain ⟨ε, hε, hεη, hεj, hgap⟩ := hev.exists
  have hprod : ∀ j : Fin k, ∀ᶠ g in 𝓝 g₀,
      (spec g (Q j)).eval (a j - ε) * (spec g (Q j)).eval (a j + ε) < 0 := fun j =>
    ((continuous_spec_eval (Q j) _).mul (continuous_spec_eval (Q j) _)).continuousAt.eventually_lt
      continuousAt_const (hchange j ε hε (hεj j))
  filter_upwards [nhdsWithin_le_nhds (Filter.eventually_all.mpr hprod), self_mem_nhdsWithin]
    with g hg hgD
  have hfin := rootSet_finite F g
  have hk := hD g hgD
  -- a root of `Q j` in each window
  have hc : ∀ j : Fin k, ∃ c ∈ Set.Ioo (a j - ε) (a j + ε), c ∈ rootSet F g := by
    intro j
    obtain ⟨c, hc, hcr⟩ := exists_root_of_mul_neg (by linarith) (hg j)
    have hne : spec g (Q j) ≠ 0 := by
      intro h0
      have := hg j
      rw [h0] at this
      simp at this
    exact ⟨c, hc, Q j, hQF j, hne, hcr⟩
  choose c hcwin hcroot using hc
  have hc_mono : StrictMono c := by
    intro j j' hjj'
    have h1 := (hcwin j).2
    have h2 := (hcwin j').1
    have h3 := hgap j j' hjj'
    linarith
  -- these are all the roots
  have hrange : Set.range c = rootSet F g := by
    refine Set.eq_of_subset_of_ncard_le (Set.range_subset_iff.mpr hcroot) ?_ hfin
    rw [hk, Set.ncard_range_of_injective hc_mono.injective, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hbelow : {z | z ∈ rootSet F g ∧ z < c ⟨i, hi⟩} = c '' Set.Iio ⟨i, hi⟩ := by
    ext z
    constructor
    · rintro ⟨hz, hzc⟩
      rw [← hrange] at hz
      obtain ⟨j, rfl⟩ := hz
      exact ⟨j, hc_mono.lt_iff_lt.mp hzc, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hcroot j, hc_mono hj⟩
  have hcount : countBelow (rootSet F g) (c ⟨i, hi⟩) = i := by
    unfold countBelow
    rw [hbelow, Set.ncard_image_of_injective _ hc_mono.injective, ncard_Iio_fin]
  have heq : rootFn F g i = c ⟨i, hi⟩ :=
    ((eq_nthElem_iff hfin (hk ▸ hi)).mpr ⟨hcroot _, hcount⟩).symm
  rw [heq, Real.dist_eq]
  have hw := hcwin ⟨i, hi⟩
  change |c ⟨i, hi⟩ - a ⟨i, hi⟩| < η
  rw [abs_lt]
  constructor <;> linarith [hw.1, hw.2]

end NLQCLean
