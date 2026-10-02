import NLQCLean.Semialgebraic.ScalarNullFinite
import NLQCLean.Semialgebraic.PolynomialFunctions
import NLQCLean.Exact.RationalPolynomialSmoothness
import NLQCLean.Semialgebraic.ProjectionTheorem
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Continuous semialgebraic functions are piecewise C¹ (`fact:piecewise`)

A continuous function on `[0,1]` with semialgebraic graph is continuously
differentiable away from finitely many points. The graph lies in the zero set
of a nonzero polynomial `P`; let `D j = ∂_y^j P`, which vanishes for large `j`.
Each set `Z j = {x ∈ [0,1] | D j (x, f x) = 0}` is semialgebraic (proved
projection), so has finite frontier. Off these frontiers and the finitely many
vertical zero lines of the last nonzero `D k`, take the least `j` with
`x ∉ Z j`: then `D (j-1)` vanishes along the graph near `x` while its
`y`-derivative does not, and the implicit function theorem makes `f` C¹ at `x`.
-/

noncomputable section

namespace NLQCLean

open MvPolynomial Filter Set
open scoped Topology ContDiff

section PolynomialCalculus

/-- Evaluation of a bivariate polynomial. -/
def eval2 (Q : MvPolynomial (Fin 2) ℝ) (x y : ℝ) : ℝ := MvPolynomial.eval ![x, y] Q

/-- Derivative of polynomial evaluation along one coordinate. -/
theorem hasDerivAt_eval_update {σ : Type*} [DecidableEq σ] (Q : MvPolynomial σ ℝ)
    (v : σ → ℝ) (i : σ) (t : ℝ) :
    HasDerivAt (fun s => MvPolynomial.eval (Function.update v i s) Q)
      (MvPolynomial.eval (Function.update v i t) (pderiv i Q)) t := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero]
    exact hasDerivAt_const t a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p j hp =>
    have hj : HasDerivAt (fun s => Function.update v i s j)
        (if j = i then 1 else 0) t := by
      by_cases h : j = i
      · subst h
        simp only [Function.update_self, ite_true]
        exact hasDerivAt_id' t
      · simp only [Function.update_of_ne h, ite_eq_right h]
        exact hasDerivAt_const t (v j)
    simp only [map_mul, eval_X]
    refine (hp.mul hj).congr_deriv ?_
    rw [Derivation.leibniz, pderiv_X]
    by_cases h : j = i
    · subst h
      simp
      ring
    · simp [h]
      ring

theorem hasDerivAt_eval2_right (Q : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    HasDerivAt (fun s => eval2 Q x s) (eval2 (pderiv 1 Q) x y) y := by
  have h := hasDerivAt_eval_update Q ![x, y] 1 y
  have hu : ∀ s, Function.update ![x, y] 1 s = ![x, s] := fun s => by
    funext k
    fin_cases k <;> simp
  simpa only [eval2, hu] using h

/-- If `∂_y Q = 0` then `Q` does not depend on `y`. -/
theorem eval2_eq_of_pderiv_eq_zero {Q : MvPolynomial (Fin 2) ℝ} (hQ : pderiv 1 Q = 0)
    (x y : ℝ) : eval2 Q x y = eval2 Q x 0 := by
  have h : ∀ s, HasDerivAt (fun s => eval2 Q x s) 0 s := fun s => by
    simpa [hQ, eval2] using hasDerivAt_eval2_right Q x s
  exact is_const_of_deriv_eq_zero (fun s => (h s).differentiableAt)
    (fun s => (h s).deriv) y 0

/-- `∂_y` strictly lowers the total degree of a polynomial it does not kill. -/
theorem totalDegree_pderiv_lt {σ : Type*} [DecidableEq σ] {p : MvPolynomial σ ℝ} {i : σ}
    (h : pderiv i p ≠ 0) : (pderiv i p).totalDegree < p.totalDegree := by
  have hmem : ∀ m ∈ (pderiv i p).support, (m.sum fun _ e => e) < p.totalDegree := by
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have hc : p.coeff (m + Finsupp.single i 1) ≠ 0 := fun h0 => hm (by simp [h0])
    have hle := le_totalDegree (mem_support_iff.mpr hc)
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl] at hle
    omega
  obtain ⟨m0, hm0⟩ := MvPolynomial.support_nonempty.mpr h
  have hpos : 0 < p.totalDegree := lt_of_le_of_lt (Nat.zero_le _) (hmem m0 hm0)
  rw [totalDegree, Finset.sup_lt_iff hpos]
  exact hmem

theorem eval_aeval_vertical (Q : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    (MvPolynomial.aeval (fun k : Fin 2 => if k = 0 then Polynomial.X else Polynomial.C y)
      Q).eval x = eval2 Q x y := by
  unfold eval2
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, Polynomial.eval_mul, aeval_X, hp, eval_X]
    fin_cases j <;> simp

/-- A nonzero bivariate polynomial vanishes identically on only finitely many
vertical lines. -/
theorem finite_vertical_zeros {Q : MvPolynomial (Fin 2) ℝ} (hQ : Q ≠ 0) :
    {x : ℝ | ∀ y, eval2 Q x y = 0}.Finite := by
  by_contra hinf
  apply hQ
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by
    funext k
    fin_cases k <;> rfl
  rw [hv, map_zero]
  -- For fixed `y`, `x ↦ Q(x, y)` is a polynomial with infinitely many roots.
  set y := v 1
  let px : Polynomial ℝ :=
    MvPolynomial.aeval (fun k : Fin 2 => if k = 0 then Polynomial.X else Polynomial.C y) Q
  have hzero : px = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot px (Set.Infinite.mono ?_ hinf)
    intro x hx
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, px, eval_aeval_vertical] at hx ⊢
    exact hx y
  have := eval_aeval_vertical Q (v 0) y
  rw [show MvPolynomial.aeval (fun k : Fin 2 => if k = 0 then Polynomial.X else Polynomial.C y)
    Q = px from rfl, hzero, Polynomial.eval_zero] at this
  exact this.symm

end PolynomialCalculus

section Implicit

/-- **Polynomial implicit functions.** If `Q(x, f x) = 0` near `x₁`, `f` is
continuous at `x₁` and `∂_y Q(x₁, f x₁) ≠ 0`, then `f` is C¹ at `x₁`. -/
theorem contDiffAt_of_polynomial_implicit {Q : MvPolynomial (Fin 2) ℝ} {f : ℝ → ℝ} {x₁ : ℝ}
    (hf : ContinuousAt f x₁) (hQ : ∀ᶠ x in 𝓝 x₁, eval2 Q x (f x) = 0)
    (hdQ : eval2 (pderiv 1 Q) x₁ (f x₁) ≠ 0) : ContDiffAt ℝ 1 f x₁ := by
  let q : ℝ × ℝ → ℝ := fun p => eval2 Q p.1 p.2
  let u : ℝ × ℝ := (x₁, f x₁)
  have hq : ContDiff ℝ ∞ q := by
    unfold q eval2
    refine contDiff_mvPolynomial_eval_comp (fun k => ?_) Q
    fin_cases k
    · simpa using (contDiff_fst : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1))
    · simpa using (contDiff_snd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2))
  have hcd : ContDiffAt ℝ 1 q u := (hq.of_le (by simp)).contDiffAt
  -- The partial derivative in `y`.
  set c := eval2 (pderiv 1 Q) x₁ (f x₁)
  have hline : HasDerivAt (fun s => q (u.1, s)) c u.2 := hasDerivAt_eval2_right Q x₁ (f x₁)
  have hfd : HasFDerivAt q (fderiv ℝ q u) u := (hq.differentiable (by simp) u).hasFDerivAt
  have hinr : HasDerivAt (fun s : ℝ => (u.1, s)) ((0 : ℝ), (1 : ℝ)) u.2 :=
    HasDerivAt.prodMk (hasDerivAt_const u.2 u.1) (hasDerivAt_id u.2)
  have hval : fderiv ℝ q u ((0 : ℝ), (1 : ℝ)) = c :=
    (hfd.comp_hasDerivAt u.2 hinr).unique hline
  have hL : (fderiv ℝ q u ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) = c • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [hval]
  have hinv : (fderiv ℝ q u ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hL]
    refine ⟨(ContinuousLinearEquiv.unitsEquivAut ℝ) (Units.mk0 c hdQ), ?_⟩
    ext
    simp [ContinuousLinearEquiv.unitsEquivAut]
  have hψ := hcd.contDiffAt_implicitFunction one_ne_zero hinv
  have hev := hcd.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv
  have hq0 : q u = 0 := hQ.self_of_nhds
  have ht : Tendsto (fun x => (x, f x)) (𝓝 x₁) (𝓝 u) :=
    (continuousAt_id.prodMk hf).tendsto
  have hfe : f =ᶠ[𝓝 x₁] hcd.implicitFunction one_ne_zero hinv := by
    filter_upwards [ht.eventually hev, hQ] with x hx hQx
    have : q (x, f x) = q u := by rw [hq0]; exact hQx
    exact ((hx.mp this)).symm
  exact hψ.congr_of_eventuallyEq hfe

end Implicit

section Line

/-- The real line as one-coordinate Euclidean space. -/
def lineHomeomorph : ℝ ≃ₜ RealEuclidean 1 where
  toFun t := WithLp.toLp 2 (fun _ => t)
  invFun y := y 0
  left_inv _ := rfl
  right_inv y := by
    ext i
    fin_cases i
    rfl
  continuous_toFun := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_id)
  continuous_invFun := (continuous_apply 0).comp (PiLp.continuous_ofLp 2 _)

/-- A semialgebraic subset of the line has finite frontier. -/
theorem finite_frontier_of_semialgebraic_line {S : Set ℝ}
    (hS : Semialgebraic {y : RealEuclidean 1 | y 0 ∈ S}) : (frontier S).Finite := by
  classical
  obtain ⟨F, hF⟩ := hS
  have hpre : S = lineHomeomorph ⁻¹' F.source := by
    rw [hF]
    rfl
  have hsub : frontier S ⊆ ⋃ L ∈ F.clauses.toFinset, ⋃ A ∈ L.toFinset,
      {t : ℝ | A.polynomial ≠ 0 ∧ MvPolynomial.eval (fun _ => t) A.polynomial = 0} := by
    intro t ht
    rw [hpre, ← Homeomorph.preimage_frontier] at ht
    obtain ⟨L, hL, A, hA, hA0, hAt⟩ := F.exists_nonzero_polynomial_zero_of_mem_frontier ht
    simp only [Set.mem_iUnion, List.mem_toFinset]
    exact ⟨L, hL, A, hA, hA0, hAt⟩
  refine Set.Finite.subset ?_ hsub
  refine (F.clauses.toFinset.finite_toSet).biUnion fun L _ => ?_
  refine (L.toFinset.finite_toSet).biUnion fun A _ => ?_
  by_cases hA : A.polynomial = 0
  · simp [hA]
  · exact (finite_setOf_eval_const_eq_zero hA).subset fun t ht => ht.2

end Line

section Graph

variable {f : ℝ → ℝ}

/-- The graph of `f` over `[0,1]` in the Euclidean plane. -/
def unitGraph (f : ℝ → ℝ) : Set (RealEuclidean 2) := {p | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 = f (p 0)}

theorem eval_pair (R : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    MvPolynomial.eval (fun i => (WithLp.toLp 2 ![x, y] : RealEuclidean 2) i) R = eval2 R x y := by
  unfold eval2
  congr 1

/-- Zeros of a polynomial along the graph form a semialgebraic subset of the line. -/
theorem semialgebraic_graph_zeros (hΓ : Semialgebraic (unitGraph f)) (R : MvPolynomial (Fin 2) ℝ) :
    Semialgebraic {y : RealEuclidean 1 | y 0 ∈ {x | x ∈ Icc (0 : ℝ) 1 ∧ eval2 R x (f x) = 0}} := by
  have hT := hΓ.inter (Semialgebraic.polynomial_zero (n := 2) R)
  have h := semialgebraicProjectionTheorem 1 _ hT
  convert h using 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_inter_iff, unitGraph]
  constructor
  · rintro ⟨hy, hR⟩
    refine ⟨WithLp.toLp 2 ![y 0, f (y 0)], ⟨⟨hy, rfl⟩, ?_⟩, ?_⟩
    · rw [eval_pair]
      exact hR
    · ext i
      fin_cases i
      rfl
  · rintro ⟨p, ⟨⟨hp0, hp1⟩, hpR⟩, rfl⟩
    refine ⟨hp0, ?_⟩
    have hpv : p = WithLp.toLp 2 ![p 0, f (p 0)] := by
      ext i
      fin_cases i
      · rfl
      · exact hp1
    rw [hpv, eval_pair] at hpR
    simpa [coordinateProjection] using hpR

theorem finite_frontier_graph_zeros (hΓ : Semialgebraic (unitGraph f))
    (R : MvPolynomial (Fin 2) ℝ) :
    (frontier {x | x ∈ Icc (0 : ℝ) 1 ∧ eval2 R x (f x) = 0}).Finite :=
  finite_frontier_of_semialgebraic_line (semialgebraic_graph_zeros hΓ R)

/-- The graph lies in the zero set of a nonzero polynomial. -/
theorem exists_polynomial_vanishing_on_graph (hΓ : Semialgebraic (unitGraph f)) :
    ∃ P : MvPolynomial (Fin 2) ℝ, P ≠ 0 ∧ ∀ x ∈ Icc (0 : ℝ) 1, eval2 P x (f x) = 0 := by
  classical
  obtain ⟨F, hF⟩ := hΓ
  let atoms := ((F.clauses.flatten).map PolynomialSignAtom.polynomial).filter (· ≠ 0)
  refine ⟨atoms.prod, ?_, fun x hx => ?_⟩
  · refine List.prod_ne_zero fun h0 => ?_
    have := (List.mem_filter.mp h0).2
    simp at this
  · let p : RealEuclidean 2 := WithLp.toLp 2 ![x, f x]
    have hp : p ∈ F.source := by
      rw [hF]
      exact ⟨hx, rfl⟩
    have hfr : p ∈ frontier F.source := by
      let g : ℝ → RealEuclidean 2 := fun t => WithLp.toLp 2 ![x, f x + t]
      have hg : Continuous g :=
        (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => by
          fin_cases i
          · exact continuous_const
          · exact continuous_const.add continuous_id)
      have hg0 : g 0 = p := by simp [g, p]
      rw [frontier_eq_closure_inter_closure]
      refine ⟨subset_closure hp, ?_⟩
      have ht : Filter.Tendsto g (𝓝[≠] 0) (𝓝 p) :=
        hg0 ▸ hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto ht ?_
      filter_upwards [self_mem_nhdsWithin] with t ht0 hmem
      rw [hF] at hmem
      have h1 := hmem.2
      simp [g] at h1
      exact ht0 h1
    obtain ⟨L, hL, A, hA, hA0, hAp⟩ := F.exists_nonzero_polynomial_zero_of_mem_frontier hfr
    rw [eval_pair] at hAp
    unfold eval2
    rw [map_list_prod]
    refine List.prod_eq_zero ?_
    refine List.mem_map.mpr ⟨A.polynomial, List.mem_filter.mpr ⟨List.mem_map.mpr
      ⟨A, List.mem_flatten.mpr ⟨L, hL, hA⟩, rfl⟩, by simpa using hA0⟩, ?_⟩
    exact hAp

end Graph

section Piecewise

open MvPolynomial

theorem iterate_pderiv_totalDegree {P : MvPolynomial (Fin 2) ℝ} :
    ∀ j, (pderiv 1)^[j] P ≠ 0 → ((pderiv 1)^[j] P).totalDegree + j ≤ P.totalDegree
  | 0, _ => by simp
  | j + 1, h => by
    rw [Function.iterate_succ_apply'] at h ⊢
    have hj : (pderiv 1)^[j] P ≠ 0 := fun h0 => h (by rw [h0, map_zero])
    have h1 := totalDegree_pderiv_lt h
    have h2 := iterate_pderiv_totalDegree j hj
    omega

theorem iterate_pderiv_eq_zero (P : MvPolynomial (Fin 2) ℝ) :
    (pderiv 1)^[P.totalDegree + 1] P = 0 := by
  by_contra h
  have := iterate_pderiv_totalDegree _ h
  omega

/-- **`fact:piecewise`.** A continuous function on `[0,1]` with semialgebraic
graph is continuously differentiable away from finitely many points. -/
theorem fact_piecewise {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hsa : Semialgebraic {p : RealEuclidean 2 | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 = f (p 0)}) :
    ∃ Bad : Set ℝ, Bad.Finite ∧ ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ Bad → ContDiffAt ℝ 1 f x := by
  classical
  have hΓ : Semialgebraic (unitGraph f) := hsa
  obtain ⟨P, hP0, hP⟩ := exists_polynomial_vanishing_on_graph hΓ
  let D : ℕ → MvPolynomial (Fin 2) ℝ := fun j => (pderiv 1)^[j] P
  have hex : ∃ j, D (j + 1) = 0 := ⟨_, iterate_pderiv_eq_zero P⟩
  let k := Nat.find hex
  have hDk : D k ≠ 0 := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk]
      exact hP0
    · have := Nat.find_min hex (Nat.sub_lt hk one_pos)
      have e : Nat.find hex - 1 + 1 = k := Nat.sub_add_cancel hk
      rwa [e] at this
  have hDk1 : pderiv 1 (D k) = 0 := by
    have := Nat.find_spec hex
    change (pderiv 1)^[k + 1] P = 0 at this
    rwa [Function.iterate_succ_apply'] at this
  let Z : ℕ → Set ℝ := fun j => {x | x ∈ Icc (0 : ℝ) 1 ∧ eval2 (D j) x (f x) = 0}
  refine ⟨(⋃ j ∈ Finset.range (k + 1), frontier (Z j)) ∪ {x | ∀ y, eval2 (D k) x y = 0},
    ((Finset.range (k + 1)).finite_toSet.biUnion fun j _ =>
      finite_frontier_graph_zeros hΓ (D j)).union (finite_vertical_zeros hDk), ?_⟩
  intro x₀ hx₀ hBad
  simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_range, not_or, not_exists] at hBad
  obtain ⟨hfr, hvert⟩ := hBad
  have hIcc : x₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx₀
  have hbad : ∃ j, x₀ ∉ Z j := by
    refine ⟨k, fun h => hvert fun y => ?_⟩
    rw [eval2_eq_of_pderiv_eq_zero hDk1, ← eval2_eq_of_pderiv_eq_zero hDk1 x₀ (f x₀)]
    exact h.2
  let j := Nat.find hbad
  have hj0 : j ≠ 0 := by
    intro h
    have := Nat.find_spec hbad
    rw [show Nat.find hbad = 0 from h] at this
    exact this ⟨hIcc, hP x₀ hIcc⟩
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hjk : j ≤ k := Nat.find_min' hbad fun h => hvert fun y => by
    rw [eval2_eq_of_pderiv_eq_zero hDk1, ← eval2_eq_of_pderiv_eq_zero hDk1 x₀ (f x₀)]
    exact h.2
  have hZi : x₀ ∈ Z i := by
    by_contra h
    have := Nat.find_min' hbad h
    change j ≤ i at this
    omega
  have hint : x₀ ∈ interior (Z i) := by
    by_contra h
    exact hfr i (by omega) ⟨subset_closure hZi, h⟩
  have hev : ∀ᶠ x in 𝓝 x₀, eval2 (D i) x (f x) = 0 :=
    Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp hint) fun x hx => hx.2
  have hnz : eval2 (pderiv 1 (D i)) x₀ (f x₀) ≠ 0 := by
    have hspec := Nat.find_spec hbad
    change x₀ ∉ Z j at hspec
    rw [hi] at hspec
    intro h
    refine hspec ⟨hIcc, ?_⟩
    change eval2 ((pderiv 1)^[i + 1] P) x₀ (f x₀) = 0
    rw [Function.iterate_succ_apply']
    exact h
  exact contDiffAt_of_polynomial_implicit
    (hf.continuousAt (Icc_mem_nhds hx₀.1 hx₀.2)) hev hnz

/-- **`fact:piecewise`, vector form.** A continuous path in `ℝ^n` over `[0,1]`
whose coordinate graphs are semialgebraic is continuously differentiable away
from finitely many points. -/
theorem fact_piecewise_vector {n : ℕ} {γ : ℝ → RealEuclidean n} (hγ : ContinuousOn γ (Icc 0 1))
    (hsa : ∀ i, Semialgebraic {p : RealEuclidean 2 | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 = γ (p 0) i}) :
    ∃ Bad : Set ℝ, Bad.Finite ∧ ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ Bad → ContDiffAt ℝ 1 γ x := by
  choose B hB hC using fun i =>
    fact_piecewise (f := fun t => γ t i) ((PiLp.continuous_apply 2 _ i).comp_continuousOn hγ)
      (hsa i)
  refine ⟨⋃ i, B i, Set.finite_iUnion hB, fun x hx hxB => ?_⟩
  exact contDiffAt_piLp' 2 fun i => hC i x hx fun h => hxB (Set.mem_iUnion.mpr ⟨i, h⟩)

end Piecewise

end NLQCLean
