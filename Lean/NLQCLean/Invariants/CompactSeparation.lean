import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Polynomial invariants separate orbits of compact linear actions

Let a compact group act continuously on `ℝ^σ` by matrices, and let `μ` be a
left-invariant probability measure. Averaging a polynomial over the group
gives an invariant polynomial. By Urysohn and Stone–Weierstrass, two distinct
orbits are separated by such an average. The Hilbert basis theorem then
selects finitely many invariant polynomials that separate all orbits.
-/

noncomputable section

namespace NLQCLean

open MeasureTheory MvPolynomial
open scoped Matrix

universe u v

section Representation

variable {σ : Type u} [Fintype σ] [DecidableEq σ]

/-- A polynomial composed with a linear substitution, written as a finite sum
of monomials with continuous coefficient functions of the substitution. -/
structure LinearSubstRep (p : MvPolynomial σ ℝ) where
  /-- Index type of the monomial terms. -/
  ι : Type u
  [fintype : Fintype ι]
  /-- Exponents of each term. -/
  e : ι → σ → ℕ
  /-- Coefficient of each term, as a function of the substitution matrix. -/
  c : ι → Matrix σ σ ℝ → ℝ
  continuous_c : ∀ i, Continuous (c i)
  eval_eq : ∀ (M : Matrix σ σ ℝ) (z : σ → ℝ),
    eval (M *ᵥ z) p = ∑ i, c i M * ∏ k, z k ^ e i k

attribute [instance] LinearSubstRep.fintype

theorem prod_pow_add_single (z : σ → ℝ) (a : σ → ℕ) (k : σ) :
    ∏ j, z j ^ (a j + (Pi.single k (1 : ℕ) : σ → ℕ) j) = (∏ j, z j ^ a j) * z k := by
  simp only [pow_add, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- Every polynomial admits such a representation. -/
theorem nonempty_linearSubstRep (p : MvPolynomial σ ℝ) : Nonempty (LinearSubstRep p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact ⟨⟨PUnit, fun _ _ => 0, fun _ _ => a, fun _ => continuous_const, by simp⟩⟩
  | add p q hp hq =>
    obtain ⟨R₁⟩ := hp
    obtain ⟨R₂⟩ := hq
    refine ⟨⟨R₁.ι ⊕ R₂.ι, Sum.elim R₁.e R₂.e, Sum.elim R₁.c R₂.c, ?_, ?_⟩⟩
    · rintro (i | i)
      · exact R₁.continuous_c i
      · exact R₂.continuous_c i
    · intro M z
      rw [eval_add, R₁.eval_eq, R₂.eval_eq, Fintype.sum_sum_type]
      rfl
  | mul_X p n hp =>
    obtain ⟨R⟩ := hp
    refine ⟨⟨R.ι × σ, fun ik => R.e ik.1 + (Pi.single ik.2 (1 : ℕ) : σ → ℕ),
      fun ik M => R.c ik.1 M * M n ik.2, ?_, ?_⟩⟩
    · rintro ⟨i, k⟩
      exact (R.continuous_c i).mul ((continuous_apply k).comp (continuous_apply n))
    · intro M z
      rw [eval_mul, eval_X, R.eval_eq, Fintype.sum_prod_type, Matrix.mulVec, dotProduct,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.add_apply]
      rw [prod_pow_add_single]
      ring

end Representation

section Averaging

variable {G : Type v} [Group G] [TopologicalSpace G]
variable {σ : Type u} [Fintype σ] [DecidableEq σ]

/-- A continuous linear representation of `G` on `ℝ^σ`, given by matrices. -/
structure MatrixRepresentation (G : Type v) [Group G] [TopologicalSpace G]
    (σ : Type u) [Fintype σ] [DecidableEq σ] where
  /-- The representing matrices. -/
  toMatrix : G → Matrix σ σ ℝ
  continuous_toMatrix : Continuous toMatrix
  map_one : toMatrix 1 = 1
  map_mul : ∀ g h, toMatrix (g * h) = toMatrix g * toMatrix h

namespace MatrixRepresentation

variable (ρ : MatrixRepresentation G σ)

/-- The orbit of a coordinate vector. -/
def orbit (x : σ → ℝ) : Set (σ → ℝ) := Set.range fun g => ρ.toMatrix g *ᵥ x

/-- A polynomial is invariant if it is constant on every orbit. -/
def IsInvariant (p : MvPolynomial σ ℝ) : Prop :=
  ∀ g (z : σ → ℝ), eval (ρ.toMatrix g *ᵥ z) p = eval z p

theorem toMatrix_inv_mul (g : G) : ρ.toMatrix g⁻¹ * ρ.toMatrix g = 1 := by
  rw [← ρ.map_mul, inv_mul_cancel, ρ.map_one]

theorem mem_orbit_self (x : σ → ℝ) : x ∈ ρ.orbit x :=
  ⟨1, by simp [ρ.map_one]⟩

theorem orbit_symm {x y : σ → ℝ} (h : y ∈ ρ.orbit x) : x ∈ ρ.orbit y := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  show ρ.toMatrix g⁻¹ *ᵥ (ρ.toMatrix g *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, toMatrix_inv_mul, Matrix.one_mulVec]

theorem orbit_trans {x y z : σ → ℝ} (hxy : y ∈ ρ.orbit x) (hyz : z ∈ ρ.orbit y) :
    z ∈ ρ.orbit x := by
  obtain ⟨g, rfl⟩ := hxy
  obtain ⟨h, rfl⟩ := hyz
  exact ⟨h * g, by
    show ρ.toMatrix (h * g) *ᵥ x = ρ.toMatrix h *ᵥ (ρ.toMatrix g *ᵥ x)
    rw [ρ.map_mul, Matrix.mulVec_mulVec]⟩

theorem isCompact_orbit [CompactSpace G] (x : σ → ℝ) : IsCompact (ρ.orbit x) :=
  isCompact_range ((Continuous.matrix_mulVec ρ.continuous_toMatrix continuous_const))

theorem disjoint_orbit {x y : σ → ℝ} (h : y ∉ ρ.orbit x) :
    Disjoint (ρ.orbit x) (ρ.orbit y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  exact h (ρ.orbit_trans hzx (ρ.orbit_symm hzy))

theorem IsInvariant.eval_eq_of_mem_orbit {p : MvPolynomial σ ℝ} (hp : ρ.IsInvariant p)
    {x y : σ → ℝ} (h : y ∈ ρ.orbit x) : eval y p = eval x p := by
  obtain ⟨g, rfl⟩ := h
  exact hp g x

theorem continuous_toMatrix_inv [IsTopologicalGroup G] :
    Continuous fun g : G => ρ.toMatrix g⁻¹ :=
  ρ.continuous_toMatrix.comp continuous_inv

variable [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [IsProbabilityMeasure μ]

/-- The group average of a polynomial, built from a chosen continuous
monomial representation. -/
def average (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  let R := Classical.choice (nonempty_linearSubstRep p)
  ∑ i, C (∫ g, R.c i (ρ.toMatrix g⁻¹) ∂μ) * ∏ k, X k ^ R.e i k

/-- Evaluating the average is averaging the evaluations. -/
theorem eval_average (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    eval z (ρ.average μ p) = ∫ g, eval (ρ.toMatrix g⁻¹ *ᵥ z) p ∂μ := by
  let R := Classical.choice (nonempty_linearSubstRep p)
  have hint : ∀ i, Integrable (fun g => R.c i (ρ.toMatrix g⁻¹)) μ := fun i =>
    ((R.continuous_c i).comp ρ.continuous_toMatrix_inv).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change eval z (∑ i, C (∫ g, R.c i (ρ.toMatrix g⁻¹) ∂μ) * ∏ k, X k ^ R.e i k) = _
  simp_rw [R.eval_eq]
  rw [integral_finsetSum _ (fun i _ => (hint i).mul_const _)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_const, eval_mul, eval_C, map_prod]
  simp only [map_pow, eval_X]

theorem integrable_eval_orbit (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    Integrable (fun g => eval (ρ.toMatrix g⁻¹ *ᵥ z) p) μ :=
  ((MvPolynomial.continuous_eval p).comp
      (ρ.continuous_toMatrix_inv.matrix_mulVec continuous_const)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

variable [μ.IsMulLeftInvariant]

/-- The average is invariant. Only left invariance of `μ` is used. -/
theorem isInvariant_average (p : MvPolynomial σ ℝ) : ρ.IsInvariant (ρ.average μ p) := by
  intro h z
  rw [eval_average, eval_average]
  have hfun : (fun g : G => eval (ρ.toMatrix g⁻¹ *ᵥ (ρ.toMatrix h *ᵥ z)) p) =
      fun g => (fun k : G => eval (ρ.toMatrix k⁻¹ *ᵥ z) p) (h⁻¹ * g) := by
    funext g
    show eval (ρ.toMatrix g⁻¹ *ᵥ (ρ.toMatrix h *ᵥ z)) p = eval (ρ.toMatrix (h⁻¹ * g)⁻¹ *ᵥ z) p
    rw [Matrix.mulVec_mulVec, ← ρ.map_mul, mul_inv_rev, inv_inv]
  rw [hfun, integral_mul_left_eq_self (fun k : G => eval (ρ.toMatrix k⁻¹ *ᵥ z) p) h⁻¹]

omit [Fintype σ] [DecidableEq σ] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G] in
/-- Polynomial approximation on a compact subset of `ℝ^σ`. -/
theorem exists_polynomial_near {K : Set (σ → ℝ)} (hK : IsCompact K)
    (f : C(σ → ℝ, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial σ ℝ, ∀ z ∈ K, |eval z p - f z| < ε := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let coord : σ → C(K, ℝ) := fun i =>
    ⟨fun z => (z : σ → ℝ) i, (continuous_apply i).comp continuous_subtype_val⟩
  let A : Subalgebra ℝ C(K, ℝ) := (MvPolynomial.aeval coord).range
  have hcoord : ∀ (p : MvPolynomial σ ℝ) (z : K), MvPolynomial.aeval coord p z = eval z.1 p := by
    intro p z
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p n hp => simp [hp, coord]
  have hsep : A.SeparatesPoints := by
    intro z w hzw
    have : (z : σ → ℝ) ≠ w := fun h => hzw (Subtype.ext h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp this
    refine ⟨coord i, ⟨coord i, ⟨X i, by simp⟩, rfl⟩, hi⟩
  obtain ⟨⟨g, hgA⟩, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    A hsep (f.restrict K) ε hε
  obtain ⟨p, rfl⟩ := hgA
  refine ⟨p, fun z hz => ?_⟩
  have hle := ContinuousMap.norm_coe_le_norm (MvPolynomial.aeval coord p - f.restrict K) ⟨z, hz⟩
  rw [ContinuousMap.sub_apply, hcoord, ContinuousMap.restrict_apply, Real.norm_eq_abs] at hle
  exact lt_of_le_of_lt hle hg

include μ in
/-- **Separation of two orbits.** Distinct orbits of a compact linear action
are separated by an invariant real polynomial. -/
theorem exists_invariant_separating {x y : σ → ℝ} (hxy : y ∉ ρ.orbit x) :
    ∃ p : MvPolynomial σ ℝ, ρ.IsInvariant p ∧ eval x p ≠ eval y p := by
  obtain ⟨f, hf0, hf1, -⟩ := exists_continuous_zero_one_of_isClosed
    (ρ.isCompact_orbit x).isClosed (ρ.isCompact_orbit y).isClosed (ρ.disjoint_orbit hxy)
  obtain ⟨p, hp⟩ := exists_polynomial_near ((ρ.isCompact_orbit x).union (ρ.isCompact_orbit y)) f
    (show (0 : ℝ) < 1 / 3 by norm_num)
  refine ⟨ρ.average μ p, ρ.isInvariant_average μ p, ?_⟩
  have hx : eval x (ρ.average μ p) ≤ 1 / 3 := by
    rw [eval_average]
    have hb : ∀ g : G, eval (ρ.toMatrix g⁻¹ *ᵥ x) p ≤ 1 / 3 := by
      intro g
      have hz : ρ.toMatrix g⁻¹ *ᵥ x ∈ ρ.orbit x := ⟨g⁻¹, rfl⟩
      have h := hp _ (Or.inl hz)
      rw [hf0 hz, Pi.zero_apply, sub_zero] at h
      exact (abs_lt.mp h).2.le
    calc ∫ g, eval (ρ.toMatrix g⁻¹ *ᵥ x) p ∂μ ≤ ∫ _g, (1 / 3 : ℝ) ∂μ :=
          integral_mono (ρ.integrable_eval_orbit μ p x) (integrable_const _) hb
      _ = 1 / 3 := by simp
  have hy : 2 / 3 ≤ eval y (ρ.average μ p) := by
    rw [eval_average]
    have hb : ∀ g : G, (2 / 3 : ℝ) ≤ eval (ρ.toMatrix g⁻¹ *ᵥ y) p := by
      intro g
      have hz : ρ.toMatrix g⁻¹ *ᵥ y ∈ ρ.orbit y := ⟨g⁻¹, rfl⟩
      have h := hp _ (Or.inr hz)
      rw [hf1 hz, Pi.one_apply] at h
      linarith [(abs_lt.mp h).1]
    calc (2 / 3 : ℝ) = ∫ _g, (2 / 3 : ℝ) ∂μ := by simp
      _ ≤ ∫ g, eval (ρ.toMatrix g⁻¹ *ᵥ y) p ∂μ :=
          integral_mono (integrable_const _) (ρ.integrable_eval_orbit μ p y) hb
  intro h
  rw [h] at hx
  linarith

omit [Fintype σ] [DecidableEq σ] in
/-- The two-copy difference polynomial `p(x) - p(y)`. -/
def doubled (p : MvPolynomial σ ℝ) : MvPolynomial (σ ⊕ σ) ℝ :=
  rename Sum.inl p - rename Sum.inr p

omit [Fintype σ] [DecidableEq σ] in
theorem eval_doubled (p : MvPolynomial σ ℝ) (x y : σ → ℝ) :
    eval (Sum.elim x y) (doubled p) = eval x p - eval y p := by
  simp [doubled, eval_rename, Function.comp_def]

include μ in
/-- **Finite separating family.** Finitely many invariant real polynomials
separate all orbits of a continuous compact linear action. -/
theorem exists_finite_separating_invariants :
    ∃ s : Finset (MvPolynomial σ ℝ), (∀ p ∈ s, ρ.IsInvariant p) ∧
      ∀ x y : σ → ℝ, (∀ p ∈ s, eval x p = eval y p) → y ∈ ρ.orbit x := by
  classical
  let fam : Set (Ideal (MvPolynomial (σ ⊕ σ) ℝ)) :=
    {I | ∃ s : Finset (MvPolynomial σ ℝ), (∀ p ∈ s, ρ.IsInvariant p) ∧
      I = Ideal.span (doubled '' (s : Set (MvPolynomial σ ℝ)))}
  have hne : fam.Nonempty := ⟨_, ∅, by simp, rfl⟩
  obtain ⟨J, ⟨s, hs, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance :
      IsNoetherian (MvPolynomial (σ ⊕ σ) ℝ) (MvPolynomial (σ ⊕ σ) ℝ)) fam hne
  refine ⟨s, hs, fun x y hxy => ?_⟩
  by_contra hy
  obtain ⟨p, hp, hpxy⟩ := ρ.exists_invariant_separating μ hy
  -- The difference of `p` lies in the maximal ideal.
  have hmem : doubled p ∈ Ideal.span (doubled '' (s : Set (MvPolynomial σ ℝ))) := by
    by_contra hnot
    refine hmax _ ⟨insert p s, ?_, rfl⟩ ?_
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hp
      · exact hs q hq
    · refine lt_of_le_of_ne (Ideal.span_mono ?_) ?_
      · intro q hq
        obtain ⟨r, hr, rfl⟩ := hq
        exact ⟨r, Finset.mem_insert_of_mem hr, rfl⟩
      · intro heq
        apply hnot
        rw [heq]
        exact Ideal.subset_span ⟨p, Finset.mem_insert_self p s, rfl⟩
  -- Evaluation at `(x, y)` kills the generators, hence the whole ideal.
  have hker : Ideal.span (doubled '' (s : Set (MvPolynomial σ ℝ))) ≤
      RingHom.ker (eval (Sum.elim x y)) := by
    rw [Ideal.span_le]
    rintro q ⟨r, hr, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, eval_doubled, hxy r hr, sub_self]
  have h0 := hker hmem
  rw [RingHom.mem_ker, eval_doubled, sub_eq_zero] at h0
  exact hpxy h0

end MatrixRepresentation

end Averaging

end NLQCLean
