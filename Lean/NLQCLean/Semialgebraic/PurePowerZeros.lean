import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Set.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Common zeros of pure-power polynomial systems

If `b₁, …, b_N ∈ ℝ[x₁, …, x_N]` have the form `bᵢ = aᵢ xᵢ^e + hᵢ` with `aᵢ ≠ 0`
and `deg hᵢ < e`, then the system has at most `e^N` common real zeros.

On the common zero set `xᵢ^e = -hᵢ/aᵢ`, so every polynomial agrees there with a
polynomial supported in the box `{α | ∀ i, α i < e}` (strong induction on the
total degree). A multivariate Lagrange basis shows that evaluation on any finite
set of points is surjective, so the box monomials span a space of dimension at
least the number of points. No multiplicity, nondegeneracy or complex zeros are
involved.
-/

namespace NLQCLean.PurePowerZeros

open MvPolynomial Module

variable {N : ℕ}

/-- The common real zeros of a family of polynomials. -/
def commonZeros (b : Fin N → MvPolynomial (Fin N) ℝ) : Set (Fin N → ℝ) :=
  {z | ∀ i, eval z (b i) = 0}

/-- A polynomial whose monomials all have every exponent below `e`. -/
def BoxSupported (e : ℕ) (r : MvPolynomial (Fin N) ℝ) : Prop :=
  ∀ α ∈ r.support, ∀ i, α i < e

/-- The pure-power hypothesis: `bᵢ = aᵢ xᵢ^e + hᵢ` with `aᵢ ≠ 0`, `deg hᵢ < e`. -/
def PurePowerSystem (e : ℕ) (b : Fin N → MvPolynomial (Fin N) ℝ) : Prop :=
  ∀ i, ∃ a : ℝ, a ≠ 0 ∧ ∃ h : MvPolynomial (Fin N) ℝ,
    b i = C a * X i ^ e + h ∧ h.totalDegree < e

theorem boxSupported_zero (e : ℕ) : BoxSupported e (0 : MvPolynomial (Fin N) ℝ) := by
  simp [BoxSupported]

theorem BoxSupported.add {e : ℕ} {r s : MvPolynomial (Fin N) ℝ} (hr : BoxSupported e r)
    (hs : BoxSupported e s) : BoxSupported e (r + s) := by
  classical
  intro α hα i
  rcases Finset.mem_union.mp (support_add hα) with h | h
  · exact hr α h i
  · exact hs α h i

theorem BoxSupported.smul {e : ℕ} {r : MvPolynomial (Fin N) ℝ} (hr : BoxSupported e r)
    (c : ℝ) : BoxSupported e (c • r) :=
  fun α hα i => hr α (support_smul hα) i

theorem boxSupported_monomial {e : ℕ} {α : Fin N →₀ ℕ} (hα : ∀ i, α i < e) (c : ℝ) :
    BoxSupported e (monomial α c) := by
  classical
  intro β hβ i
  rw [support_monomial] at hβ
  split_ifs at hβ
  · simp at hβ
  · rw [Finset.mem_singleton.mp hβ]
    exact hα i

/-- Agreement with a box-supported polynomial on a set. -/
def BoxReducible (e : ℕ) (Z : Set (Fin N → ℝ)) (f : MvPolynomial (Fin N) ℝ) : Prop :=
  ∃ r, BoxSupported e r ∧ ∀ z ∈ Z, eval z f = eval z r

theorem BoxReducible.add {e : ℕ} {Z : Set (Fin N → ℝ)} {f g : MvPolynomial (Fin N) ℝ}
    (hf : BoxReducible e Z f) (hg : BoxReducible e Z g) : BoxReducible e Z (f + g) := by
  obtain ⟨r, hr, hfr⟩ := hf
  obtain ⟨s, hs, hgs⟩ := hg
  exact ⟨r + s, hr.add hs, fun z hz => by simp [hfr z hz, hgs z hz]⟩

theorem BoxReducible.smul {e : ℕ} {Z : Set (Fin N → ℝ)} {f : MvPolynomial (Fin N) ℝ}
    (hf : BoxReducible e Z f) (c : ℝ) : BoxReducible e Z (c • f) := by
  obtain ⟨r, hr, hfr⟩ := hf
  exact ⟨c • r, hr.smul c, fun z hz => by simp [hfr z hz]⟩

theorem boxReducible_sum {e : ℕ} {Z : Set (Fin N → ℝ)} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin N) ℝ) (hf : ∀ i ∈ s, BoxReducible e Z (f i)) :
    BoxReducible e Z (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, boxSupported_zero e, fun z _ => by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The total degree of a monomial with nonzero coefficient is its degree. -/
theorem totalDegree_monomial_one (α : Fin N →₀ ℕ) :
    (monomial α (1 : ℝ)).totalDegree = α.sum fun _ e => e :=
  totalDegree_monomial α one_ne_zero

/-- **Box reduction.** On the common zeros of a pure-power system every
polynomial agrees with a box-supported polynomial. -/
theorem boxReducible_of_purePower {e : ℕ} {b : Fin N → MvPolynomial (Fin N) ℝ}
    (hb : PurePowerSystem e b) (f : MvPolynomial (Fin N) ℝ) :
    BoxReducible e (commonZeros b) f := by
  classical
  -- Strong induction on the total degree.
  suffices H : ∀ d, ∀ f : MvPolynomial (Fin N) ℝ, f.totalDegree ≤ d →
      BoxReducible e (commonZeros b) f from H _ f le_rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro f hf
  rw [f.as_sum]
  refine boxReducible_sum _ _ fun α hα => ?_
  have hαd : (α.sum fun _ e => e) ≤ d :=
    (le_totalDegree hα).trans hf
  -- Reduce one monomial.
  rw [show monomial α (f.coeff α) = f.coeff α • monomial α (1 : ℝ) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  refine BoxReducible.smul ?_ _
  by_cases hbox : ∀ i, α i < e
  · exact ⟨monomial α 1, boxSupported_monomial hbox 1, fun _ _ => rfl⟩
  push Not at hbox
  obtain ⟨i, hi⟩ := hbox
  obtain ⟨a, ha, h, hbi, hh⟩ := hb i
  set β := α - Finsupp.single i e with hβ
  have hαβ : α = β + Finsupp.single i e :=
    (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)).symm
  have hdeg : (α.sum fun _ e => e) = (β.sum fun _ e => e) + e := by
    rw [hαβ, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl]
  -- On the zero set, `xᵢ^e = -hᵢ/aᵢ`.
  set g : MvPolynomial (Fin N) ℝ := C (-a⁻¹) * (monomial β 1 * h) with hg
  have hgdeg : g.totalDegree < α.sum fun _ e => e := by
    calc g.totalDegree ≤ (C (-a⁻¹)).totalDegree + (monomial β 1 * h).totalDegree :=
          totalDegree_mul _ _
      _ ≤ 0 + ((monomial β (1 : ℝ)).totalDegree + h.totalDegree) := by
          rw [totalDegree_C]
          exact Nat.add_le_add_left (totalDegree_mul _ _) 0
      _ < α.sum fun _ e => e := by
          rw [totalDegree_monomial_one, hdeg, zero_add]
          omega
  obtain ⟨r, hr, hgr⟩ := ih _ (lt_of_lt_of_le hgdeg hαd) g le_rfl
  refine ⟨r, hr, fun z hz => ?_⟩
  rw [← hgr z hz, hαβ, monomial_add_single, hg]
  have hzi : eval z (b i) = 0 := hz i
  rw [hbi] at hzi
  simp only [map_add, map_mul, eval_C, map_pow, eval_X] at hzi
  simp only [map_mul, eval_C, map_pow, eval_X]
  have : z i ^ e = -a⁻¹ * eval z h := by
    field_simp
    linarith
  rw [this]
  ring

/-- **Multivariate Lagrange basis.** For a finite set of points and a member
`z`, a polynomial equal to `1` at `z` and `0` at the other points. -/
theorem exists_mvLagrange (Z : Finset (Fin N → ℝ)) (z : Fin N → ℝ) :
    ∃ L : MvPolynomial (Fin N) ℝ, ∀ w ∈ Z, eval w L = if w = z then 1 else 0 := by
  classical
  have hsep : ∀ w : Fin N → ℝ, w ≠ z → ∃ j, w j ≠ z j := fun w hw => by
    by_contra h
    push Not at h
    exact hw (funext h)
  -- The separating linear factor for `w ≠ z`, equal to `1` at `z` and `0` at `w`.
  let ℓ : (Fin N → ℝ) → MvPolynomial (Fin N) ℝ := fun w =>
    if hw : w ≠ z then
      C (z (hsep w hw).choose - w (hsep w hw).choose)⁻¹ *
        (X (hsep w hw).choose - C (w (hsep w hw).choose))
    else 1
  refine ⟨∏ w ∈ Z.erase z, ℓ w, fun w hw => ?_⟩
  rw [eval_prod]
  split_ifs with hwz
  · subst hwz
    refine Finset.prod_eq_one fun u hu => ?_
    have hu' : u ≠ w := Finset.ne_of_mem_erase hu
    have hj := (hsep u hu').choose_spec
    simp only [ℓ, dite_eq_left hu', map_mul, eval_C, map_sub, eval_X]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hj))
  · refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hwz, hw⟩) ?_
    simp [ℓ, hwz]

/-- The finite set of box exponents `{α | ∀ i, α i < e}`. -/
noncomputable def boxExponents (N e : ℕ) : Finset (Fin N →₀ ℕ) :=
  Finset.univ.image fun κ : Fin N → Fin e => Finsupp.equivFunOnFinite.symm fun i => (κ i : ℕ)

theorem card_boxExponents_le (N e : ℕ) : (boxExponents N e).card ≤ e ^ N := by
  classical
  unfold boxExponents
  refine Finset.card_image_le.trans ?_
  simp

theorem mem_boxExponents {e : ℕ} {α : Fin N →₀ ℕ} (hα : ∀ i, α i < e) :
    α ∈ boxExponents N e := by
  classical
  refine Finset.mem_image.mpr ⟨fun i => ⟨α i, hα i⟩, Finset.mem_univ _, ?_⟩
  ext i
  simp

/-- **Point count.** Every finite set of common zeros of a pure-power system has
at most `e^N` points. -/
theorem card_le_of_subset_commonZeros {e : ℕ} {b : Fin N → MvPolynomial (Fin N) ℝ}
    (hb : PurePowerSystem e b) (T : Finset (Fin N → ℝ)) (hT : ↑T ⊆ commonZeros b) :
    T.card ≤ e ^ N := by
  classical
  -- Evaluation on `T`.
  let ev : MvPolynomial (Fin N) ℝ →ₗ[ℝ] (T → ℝ) :=
    { toFun := fun f t => eval (t : Fin N → ℝ) f
      map_add' := fun f g => by ext t; simp
      map_smul' := fun c f => by ext t; simp }
  let S : Finset (T → ℝ) := (boxExponents N e).image fun α => ev (monomial α 1)
  have hspan : Submodule.span ℝ (S : Set (T → ℝ)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    -- `y` is the evaluation of a Lagrange combination, hence of a box polynomial.
    have hL : ∀ t : T, ∃ L : MvPolynomial (Fin N) ℝ,
        ∀ w ∈ T, eval w L = if w = (t : Fin N → ℝ) then 1 else 0 :=
      fun t => exists_mvLagrange T t
    choose L hL using hL
    let f : MvPolynomial (Fin N) ℝ := ∑ t : T, y t • L t
    have hfy : ev f = y := by
      ext s
      change eval (s : Fin N → ℝ) f = y s
      simp only [f, map_sum, smul_eval]
      rw [Finset.sum_eq_single s]
      · rw [hL s s s.2, ite_eq_left rfl, mul_one]
      · intro t _ hts
        rw [hL t s s.2, ite_eq_right (fun h => hts (Subtype.ext h).symm), mul_zero]
      · simp
    obtain ⟨r, hr, hfr⟩ := boxReducible_of_purePower hb f
    have hevr : ev r = y := by
      rw [← hfy]
      ext s
      exact (hfr s (hT s.2)).symm
    rw [← hevr, r.as_sum, map_sum]
    refine Submodule.sum_mem _ fun α hα => ?_
    rw [show monomial α (r.coeff α) = r.coeff α • monomial α (1 : ℝ) by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨α, mem_boxExponents (hr α hα), rfl⟩)
  have hrank : finrank ℝ (T → ℝ) ≤ S.card := by
    have h := finrank_span_le_card (R := ℝ) (S : Set (T → ℝ))
    rw [hspan, finrank_top, Finset.toFinset_coe] at h
    exact h
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrank
  exact hrank.trans (Finset.card_image_le.trans (card_boxExponents_le N e))

/-- **Common zeros of a pure-power system.** They are finitely many, at most
`e^N`. -/
theorem commonZeros_finite_ncard_le {e : ℕ} {b : Fin N → MvPolynomial (Fin N) ℝ}
    (hb : PurePowerSystem e b) :
    (commonZeros b).Finite ∧ (commonZeros b).ncard ≤ e ^ N := by
  have hfin : (commonZeros b).Finite := by
    by_contra hinf
    obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (e ^ N + 1)
    have := card_le_of_subset_commonZeros hb T hT
    omega
  refine ⟨hfin, ?_⟩
  obtain ⟨T, hT⟩ := hfin.exists_finset_coe
  rw [← hT, Set.ncard_coe_finset]
  exact card_le_of_subset_commonZeros hb T hT.le

end NLQCLean.PurePowerZeros
