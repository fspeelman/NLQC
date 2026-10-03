import NLQCLean.Arithmetic.PurePowerReduction
import NLQCLean.Arithmetic.PhysicalPolynomialConstraints

/-!
# The deformed critical system of a polynomial optimization problem

The coordinates are `x : κ`, together with an unknown `y` for the objective value
(`Option κ`, with `none` for `y`). The parameters are `λ, c, s` (`Fin 3`). For a
constraint `Cst(x)` and a score `Sc(c, s, x)`:

* `Q = Cst² + (y − Sc)²` (zero set: the graph of the score over the feasible set);
* `G = Σ_u z_u²⁶`;
* `Q_λ = G − R₀ + λ Q`.

The square system
`∂_{x_i} Q_λ = 26 x_i²⁵ + λ ∂_{x_i} Q` and `26 Q_λ − Σ_i x_i ∂_{x_i} Q_λ = 26 y²⁶ + …`
is a pure-power system (`PurePower.System`) when the score and the constraint have degree
at most `12`.
-/

namespace NLQCLean.Deformation

open MvPolynomial NLQCLean.PhysicalPolynomial NLQCLean.Elimination NLQCLean.PurePower

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- Unknowns `Option κ` (`none` is `y`) and parameters `Fin 3` (`λ`, `c`, `s`). -/
abbrev Amb (κ : Type) := MvPolynomial (Option κ ⊕ Fin 3) ℤ

theorem totalDegree_pderiv_le {σ : Type*} [DecidableEq σ] (p : MvPolynomial σ ℤ) (i : σ) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  refine Finset.sup_le fun m hm => ?_
  rw [mem_support_iff, coeff_pderiv] at hm
  have hm1 : p.coeff (m + Finsupp.single i 1) ≠ 0 := left_ne_zero_of_mul hm
  have := le_totalDegree (mem_support_iff.mpr hm1)
  have h : ((m + Finsupp.single i 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
    change Finsupp.degree (m + _) = Finsupp.degree m + 1
    rw [map_add, Finsupp.degree_single]
  simp only at *
  omega

/-- The constraint in the ambient ring. -/
noncomputable def liftCst (Cst : MvPolynomial κ ℤ) : Amb κ :=
  rename (fun i => Sum.inl (some i)) Cst

/-- The score in the ambient ring, with `cos ↦ c` and `sin ↦ s`. -/
noncomputable def liftSc (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) : Amb κ :=
  rename (Sum.elim (fun j => Sum.inr j.succ) (fun i => Sum.inl (some i))) Sc

/-- `Q = Cst² + (y − Sc)²`. -/
noncomputable def Qpoly (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) : Amb κ :=
  liftCst Cst ^ 2 + (X (Sum.inl none) - liftSc Sc) ^ 2

/-- `G = Σ_u z_u²⁶`. -/
noncomputable def Gpoly : Amb κ := ∑ u : Option κ, X (Sum.inl u) ^ 26

/-- `Q_λ = G − R₀ + λ Q`. -/
noncomputable def Qlam (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) (R₀ : ℕ) :
    Amb κ :=
  Gpoly - C (R₀ : ℤ) + X (Sum.inr 0) * Qpoly Cst Sc

/-- The exponents `25` for the coordinates and `26` for `y`. -/
def ePow : Option κ → ℕ
  | some _ => 25
  | none => 26

/-- The lower-order parts. -/
noncomputable def rPoly (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) (R₀ : ℕ) :
    Option κ → Amb κ
  | some i => X (Sum.inr 0) * pderiv (Sum.inl (some i)) (Qpoly Cst Sc)
  | none => -C (26 * (R₀ : ℤ)) + X (Sum.inr 0) * (C 26 * Qpoly Cst Sc -
      ∑ i, X (Sum.inl (some i)) * pderiv (Sum.inl (some i)) (Qpoly Cst Sc))

omit [Fintype κ] [DecidableEq κ] in
theorem totalDegree_liftCst {Cst : MvPolynomial κ ℤ} (h : Cst.totalDegree ≤ 12) :
    (liftCst Cst).totalDegree ≤ 12 :=
  (totalDegree_rename_le _ _).trans h

omit [Fintype κ] [DecidableEq κ] in
theorem totalDegree_liftSc {Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ} (h : Sc.totalDegree ≤ 12) :
    (liftSc Sc).totalDegree ≤ 12 :=
  (totalDegree_rename_le _ _).trans h

omit [Fintype κ] [DecidableEq κ] in
theorem totalDegree_Qpoly {Cst : MvPolynomial κ ℤ} {Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ}
    (hC : Cst.totalDegree ≤ 12) (hS : Sc.totalDegree ≤ 12) : (Qpoly Cst Sc).totalDegree ≤ 24 := by
  unfold Qpoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_pow _ _).trans ?_
    have := totalDegree_liftCst hC
    omega
  · refine (totalDegree_pow _ _).trans ?_
    have h1 : (X (Sum.inl none) - liftSc Sc : Amb κ).totalDegree ≤ 12 :=
      (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X]; omega) (totalDegree_liftSc hS))
    omega

theorem totalDegree_rPoly {Cst : MvPolynomial κ ℤ} {Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ}
    (hC : Cst.totalDegree ≤ 12) (hS : Sc.totalDegree ≤ 12) (R₀ : ℕ) (u : Option κ) :
    (rPoly Cst Sc R₀ u).totalDegree < ePow u := by
  have hQ := totalDegree_Qpoly hC hS
  have hd : ∀ i : κ, (pderiv (Sum.inl (some i)) (Qpoly Cst Sc)).totalDegree ≤ 23 := fun i =>
    (totalDegree_pderiv_le _ _).trans (by omega)
  rcases u with _ | i
  · simp only [rPoly, ePow]
    refine Nat.lt_succ_of_le ((totalDegree_add _ _).trans (max_le (by rw [totalDegree_neg, totalDegree_C]; omega) ?_))
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    have h2 : (C 26 * Qpoly Cst Sc - ∑ i, X (Sum.inl (some i)) *
        pderiv (Sum.inl (some i)) (Qpoly Cst Sc) : Amb κ).totalDegree ≤ 24 := by
      refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
      · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)
      · refine totalDegree_finsetSum_le fun i _ => (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]
        have := hd i
        omega
    omega
  · simp only [rPoly, ePow]
    refine Nat.lt_succ_of_le ((totalDegree_mul _ _).trans ?_)
    rw [totalDegree_X]
    have := hd i
    omega

/-- The deformed critical system. -/
noncomputable def sys (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) (R₀ : ℕ)
    (hC : Cst.totalDegree ≤ 12) (hS : Sc.totalDegree ≤ 12) : System (Option κ) (Fin 3) where
  e := ePow
  a := 26
  f u := C 26 * X (Sum.inl u) ^ ePow u + rPoly Cst Sc R₀ u
  r := rPoly Cst Sc R₀
  he u := by cases u <;> simp [ePow]
  ha := by norm_num
  hf _ := rfl
  hr := totalDegree_rPoly hC hS R₀

theorem pderiv_Gpoly (i : κ) :
    pderiv (Sum.inl (some i)) (Gpoly : Amb κ) = C 26 * X (Sum.inl (some i)) ^ 25 := by
  classical
  unfold Gpoly
  rw [map_sum, Finset.sum_eq_single (some i)]
  · rw [Derivation.leibniz_pow, pderiv_X_self]
    simp only [smul_eq_mul, mul_one, nsmul_eq_mul]
    norm_num
  · intro u _ hu
    rw [Derivation.leibniz_pow, pderiv_X_of_ne (fun h => hu (Sum.inl_injective h))]
    simp
  · simp

theorem pderiv_Qlam (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) (R₀ : ℕ) (i : κ) :
    pderiv (Sum.inl (some i)) (Qlam Cst Sc R₀) =
      C 26 * X (Sum.inl (some i)) ^ 25 +
        X (Sum.inr 0) * pderiv (Sum.inl (some i)) (Qpoly Cst Sc) := by
  unfold Qlam
  rw [map_add, map_sub, pderiv_Gpoly, pderiv_C, Derivation.leibniz,
    pderiv_X_of_ne (by simp : (Sum.inr 0 : Option κ ⊕ Fin 3) ≠ Sum.inl (some i))]
  simp only [smul_eq_mul, mul_zero, add_zero, sub_zero]

theorem sys_f_some (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) (R₀ : ℕ)
    (hC : Cst.totalDegree ≤ 12) (hS : Sc.totalDegree ≤ 12) (i : κ) :
    (sys Cst Sc R₀ hC hS).f (some i) = pderiv (Sum.inl (some i)) (Qlam Cst Sc R₀) := by
  rw [pderiv_Qlam]
  rfl

theorem sys_f_none (Cst : MvPolynomial κ ℤ) (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) (R₀ : ℕ)
    (hC : Cst.totalDegree ≤ 12) (hS : Sc.totalDegree ≤ 12) :
    (sys Cst Sc R₀ hC hS).f none = C 26 * Qlam Cst Sc R₀ -
      ∑ i, X (Sum.inl (some i)) * pderiv (Sum.inl (some i)) (Qlam Cst Sc R₀) := by
  simp only [pderiv_Qlam]
  change C 26 * X (Sum.inl none) ^ 26 + rPoly Cst Sc R₀ none = _
  simp only [rPoly, Qlam, Gpoly, Fintype.sum_option]
  rw [show (C (26 * (R₀ : ℤ)) : Amb κ) = C 26 * C (R₀ : ℤ) by rw [map_mul]]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_sub]
  ring_nf

end NLQCLean.Deformation
