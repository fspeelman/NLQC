import NLQCLean.Arithmetic.EliminationGenericDerivation

/-!
# The Lagrange system of a parametrized polynomial optimization

Variables: the parameters `y, c`, the sine `σ`, the coordinates `xⱼ` and multipliers `λ_q`.
For a score `F(cos, sin, x)` and constraints `h_q(x)` the system is

* `c² + σ² - 1`,
* `h_q(x)`,
* `∂ⱼF(c, σ, x) - Σ_q λ_q ∂ⱼh_q(x)`,
* `16 - 16 y - F(c, σ, x)`.

At the generic parameter point it has no common zero: applying the derivation `∂/∂y` to
the equations forces `-16 = 0`.
-/

namespace NLQCLean.Elimination

open MvPolynomial

variable {J Q : Type*}

/-- Variables: parameters, then `σ`, the coordinates and the multipliers. -/
abbrev SysVar (J Q : Type*) := Fin 2 ⊕ (Unit ⊕ (J ⊕ Q))

/-- Equations: circle, constraints, stationarity, level. -/
abbrev SysEq (J Q : Type*) := Unit ⊕ (Q ⊕ (J ⊕ Unit))

def yV : SysVar J Q := Sum.inl 0
def cV : SysVar J Q := Sum.inl 1
def σV : SysVar J Q := Sum.inr (Sum.inl ())
def xV (j : J) : SysVar J Q := Sum.inr (Sum.inr (Sum.inl j))
def lamV (q : Q) : SysVar J Q := Sum.inr (Sum.inr (Sum.inr q))

/-- The score variables `(cos, sin, x)` inside the system variables. -/
def scoreVar : Fin 2 ⊕ J → SysVar J Q :=
  Sum.elim (fun k => if k = 0 then cV else σV) xV

noncomputable def liftF (G : MvPolynomial (Fin 2 ⊕ J) ℤ) : MvPolynomial (SysVar J Q) ℤ :=
  rename scoreVar G

noncomputable def liftH (G : MvPolynomial J ℤ) : MvPolynomial (SysVar J Q) ℤ :=
  rename (xV (Q := Q)) G

/-- The Lagrange system. -/
noncomputable def lagrangeSystem [Fintype Q] (F : MvPolynomial (Fin 2 ⊕ J) ℤ)
    (h : Q → MvPolynomial J ℤ) : SysEq J Q → MvPolynomial (SysVar J Q) ℤ
  | Sum.inl _ => X cV ^ 2 + X σV ^ 2 - 1
  | Sum.inr (Sum.inl q) => liftH (h q)
  | Sum.inr (Sum.inr (Sum.inl j)) =>
      liftF (pderiv (Sum.inr j) F) - ∑ q, X (lamV q) * liftH (pderiv j (h q))
  | Sum.inr (Sum.inr (Sum.inr _)) => 16 - 16 * X yV - liftF F

local notation "L" => GenericField

theorem genericD_add (a b : L) : genericD (a + b) = genericD a + genericD b := by
  simp [genericD, map_add]

theorem genericD_mul (a b : L) : genericD (a * b) = a * genericD b + b * genericD a := by
  simp only [genericD, map_mul, TrivSqZeroExt.snd_mul, fst_dualLift, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

theorem genericD_intCast (z : ℤ) : genericD (z : L) = 0 := by
  simp [genericD, map_intCast]

theorem genericD_sub (a b : L) : genericD (a - b) = genericD a - genericD b := by
  simp [genericD, map_sub]

theorem genericD_zero : genericD (0 : L) = 0 := by simpa using genericD_intCast 0

theorem genericParam_sq_ne_one : genericParam 1 ^ 2 ≠ 1 := by
  intro h
  have h' : algebraMap Par L (X 1 ^ 2 - 1) = 0 := by
    rw [map_sub, map_pow, map_one]; rw [genericParam] at h; rw [h, sub_self]
  rw [map_eq_zero_iff _ algebraMap_generic_injective] at h'
  have := congrArg (eval (fun _ => (0 : ℤ))) h'
  simp at this

/-- **No common zero at the generic parameter point.** -/
theorem lagrangeSystem_generic [Fintype J] [Fintype Q] [DecidableEq J]
    (F : MvPolynomial (Fin 2 ⊕ J) ℤ) (h : Q → MvPolynomial J ℤ)
    (w : Unit ⊕ (J ⊕ Q) → L) :
    ∃ i, eval₂ (Int.castRingHom L) (Sum.elim genericParam w) (lagrangeSystem F h i) ≠ 0 := by
  classical
  by_contra! hall
  set pt : SysVar J Q → L := Sum.elim genericParam w with hpt
  set c := genericParam 1
  set σ := w (Sum.inl ())
  set x : J → L := fun j => w (Sum.inr (Sum.inl j))
  set lam : Q → L := fun q => w (Sum.inr (Sum.inr q))
  set p' : Fin 2 ⊕ J → L := pt ∘ scoreVar with hp'
  have hevF : ∀ G : MvPolynomial (Fin 2 ⊕ J) ℤ,
      eval₂ (Int.castRingHom L) pt (liftF G) = eval₂ (Int.castRingHom L) p' G := fun G => by
    rw [liftF, eval₂_rename]
  have hevH : ∀ G : MvPolynomial J ℤ,
      eval₂ (Int.castRingHom L) pt (liftH (Q := Q) G) = eval₂ (Int.castRingHom L) x G :=
    fun G => by rw [liftH, eval₂_rename]; rfl
  have hp'0 : p' (Sum.inl 0) = c := rfl
  have hp'1 : p' (Sum.inl 1) = σ := rfl
  have hp'x : ∀ j, p' (Sum.inr j) = x j := fun j => rfl
  -- the circle equation
  have hcirc := hall (Sum.inl ())
  simp only [lagrangeSystem, eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at hcirc
  change c ^ 2 + σ ^ 2 - 1 = 0 at hcirc
  have hσ0 : σ ≠ 0 := by
    rintro hσ
    rw [hσ] at hcirc
    exact genericParam_sq_ne_one (by linear_combination hcirc)
  have hDc : genericD c = 0 := genericD_param_one
  have hDσ : genericD σ = 0 := by
    have hD := congrArg genericD hcirc
    rw [genericD_sub, genericD_add, pow_two, pow_two, genericD_mul, genericD_mul, hDc,
      show genericD (1 : L) = 0 by simpa using genericD_intCast 1, genericD_zero] at hD
    have : 2 * σ * genericD σ = 0 := by linear_combination hD
    rcases mul_eq_zero.mp this with h2 | h2
    · exact absurd (mul_eq_zero.mp h2) (by simp [hσ0])
    · exact h2
  -- derivative of the score along the generic point
  have hDF : ∀ G : MvPolynomial (Fin 2 ⊕ J) ℤ,
      genericD (eval₂ (Int.castRingHom L) p' G) =
        ∑ j, eval₂ (Int.castRingHom L) p' (pderiv (Sum.inr j) G) * genericD (x j) := by
    intro G
    rw [genericD_eval₂, Fintype.sum_sum_type, Fin.sum_univ_two, hp'0, hp'1, hDc, hDσ]
    simp [hp'x]
  have hDH : ∀ q, ∑ j, eval₂ (Int.castRingHom L) x (pderiv j (h q)) * genericD (x j) = 0 := by
    intro q
    have hq := hall (Sum.inr (Sum.inl q))
    change eval₂ (Int.castRingHom L) pt (liftH (h q)) = 0 at hq
    rw [hevH] at hq
    rw [← genericD_eval₂, hq]
    simpa using genericD_intCast 0
  have hstat : ∀ j, eval₂ (Int.castRingHom L) p' (pderiv (Sum.inr j) F) =
      ∑ q, lam q * eval₂ (Int.castRingHom L) x (pderiv j (h q)) := by
    intro j
    have hj := hall (Sum.inr (Sum.inr (Sum.inl j)))
    simp only [lagrangeSystem, eval₂_sub, eval₂_sum, eval₂_mul, eval₂_X, hevF,
      hevH] at hj
    rw [sub_eq_zero] at hj
    exact hj
  have hlevel := hall (Sum.inr (Sum.inr (Sum.inr ())))
  simp only [lagrangeSystem, eval₂_sub, eval₂_mul, eval₂_X, hevF] at hlevel
  have hD := congrArg genericD hlevel
  rw [genericD_sub, genericD_sub, genericD_mul, hDF] at hD
  have hy : genericD (pt yV) = 1 := genericD_param_zero
  have hsum : ∑ j, eval₂ (Int.castRingHom L) p' (pderiv (Sum.inr j) F) * genericD (x j) = 0 := by
    calc ∑ j, eval₂ (Int.castRingHom L) p' (pderiv (Sum.inr j) F) * genericD (x j)
        = ∑ j, (∑ q, lam q * eval₂ (Int.castRingHom L) x (pderiv j (h q))) * genericD (x j) :=
          Finset.sum_congr rfl fun j _ => by rw [hstat j]
      _ = ∑ q, ∑ j, lam q * eval₂ (Int.castRingHom L) x (pderiv j (h q)) * genericD (x j) := by
          simp only [Finset.sum_mul]
          exact Finset.sum_comm
      _ = 0 := by
          refine Finset.sum_eq_zero fun q _ => ?_
          calc ∑ j, lam q * eval₂ (Int.castRingHom L) x (pderiv j (h q)) * genericD (x j)
              = lam q * ∑ j, eval₂ (Int.castRingHom L) x (pderiv j (h q)) * genericD (x j) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ = 0 := by rw [hDH q, mul_zero]
  have h16' : (16 : L) = 0 := by
    have e1 : eval₂ (Int.castRingHom L) pt (16 : MvPolynomial (SysVar J Q) ℤ) = 16 :=
      map_ofNat (eval₂Hom (Int.castRingHom L) pt) 16
    rw [e1, hy, hsum] at hD
    have e2 : genericD (16 : L) = 0 := by simpa using genericD_intCast 16
    rw [e2, genericD_zero] at hD
    linear_combination -hD
  norm_num at h16'


theorem SizeLE.natCast {σ : Type*} (k : ℕ) : SizeLE (k : MvPolynomial σ ℤ) 0 k := by
  have h := PhysicalPolynomial.CoefficientMassLE.constant (σ := σ) (k : ℤ)
  rw [map_natCast, Int.natAbs_natCast] at h
  refine ⟨?_, h⟩
  rw [← map_natCast (C : ℤ →+* MvPolynomial σ ℤ)]
  exact (totalDegree_C _).le

theorem SizeLE.sub {σ : Type*} {p q : MvPolynomial σ ℤ} {d M N : ℕ} (hp : SizeLE p d M)
    (hq : SizeLE q d N) : SizeLE (p - q) d (M + N) := by
  rw [sub_eq_add_neg]; exact hp.add hq.neg

/-- Size of the Lagrange system. -/
theorem lagrangeSystem_size [Fintype J] [Fintype Q] [DecidableEq J]
    (F : MvPolynomial (Fin 2 ⊕ J) ℤ) (h : Q → MvPolynomial J ℤ) {MF Mh : ℕ}
    (hF : SizeLE F 12 MF) (hh : ∀ q, SizeLE (h q) 2 Mh) (e : SysEq J Q) :
    SizeLE (lagrangeSystem F h e) 12 (13 * MF + 4 * Fintype.card Q * Mh + 32) := by
  classical
  rcases e with _ | q | j | _
  · have hX : ∀ v : SysVar J Q, SizeLE ((X v : MvPolynomial (SysVar J Q) ℤ) ^ 2) 2 1 :=
      fun v => by simpa using (SizeLE.X v).pow 2
    have := ((hX cV).add (hX σV)).sub (SizeLE.one.mono (by norm_num) le_rfl)
    exact this.mono (by norm_num) (by omega)
  · have hQ : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q⟩
    refine ((hh q).rename _).mono (by norm_num) ?_
    nlinarith
  · have h1 : SizeLE (liftF (Q := Q) (pderiv (Sum.inr j) F)) 12 (12 * MF) :=
      (hF.pderiv (Sum.inr j)).rename _
    have hterm : ∀ q : Q, SizeLE (X (lamV q) * liftH (Q := Q) (pderiv j (h q))) 12 (2 * Mh) :=
      fun q => by
        have := (SizeLE.X (lamV q : SysVar J Q)).mul (((hh q).pderiv j).rename (xV (Q := Q)))
        exact this.mono (by norm_num) (by omega)
    have h2 := SizeLE.finsetSum Finset.univ _ (fun q _ => hterm q)
    rw [Finset.card_univ] at h2
    exact (h1.sub h2).mono le_rfl (by nlinarith)
  · have h16 : SizeLE (16 : MvPolynomial (SysVar J Q) ℤ) 12 16 :=
      (SizeLE.natCast (σ := SysVar J Q) 16).mono (by norm_num) le_rfl
    have hy : SizeLE (16 * X yV : MvPolynomial (SysVar J Q) ℤ) 12 16 :=
      ((SizeLE.natCast (σ := SysVar J Q) 16).mul (SizeLE.X yV)).mono (by norm_num) (by norm_num)
    have hFl : SizeLE (liftF (Q := Q) F) 12 MF := hF.rename _
    exact ((h16.sub hy).sub hFl).mono le_rfl (by omega)

end NLQCLean.Elimination
