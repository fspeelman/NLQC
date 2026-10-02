import NLQCLean.Arithmetic.EliminationIterated
import Mathlib.RingTheory.Etale.Field
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.Perfect

/-!
# The derivation `∂/∂y` on the generic field

On `L = (ℚ(y, c))^alg` there is a ring map `Λ : L → L[ε]`, `ε² = 0`, with `Λ x = x + ε D x`,
`D y = 1` and `D c = 0`. It extends `y ↦ y + ε`, `c ↦ c` from `ℚ(y, c)` by formal
étaleness of the separable algebraic extension `L / ℚ(y, c)`. For an integer polynomial `Q`
and a point `p` of `L`, `D(Q(p)) = Σᵥ (∂ᵥQ)(p) · D(pᵥ)`.
-/

namespace NLQCLean.Elimination

open MvPolynomial TrivSqZeroExt

local notation "L" => GenericField
local notation "K" => FractionRing Par
local notation "tsze" => TrivSqZeroExt

/-- The generic parameter values `y` and `c` in `L`. -/
noncomputable def genericParam (k : Fin 2) : L := algebraMap Par L (X k)

/-- `y ↦ y + ε`, `c ↦ c` on `ℤ[y, c]`. -/
noncomputable def dualParam : Par →+* tsze L L :=
  eval₂Hom (Int.castRingHom _) fun k =>
    if k = 0 then inl (genericParam 0) + inr 1 else inl (genericParam 1)

theorem fst_dualParam (a : Par) : (dualParam a).fst = algebraMap Par L a := by
  have h : (fstHom L L L).toRingHom.comp dualParam = algebraMap Par L := by
    refine MvPolynomial.ringHom_ext (fun z => ?_) (fun k => ?_)
    · simp [dualParam]
    · fin_cases k <;> simp [dualParam, genericParam]
  exact RingHom.congr_fun h a

/-- The extension of `dualParam` to `ℚ(y, c)`. -/
noncomputable def dualFrac : K →+* tsze L L :=
  IsLocalization.lift (M := nonZeroDivisors Par) (g := dualParam) fun a => by
    rw [isUnit_iff_isUnit_fst, fst_dualParam]
    exact (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ algebraMap_generic_injective).mpr
      (nonZeroDivisors.ne_zero a.2)))

theorem dualFrac_algebraMap (a : Par) : dualFrac (algebraMap Par K a) = dualParam a :=
  IsLocalization.lift_eq _ _

theorem fst_dualFrac (k : K) : (dualFrac k).fst = algebraMap K L k := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors Par) k
  have hb : algebraMap Par K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have h1 : IsLocalization.mk' K a b * algebraMap Par K b = algebraMap Par K a :=
    IsLocalization.mk'_spec _ _ _
  have h2 := congrArg (fun x => (dualFrac x).fst) h1
  simp only [map_mul, fst_mul, dualFrac_algebraMap, fst_dualParam] at h2
  have h3 := congrArg (algebraMap K L) h1
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h3
  have hbL : algebraMap Par L b ≠ 0 :=
    (map_ne_zero_iff _ algebraMap_generic_injective).mpr (nonZeroDivisors.ne_zero b.2)
  exact mul_right_cancel₀ hbL (h2.trans h3.symm)

/-- `L[ε]` with the twisted `ℚ(y, c)`-algebra structure. -/
def Twisted : Type := tsze L L

noncomputable instance : CommRing Twisted := inferInstanceAs (CommRing (tsze L L))

noncomputable instance : Algebra K Twisted := dualFrac.toAlgebra

/-- The first projection, a `ℚ(y, c)`-algebra map. -/
noncomputable def twistedFst : Twisted →ₐ[K] L where
  toRingHom := (fstHom L L L).toRingHom
  commutes' k := fst_dualFrac k

theorem twistedFst_surjective : Function.Surjective twistedFst :=
  fun x => ⟨(inl x : tsze L L), rfl⟩

theorem twistedFst_ker_nilpotent : IsNilpotent (RingHom.ker (twistedFst : Twisted →+* L)) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  rw [Ideal.mem_bot]
  change (r : tsze L L).fst = 0 at hr
  change (s : tsze L L).fst = 0 at hs
  have key : ∀ a b : tsze L L, a.fst = 0 → b.fst = 0 → a * b = 0 := by
    intro a b ha hb
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [ha]
    · simp [ha, hb]
  exact key r s hr hs

instance : Algebra.FormallySmooth K L := by
  have : Algebra.IsAlgebraic K L := AlgebraicClosure.isAlgebraic K
  have : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have := Algebra.FormallyEtale.of_isSeparable K L
  infer_instance

/-- The dual-number lift `Λ`. -/
noncomputable def dualLift : L →+* tsze L L :=
  (Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K L) twistedFst twistedFst_surjective
    twistedFst_ker_nilpotent).toRingHom

theorem fst_dualLift (x : L) : (dualLift x).fst = x :=
  Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id K L) twistedFst
    twistedFst_surjective twistedFst_ker_nilpotent x

theorem dualLift_algebraMap (a : Par) : dualLift (algebraMap Par L a) = dualParam a := by
  rw [IsScalarTower.algebraMap_apply Par K L]
  have := (Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K L) twistedFst
    twistedFst_surjective twistedFst_ker_nilpotent).commutes (algebraMap Par K a)
  change dualLift _ = _ at this
  rw [this]
  exact dualFrac_algebraMap a

/-- The derivation `D = ∂/∂y`. -/
noncomputable def genericD (x : L) : L := (dualLift x).snd

theorem dualLift_eq (x : L) : dualLift x = inl x + inr (genericD x) := by
  ext <;> simp [genericD, fst_dualLift]

theorem genericD_param_zero : genericD (genericParam 0) = 1 := by
  rw [genericD, genericParam, dualLift_algebraMap]
  simp [dualParam]

theorem genericD_param_one : genericD (genericParam 1) = 0 := by
  rw [genericD, genericParam, dualLift_algebraMap]
  simp [dualParam]

/-- Dual-number Taylor formula for integer polynomials. -/
theorem eval₂_dual {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : MvPolynomial ι ℤ)
    (p q : ι → L) :
    eval₂ (Int.castRingHom (tsze L L)) (fun v => inl (p v) + inr (q v)) Q =
      inl (eval₂ (Int.castRingHom L) p Q) +
        inr (∑ v, eval₂ (Int.castRingHom L) p (pderiv v Q) * q v) := by
  induction Q using MvPolynomial.induction_on with
  | C z =>
    rw [eval₂_C, eval₂_C]
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  | add Q R hQ hR =>
    rw [eval₂_add, hQ, hR]
    ext <;> simp [Finset.sum_add_distrib, add_mul]
  | mul_X Q v hQ =>
    rw [eval₂_mul, hQ, eval₂_X]
    ext
    · simp
    · simp only [snd_mul, fst_add, fst_inl, fst_inr, add_zero, snd_add, snd_inl, snd_inr,
        zero_add, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, eval₂_mul,
        eval₂_X, Derivation.leibniz, pderiv_X, smul_eq_mul, eval₂_add, add_mul,
        Finset.sum_add_distrib, Pi.single_apply, apply_ite (eval₂ (Int.castRingHom L) p),
        eval₂_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => by ring

/-- Chain rule for `D` on integer polynomials. -/
theorem genericD_eval₂ {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : MvPolynomial ι ℤ)
    (p : ι → L) :
    genericD (eval₂ (Int.castRingHom L) p Q) =
      ∑ v, eval₂ (Int.castRingHom L) p (pderiv v Q) * genericD (p v) := by
  have h : dualLift (eval₂ (Int.castRingHom L) p Q) =
      eval₂ (Int.castRingHom (tsze L L)) (fun v => dualLift (p v)) Q := by
    rw [MvPolynomial.eval₂_comp_left]
    congr 1
    exact RingHom.ext_int _ _
  have h2 := congrArg TrivSqZeroExt.snd h
  rw [show (fun v => dualLift (p v)) = fun v => inl (p v) + inr (genericD (p v)) from
    funext fun v => dualLift_eq (p v), eval₂_dual] at h2
  simpa [genericD] using h2

end NLQCLean.Elimination
