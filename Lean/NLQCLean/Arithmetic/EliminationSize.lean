module

public import NLQCLean.Arithmetic.PhysicalPolynomialHeight
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# Degree and coefficient-mass bookkeeping

`SizeLE p d M` bounds the total degree of an integer polynomial by `d` and its coefficient
mass by `M` (`CoefficientMassLE`). The bounds are transported through sums, products,
powers, partial derivatives, substitution, renaming, determinants and coefficient
extraction in one variable.
-/

namespace NLQCLean.Elimination

open MvPolynomial NLQCLean.PhysicalPolynomial

/-- Joint degree and coefficient-mass bound. -/
def SizeLE {σ : Type*} (p : MvPolynomial σ ℤ) (d M : ℕ) : Prop :=
  p.totalDegree ≤ d ∧ CoefficientMassLE p M

theorem SizeLE.mono {σ : Type*} {p : MvPolynomial σ ℤ} {d M d' M' : ℕ} (h : SizeLE p d M)
    (hd : d ≤ d') (hM : M ≤ M') : SizeLE p d' M' :=
  ⟨h.1.trans hd, h.2.mono hM⟩

/-! ### Coefficient-mass certificates -/

theorem CoefficientMassLE.exists_support_subset {σ : Type*} {p : MvPolynomial σ ℤ} {H : ℕ}
    (hp : CoefficientMassLE p H) :
    ∃ q : MvPolynomial σ ℕ, NaturalMajorizes p q ∧ naturalCoefficientMass q ≤ H ∧
      q.support ⊆ p.support := by
  classical
  obtain ⟨r, hr, hrm⟩ := hp
  refine ⟨∑ m ∈ p.support, monomial m (r.coeff m), ?_, ?_, ?_⟩
  · intro m
    rw [coeff_sum]
    by_cases hm : m ∈ p.support
    · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, ite_eq_right hb])
        (fun h => absurd hm h), coeff_monomial, ite_eq_left rfl]
      exact hr m
    · rw [notMem_support_iff.mp hm]
      simp
  · rw [map_sum]
    calc ∑ m ∈ p.support, naturalCoefficientMass (monomial m (r.coeff m))
        = ∑ m ∈ p.support, r.coeff m := by
          refine Finset.sum_congr rfl fun m _ => ?_
          simp [naturalCoefficientMass, eval_monomial]
      _ ≤ ∑ m ∈ r.support, r.coeff m :=
          Finset.sum_le_sum_of_subset_of_nonneg (hr.support_subset) (fun _ _ _ => Nat.zero_le _)
      _ = naturalCoefficientMass r := (naturalCoefficientMass_eq_sum r).symm
      _ ≤ H := hrm
  · intro m hm
    rw [mem_support_iff, coeff_sum] at hm
    by_contra hmp
    refine hm (Finset.sum_eq_zero fun b hb => ?_)
    rw [coeff_monomial]
    split_ifs with h
    · exact absurd (h ▸ hb) hmp
    · rfl

/-- Coefficient mass passes to a polynomial whose coefficients are those of `p` along an
injective map of exponents. -/
theorem CoefficientMassLE.of_coeff_injective {σ τ : Type*} {p : MvPolynomial σ ℤ}
    {q : MvPolynomial τ ℤ} {H : ℕ} (ι : (τ →₀ ℕ) → (σ →₀ ℕ)) (hι : Function.Injective ι)
    (hq : ∀ d, q.coeff d = p.coeff (ι d)) (hp : CoefficientMassLE p H) :
    CoefficientMassLE q H := by
  classical
  obtain ⟨r, hr, hrm⟩ := hp
  refine ⟨∑ d ∈ q.support, monomial d (r.coeff (ι d)), ?_, ?_⟩
  · intro d
    rw [coeff_sum]
    by_cases hd : d ∈ q.support
    · rw [Finset.sum_eq_single d (fun b _ hb => by rw [coeff_monomial, ite_eq_right hb])
        (fun h => absurd hd h), coeff_monomial, ite_eq_left rfl, hq]
      exact hr _
    · rw [notMem_support_iff.mp hd]
      simp
  · rw [map_sum]
    have himg : q.support.image ι ⊆ r.support := by
      intro m hm
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
      rw [mem_support_iff, hq] at hd
      exact hr.support_subset (mem_support_iff.mpr hd)
    calc ∑ d ∈ q.support, naturalCoefficientMass (monomial d (r.coeff (ι d)))
        = ∑ d ∈ q.support, r.coeff (ι d) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          simp [naturalCoefficientMass, eval_monomial]
      _ = ∑ m ∈ q.support.image ι, r.coeff m :=
          (Finset.sum_image fun a _ b _ h => hι h).symm
      _ ≤ ∑ m ∈ r.support, r.coeff m :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => Nat.zero_le _)
      _ = naturalCoefficientMass r := (naturalCoefficientMass_eq_sum r).symm
      _ ≤ H := hrm

/-- Coefficient mass passes, multiplied by `c`, to a polynomial whose coefficients are
bounded by `c` times those of `p` along an injective map of exponents. -/
theorem CoefficientMassLE.of_coeff_injective_mul {σ τ : Type*} {p : MvPolynomial σ ℤ}
    {q : MvPolynomial τ ℤ} {H : ℕ} (c : ℕ) (ι : (τ →₀ ℕ) → (σ →₀ ℕ))
    (hι : Function.Injective ι)
    (hq : ∀ d, (q.coeff d).natAbs ≤ c * (p.coeff (ι d)).natAbs) (hp : CoefficientMassLE p H) :
    CoefficientMassLE q (c * H) := by
  classical
  obtain ⟨r, hr, hrm⟩ := hp
  refine ⟨∑ d ∈ q.support, monomial d (c * r.coeff (ι d)), ?_, ?_⟩
  · intro d
    rw [coeff_sum]
    by_cases hd : d ∈ q.support
    · rw [Finset.sum_eq_single d (fun b _ hb => by rw [coeff_monomial, ite_eq_right hb])
        (fun h => absurd hd h), coeff_monomial, ite_eq_left rfl]
      exact (hq d).trans (Nat.mul_le_mul_left _ (hr _))
    · rw [notMem_support_iff.mp hd]
      simp
  · rw [map_sum]
    have himg : q.support.image ι ⊆ r.support := by
      intro m hm
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
      refine hr.support_subset (mem_support_iff.mpr fun h0 => (mem_support_iff.mp hd) ?_)
      have := hq d
      rw [h0] at this
      simpa using this
    calc ∑ d ∈ q.support, naturalCoefficientMass (monomial d (c * r.coeff (ι d)))
        = c * ∑ d ∈ q.support, r.coeff (ι d) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          simp [naturalCoefficientMass, eval_monomial]
      _ = c * ∑ m ∈ q.support.image ι, r.coeff m := by
          rw [Finset.sum_image fun a _ b _ h => hι h]
      _ ≤ c * ∑ m ∈ r.support, r.coeff m :=
          Nat.mul_le_mul_left _
            (Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => Nat.zero_le _))
      _ = c * naturalCoefficientMass r := by rw [naturalCoefficientMass_eq_sum r]
      _ ≤ c * H := Nat.mul_le_mul_left _ hrm

/-- Partial derivatives multiply the mass by at most the degree. -/
theorem SizeLE.pderiv {σ : Type*} [DecidableEq σ] {p : MvPolynomial σ ℤ} {d M : ℕ}
    (hp : SizeLE p d M) (i : σ) : SizeLE (MvPolynomial.pderiv i p) d (d * M) := by
  classical
  have hdeg_succ : ∀ m : σ →₀ ℕ, ((m + Finsupp.single i 1).sum fun _ e => e) =
      (m.sum fun _ e => e) + 1 := fun m => by
    change Finsupp.degree (m + Finsupp.single i 1) = Finsupp.degree m + 1
    rw [map_add, Finsupp.degree_single]
  have hsupp : ∀ m, (MvPolynomial.pderiv i p).coeff m ≠ 0 →
      (m.sum fun _ e => e) + 1 ≤ d ∧ m i + 1 ≤ d := by
    intro m hm
    rw [coeff_pderiv] at hm
    have hm1 : p.coeff (m + Finsupp.single i 1) ≠ 0 := left_ne_zero_of_mul hm
    have hdeg := (le_totalDegree (mem_support_iff.mpr hm1)).trans hp.1
    rw [hdeg_succ] at hdeg
    have hmi : m i ≤ m.sum fun _ e => e := Finsupp.le_degree i m
    omega
  refine ⟨?_, ?_⟩
  · refine Finset.sup_le fun m hm => ?_
    have := (hsupp m (mem_support_iff.mp hm)).1
    omega
  · refine CoefficientMassLE.of_coeff_injective_mul d (fun m => m + Finsupp.single i 1)
      (add_left_injective _) (fun m => ?_) hp.2
    by_cases hm : (MvPolynomial.pderiv i p).coeff m = 0
    · rw [hm]; simp
    · have hmi := (hsupp m hm).2
      rw [coeff_pderiv, Int.natAbs_mul, mul_comm]
      refine Nat.mul_le_mul_right _ ?_
      have : ((m i : ℤ) + 1).natAbs = m i + 1 := by omega
      rw [this]
      exact hmi

/-- Substitution of polynomials of mass at most `B ≥ 1` into a polynomial of degree at most
`d` multiplies the mass by at most `B ^ d`. -/
theorem CoefficientMassLE.bind₁_le {σ τ : Type*} {p : MvPolynomial σ ℤ} {H d B : ℕ}
    (hp : CoefficientMassLE p H) (hd : p.totalDegree ≤ d) (f : σ → MvPolynomial τ ℤ)
    (hB : 1 ≤ B) (hf : ∀ i, CoefficientMassLE (f i) B) :
    CoefficientMassLE (MvPolynomial.bind₁ f p) (H * B ^ d) := by
  classical
  obtain ⟨q, hq, hqm, hqs⟩ := CoefficientMassLE.exists_support_subset hp
  choose g hfg hgm using hf
  refine ⟨MvPolynomial.bind₁ g q, hq.bind₁ f g hfg, ?_⟩
  change eval₂Hom (RingHom.id ℕ) (fun _ : τ => 1) (MvPolynomial.bind₁ g q) ≤ _
  rw [eval₂Hom_bind₁]
  change MvPolynomial.eval (fun i => naturalCoefficientMass (g i)) q ≤ _
  rw [MvPolynomial.eval_eq]
  calc ∑ m ∈ q.support, q.coeff m * ∏ i ∈ m.support, naturalCoefficientMass (g i) ^ m i
      ≤ ∑ m ∈ q.support, q.coeff m * B ^ d := by
        refine Finset.sum_le_sum fun m hm => Nat.mul_le_mul_left _ ?_
        calc ∏ i ∈ m.support, naturalCoefficientMass (g i) ^ m i
            ≤ ∏ i ∈ m.support, B ^ m i :=
              Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
                (fun i _ => Nat.pow_le_pow_left (hgm i) _)
          _ = B ^ (m.sum fun _ e => e) := by
              rw [Finset.prod_pow_eq_pow_sum]; rfl
          _ ≤ B ^ d := Nat.pow_le_pow_right hB ((le_totalDegree (hqs hm)).trans hd)
    _ = (∑ m ∈ q.support, q.coeff m) * B ^ d := by rw [Finset.sum_mul]
    _ ≤ H * B ^ d := by
        rw [← naturalCoefficientMass_eq_sum]
        exact Nat.mul_le_mul_right _ hqm

theorem SizeLE.rename {σ τ : Type*} {p : MvPolynomial σ ℤ} {d M : ℕ} (h : SizeLE p d M)
    (f : σ → τ) : SizeLE (MvPolynomial.rename f p) d M := by
  refine ⟨(totalDegree_rename_le f p).trans h.1, ?_⟩
  have : MvPolynomial.rename f p = MvPolynomial.bind₁ (fun i => X (f i)) p := by
    rw [show (fun i => (X (f i) : MvPolynomial τ ℤ)) = X ∘ f from rfl, ← bind₁_rename,
      bind₁_X_left, AlgHom.id_apply]
  rw [this]
  exact h.2.bind₁ _ fun i => CoefficientMassLE.variablePolynomial _


theorem SizeLE.zero {σ : Type*} (d M : ℕ) : SizeLE (0 : MvPolynomial σ ℤ) d M :=
  ⟨by simp, CoefficientMassLE.zero M⟩

theorem SizeLE.add {σ : Type*} {p q : MvPolynomial σ ℤ} {d M N : ℕ} (hp : SizeLE p d M)
    (hq : SizeLE q d N) : SizeLE (p + q) d (M + N) :=
  ⟨(totalDegree_add p q).trans (max_le hp.1 hq.1), hp.2.add hq.2⟩

theorem SizeLE.neg {σ : Type*} {p : MvPolynomial σ ℤ} {d M : ℕ} (hp : SizeLE p d M) :
    SizeLE (-p) d M :=
  ⟨by rw [totalDegree_neg]; exact hp.1, hp.2.neg⟩

theorem SizeLE.mul {σ : Type*} {p q : MvPolynomial σ ℤ} {d e M N : ℕ} (hp : SizeLE p d M)
    (hq : SizeLE q e N) : SizeLE (p * q) (d + e) (M * N) :=
  ⟨(totalDegree_mul p q).trans (add_le_add hp.1 hq.1), hp.2.mul hq.2⟩

theorem SizeLE.one {σ : Type*} : SizeLE (1 : MvPolynomial σ ℤ) 0 1 :=
  ⟨by simp, CoefficientMassLE.one⟩

theorem SizeLE.X {σ : Type*} (i : σ) : SizeLE (X i : MvPolynomial σ ℤ) 1 1 :=
  ⟨by simp [totalDegree_X], CoefficientMassLE.variablePolynomial i⟩

theorem SizeLE.pow {σ : Type*} {p : MvPolynomial σ ℤ} {d M : ℕ} (hp : SizeLE p d M) (k : ℕ) :
    SizeLE (p ^ k) (k * d) (M ^ k) := by
  induction k with
  | zero => simpa using (SizeLE.one (σ := σ))
  | succ k ih => simpa [pow_succ, Nat.succ_mul] using ih.mul hp

theorem SizeLE.finsetProd {σ ι : Type*} (t : Finset ι) (p : ι → MvPolynomial σ ℤ) {d M : ℕ}
    (hp : ∀ i ∈ t, SizeLE (p i) d M) : SizeLE (∏ i ∈ t, p i) (t.card * d) (M ^ t.card) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (SizeLE.one (σ := σ))
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h := (hp a (Finset.mem_insert_self a t)).mul
      (ih fun i hi => hp i (Finset.mem_insert_of_mem hi))
    refine h.mono (by rw [Nat.succ_mul]; omega) (by rw [pow_succ]; exact le_of_eq (mul_comm _ _))

theorem SizeLE.finsetSum {σ ι : Type*} (t : Finset ι) (p : ι → MvPolynomial σ ℤ) {d M : ℕ}
    (hp : ∀ i ∈ t, SizeLE (p i) d M) : SizeLE (∑ i ∈ t, p i) d (t.card * M) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (SizeLE.zero (σ := σ) d 0)
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Nat.succ_mul, add_comm _ M]
    exact (hp a (Finset.mem_insert_self a t)).add
      (ih fun i hi => hp i (Finset.mem_insert_of_mem hi))

/-- Leibniz bound for a determinant. -/
theorem SizeLE.det {σ : Type*} {N d B : ℕ} (A : Matrix (Fin N) (Fin N) (MvPolynomial σ ℤ))
    (hA : ∀ i j, SizeLE (A i j) d B) : SizeLE A.det (N * d) (N.factorial * B ^ N) := by
  classical
  rw [Matrix.det_apply]
  have hterm : ∀ τ : Equiv.Perm (Fin N),
      SizeLE (Equiv.Perm.sign τ • ∏ i, A (τ i) i) (N * d) (B ^ N) := by
    intro τ
    have hprod := SizeLE.finsetProd Finset.univ (fun i => A (τ i) i) (fun i _ => hA (τ i) i)
    rw [Finset.card_univ, Fintype.card_fin] at hprod
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
    · rw [h, one_smul]; exact hprod
    · rw [h, Units.neg_smul, one_smul]; exact hprod.neg
  have := SizeLE.finsetSum Finset.univ _ (fun τ _ => hterm τ)
  rwa [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at this

theorem SizeLE.coeff_optionEquivLeft {τ : Type*} {q : MvPolynomial (Option τ) ℤ} {d M : ℕ}
    (hq : SizeLE q d M) (k : ℕ) : SizeLE ((optionEquivLeft ℤ τ q).coeff k) d M := by
  refine ⟨(totalDegree_coeff_optionEquivLeft_le (p := q) (i := k)).trans hq.1, ?_⟩
  refine CoefficientMassLE.of_coeff_injective (fun d => d.optionElim k) ?_
    (fun d => optionEquivLeft_coeff_coeff (p := q) (m := k) (d := d)) hq.2
  intro d d' h
  ext i
  simpa using congrArg (fun t : Option τ →₀ ℕ => t (some i)) h

end NLQCLean.Elimination
