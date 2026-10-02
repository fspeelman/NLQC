import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Combinatorics.Nullstellensatz

/-!
# A unimodular shear with a constant leading coefficient

For a nonzero `P ∈ A[z₀, …, zₙ]` of total degree `e` over a characteristic-zero domain
`A`, the shear `zⱼ₊₁ ↦ zⱼ₊₁ + bⱼ z₀` with natural numbers `bⱼ ≤ e` (chosen by the
combinatorial Nullstellensatz) makes `P` a polynomial in `z₀` of degree exactly `e`
whose leading coefficient is a nonzero constant of `A`.
-/

namespace NLQCLean.Elimination

open MvPolynomial

variable {A : Type*} [CommRing A] {n : ℕ}

/-- Images of the variables under the shear `zⱼ₊₁ ↦ zⱼ₊₁ + aⱼ z₀`. -/
noncomputable def shearVariables (a : Fin n → A) : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A :=
  Fin.cons (X 0) fun j => X j.succ + C (a j) * X 0

/-- The shear `zⱼ₊₁ ↦ zⱼ₊₁ + aⱼ z₀`, fixing `z₀`. -/
noncomputable def shear (a : Fin n → A) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  aeval (shearVariables a)

/-- The shear variables as polynomials in `z₀` over `A[z₁, …, zₙ]`. -/
noncomputable def shearLinear (a : Fin n → A) :
    Fin (n + 1) → Polynomial (MvPolynomial (Fin n) A) :=
  Fin.cons Polynomial.X fun j => Polynomial.C (X j) + Polynomial.C (C (a j)) * Polynomial.X

theorem finSuccEquiv_shearVariables (a : Fin n → A) (i : Fin (n + 1)) :
    finSuccEquiv A n (shearVariables a i) = shearLinear a i := by
  cases i using Fin.cases with
  | zero => simp [shearVariables, shearLinear, finSuccEquiv_X_zero]
  | succ j =>
    simp only [shearVariables, shearLinear, Fin.cons_succ, map_add, map_mul,
      finSuccEquiv_X_zero, finSuccEquiv_X_succ, add_right_inj]
    rw [show (C (a j) : MvPolynomial (Fin (n + 1)) A) = algebraMap A _ (a j) from rfl,
      AlgEquiv.commutes]
    rfl

theorem finSuccEquiv_shear (a : Fin n → A) (P : MvPolynomial (Fin (n + 1)) A) :
    finSuccEquiv A n (shear a P) = aeval (shearLinear a) P := by
  have := comp_aeval_apply (f := shearVariables a) (finSuccEquiv A n).toAlgHom P
  simpa [shear, finSuccEquiv_shearVariables] using this

theorem natDegree_shearLinear_le (a : Fin n → A) (i : Fin (n + 1)) :
    (shearLinear a i).natDegree ≤ 1 := by
  cases i using Fin.cases with
  | zero => simpa [shearLinear] using Polynomial.natDegree_X_le
  | succ j =>
    simp only [shearLinear, Fin.cons_succ]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le

theorem coeff_one_shearLinear (a : Fin n → A) (i : Fin (n + 1)) :
    (shearLinear a i).coeff 1 = (Fin.cons 1 fun j => C (a j) : Fin (n + 1) → _) i := by
  cases i using Fin.cases with
  | zero => simp [shearLinear]
  | succ j => simp [shearLinear, Polynomial.coeff_C]

/-- Degree and top coefficient of a product of powers of polynomials of degree at most one. -/
theorem prod_pow_natDegree_le_and_coeff {R ι : Type*} [CommRing R] (s : Finset ι)
    (T : ι → Polynomial R) (hT : ∀ i, (T i).natDegree ≤ 1) (k : ι → ℕ) :
    (∏ i ∈ s, T i ^ k i).natDegree ≤ ∑ i ∈ s, k i ∧
      (∏ i ∈ s, T i ^ k i).coeff (∑ i ∈ s, k i) = ∏ i ∈ s, (T i).coeff 1 ^ k i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    have hpow : (T a ^ k a).natDegree ≤ k a := by
      simpa using Polynomial.natDegree_pow_le_of_le (k a) (hT a)
    refine ⟨Polynomial.natDegree_mul_le.trans (add_le_add hpow ih.1), ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hpow ih.1, ih.2]
    congr 1
    simpa using Polynomial.coeff_pow_of_natDegree_le (m := k a) (hT a)

/-- The total degree of a monomial exponent. -/
abbrev expDegree (m : Fin (n + 1) →₀ ℕ) : ℕ := m.sum fun _ e => e

theorem expDegree_eq (m : Fin (n + 1) →₀ ℕ) :
    expDegree m = m 0 + ∑ j : Fin n, m j.succ := by
  rw [expDegree, Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ]

/-- The top-degree part of `P`, dehomogenized at `z₀ = 1`. -/
noncomputable def topPart (P : MvPolynomial (Fin (n + 1)) A) : MvPolynomial (Fin n) A :=
  ∑ m ∈ P.support.filter (fun m => expDegree m = P.totalDegree),
    monomial (Finsupp.tail m) (P.coeff m)

theorem eval_topPart (P : MvPolynomial (Fin (n + 1)) A) (a : Fin n → A) :
    eval a (topPart P) = ∑ m ∈ P.support.filter (fun m => expDegree m = P.totalDegree),
      P.coeff m * ∏ j, a j ^ m j.succ := by
  simp only [topPart, map_sum, eval_monomial]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [Finsupp.tail_apply]

theorem totalDegree_topPart_le (P : MvPolynomial (Fin (n + 1)) A) :
    (topPart P).totalDegree ≤ P.totalDegree := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine (totalDegree_monomial_le _ _).trans ?_
  have hm' := (Finset.mem_filter.mp hm).2
  calc (Finsupp.tail m).sum (fun _ e => e) = ∑ j : Fin n, m j.succ := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]; simp [Finsupp.tail_apply]
    _ ≤ expDegree m := by rw [expDegree_eq]; omega
    _ = P.totalDegree := hm'

theorem topPart_ne_zero {P : MvPolynomial (Fin (n + 1)) A} (hP : P ≠ 0) : topPart P ≠ 0 := by
  classical
  obtain ⟨m₀, hm₀, hdeg⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.mpr hP)
    (fun m => m.sum fun _ e => e)
  have hm₀f : m₀ ∈ P.support.filter (fun m => expDegree m = P.totalDegree) :=
    Finset.mem_filter.mpr ⟨hm₀, hdeg.symm⟩
  intro h0
  have hc : (topPart P).coeff (Finsupp.tail m₀) = 0 := by rw [h0]; simp
  rw [topPart, coeff_sum, Finset.sum_eq_single m₀] at hc
  · rw [coeff_monomial, ite_eq_left rfl] at hc
    exact (mem_support_iff.mp hm₀) hc
  · intro m hm hne
    rw [coeff_monomial]
    refine ite_eq_right fun htail => hne ?_
    have hmd := (Finset.mem_filter.mp hm).2
    have hm₀d := (Finset.mem_filter.mp hm₀f).2
    rw [expDegree_eq] at hmd hm₀d
    have hsum : ∑ j : Fin n, m j.succ = ∑ j : Fin n, m₀ j.succ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simpa [Finsupp.tail_apply] using congrArg (fun t => t j) htail
    have h0' : m 0 = m₀ 0 := by omega
    rw [← Finsupp.cons_tail m, ← Finsupp.cons_tail m₀, htail, h0']
  · intro h; exact absurd hm₀f h

/-- Degree and top coefficient of the sheared polynomial in `z₀`. -/
theorem aeval_shearLinear_natDegree_le_and_coeff (a : Fin n → A)
    (P : MvPolynomial (Fin (n + 1)) A) :
    (aeval (shearLinear a) P).natDegree ≤ P.totalDegree ∧
      (aeval (shearLinear a) P).coeff P.totalDegree = C (eval a (topPart P)) := by
  classical
  have hP : aeval (shearLinear a) P = ∑ m ∈ P.support,
      Polynomial.C (C (P.coeff m)) * ∏ i, shearLinear a i ^ m i := by
    conv_lhs => rw [← support_sum_monomial_coeff P]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  have hterm : ∀ m : Fin (n + 1) →₀ ℕ,
      (∏ i, shearLinear a i ^ m i).natDegree ≤ expDegree m ∧
      (∏ i, shearLinear a i ^ m i).coeff (expDegree m) = C (∏ j, a j ^ m j.succ) := by
    intro m
    have h := prod_pow_natDegree_le_and_coeff Finset.univ (shearLinear a)
      (natDegree_shearLinear_le a) (fun i => m i)
    have hdeg : expDegree m = ∑ i, m i := Finsupp.sum_fintype _ _ (fun _ => rfl)
    rw [hdeg]
    refine ⟨h.1, ?_⟩
    rw [h.2, Fin.prod_univ_succ]
    simp [coeff_one_shearLinear]
  rw [hP]
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_, ?_⟩
  · refine (Polynomial.natDegree_C_mul_le _ _).trans ((hterm m).1.trans ?_)
    exact le_totalDegree hm
  · rw [Polynomial.finsetSum_coeff, eval_topPart, map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Polynomial.coeff_C_mul]
    split_ifs with hdeg
    · rw [← hdeg, (hterm m).2, map_mul]
    · have hlt : expDegree m < P.totalDegree := lt_of_le_of_ne (le_totalDegree hm) hdeg
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hterm m).1.trans_lt hlt), mul_zero]

/-- **Shear lemma.** A nonzero polynomial becomes, after a shear by natural numbers at most
its total degree, a polynomial in `z₀` of that degree with nonzero constant leading
coefficient. -/
theorem exists_shear_leadingCoeff [IsDomain A] [CharZero A]
    {P : MvPolynomial (Fin (n + 1)) A} (hP : P ≠ 0) :
    ∃ b : Fin n → ℕ, (∀ j, b j ≤ P.totalDegree) ∧
      (finSuccEquiv A n (shear (fun j => (b j : A)) P)).natDegree = P.totalDegree ∧
      ∃ c : A, c ≠ 0 ∧
        (finSuccEquiv A n (shear (fun j => (b j : A)) P)).leadingCoeff = C c := by
  classical
  set e := P.totalDegree
  let S : Fin n → Finset A := fun _ => (Finset.range (e + 1)).image (fun k : ℕ => (k : A))
  have hScard : ∀ j, (S j).card = e + 1 := fun j => by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hdeg : ∀ j, (topPart P).degreeOf j < (S j).card := fun j => by
    rw [hScard j]
    exact Nat.lt_succ_of_le ((degreeOf_le_totalDegree (topPart P) j).trans
      (totalDegree_topPart_le P))
  have hex : ∃ x : Fin n → A, (∀ j, x j ∈ S j) ∧ eval x (topPart P) ≠ 0 := by
    by_contra! h
    exact topPart_ne_zero hP (eq_zero_of_eval_zero_at_prod_finset _ S hdeg h)
  obtain ⟨x, hxS, hx⟩ := hex
  have hb : ∀ j, ∃ k : ℕ, k ≤ e ∧ (k : A) = x j := fun j => by
    obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp (hxS j)
    exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hkx⟩
  choose b hbe hbx using hb
  have hxb : (fun j => (b j : A)) = x := funext hbx
  have hx' : eval (fun j => (b j : A)) (topPart P) ≠ 0 := by rwa [hxb]
  obtain ⟨hle, hcoeff⟩ := aeval_shearLinear_natDegree_le_and_coeff (fun j => (b j : A)) P
  simp only [finSuccEquiv_shear]
  have hne : (aeval (shearLinear fun j => (b j : A)) P).coeff e ≠ 0 := by
    rw [hcoeff]
    intro h
    exact hx' (C_injective (Fin n) A (by simpa using h))
  have hnat : (aeval (shearLinear fun j => (b j : A)) P).natDegree = e :=
    le_antisymm hle (Polynomial.le_natDegree_of_ne_zero hne)
  refine ⟨b, hbe, hnat, _, hx', ?_⟩
  rw [Polynomial.leadingCoeff, hnat, hcoeff]

end NLQCLean.Elimination
