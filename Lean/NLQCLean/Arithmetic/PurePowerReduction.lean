import NLQCLean.Arithmetic.EliminationSize
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Roots

/-!
# Pure-power systems and the determinant trick

Let `U` index the unknowns and `P` the parameters. Let `f_u = a · z_u^{e_u} + r_u` be
integer polynomials in `z ⊕ p`, one for each unknown `u`, with `a ≠ 0` and
`totalDegree r_u < e_u` (the degree counts the parameters). Then:

* **Reduction.** For every polynomial `p` of total degree at most `n`, `a^n p` is
  congruent modulo `(f)` to a combination of the `∏ e_u` monomials `z^b` with
  `b_u < e_u`. The coefficients are parameter polynomials of degree at most `n` and
  mass at most `‖p‖₁ K^n`, where `K` bounds `|a|` and the masses of the `r_u`.
* **Determinant trick.** Write `Y = z_{y₀}` and `M` for the reduction matrix of
  multiplication by `a^D Y`. Then `Φ = det(a^D T − M)` lies in `(f)` after `T ↦ Y`.
  For every parameter value it is a nonzero polynomial in `T`, with leading
  coefficient `a^{D·N}`.

No Gröbner theory is used. The reduction lowers total degree.
-/

namespace NLQCLean.PurePower

open MvPolynomial NLQCLean.PhysicalPolynomial NLQCLean.Elimination

/-! ### The ℓ¹ coefficient mass -/

/-- The sum of the absolute values of the coefficients. -/
def l1 {σ : Type*} (p : MvPolynomial σ ℤ) : ℕ := ∑ m ∈ p.support, (p.coeff m).natAbs

theorem massLE_l1 {σ : Type*} (p : MvPolynomial σ ℤ) : CoefficientMassLE p (l1 p) := by
  classical
  refine ⟨∑ m ∈ p.support, monomial m (p.coeff m).natAbs, fun m => ?_, ?_⟩
  · rw [coeff_sum]
    by_cases hm : m ∈ p.support
    · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, ite_eq_right hb])
        (fun h => absurd hm h), coeff_monomial, ite_eq_left rfl]
    · rw [notMem_support_iff.mp hm]
      simp
  · rw [map_sum]
    refine le_of_eq (Finset.sum_congr rfl fun m _ => ?_)
    simp [naturalCoefficientMass, MvPolynomial.eval_monomial]

theorem l1_le {σ : Type*} {p : MvPolynomial σ ℤ} {M : ℕ} (h : CoefficientMassLE p M) :
    l1 p ≤ M := by
  classical
  obtain ⟨q, hq, hqm⟩ := h
  have hsub : p.support ⊆ q.support := fun m hm => by
    rw [mem_support_iff] at hm ⊢
    have := hq m
    have : 0 < (p.coeff m).natAbs := Int.natAbs_pos.mpr hm
    omega
  calc l1 p ≤ ∑ m ∈ p.support, q.coeff m := Finset.sum_le_sum fun m _ => hq m
    _ ≤ ∑ m ∈ q.support, q.coeff m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ = naturalCoefficientMass q := (naturalCoefficientMass_eq_sum q).symm
    _ ≤ M := hqm

theorem massLE_monomial {σ : Type*} (m : σ →₀ ℕ) (z : ℤ) :
    CoefficientMassLE (monomial m z) z.natAbs := by
  classical
  refine ⟨monomial m z.natAbs, fun m' => ?_, by simp [naturalCoefficientMass, MvPolynomial.eval_monomial]⟩
  rw [coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem SizeLE.finsetSum' {σ ι : Type*} (t : Finset ι) (p : ι → MvPolynomial σ ℤ) {d : ℕ}
    (M : ι → ℕ) (h : ∀ i ∈ t, SizeLE (p i) d (M i)) :
    SizeLE (∑ i ∈ t, p i) d (∑ i ∈ t, M i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (SizeLE.zero (σ := σ) d 0)
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Leibniz bound for a determinant over any finite index type. -/
theorem SizeLE.det' {σ ι : Type*} [Fintype ι] [DecidableEq ι] {d B : ℕ}
    (A : Matrix ι ι (MvPolynomial σ ℤ)) (hA : ∀ i j, SizeLE (A i j) d B) :
    SizeLE A.det (Fintype.card ι * d) ((Fintype.card ι).factorial * B ^ Fintype.card ι) := by
  classical
  set e := Fintype.equivFin ι
  have h := SizeLE.det (A.submatrix e.symm e.symm) (fun i j => hA _ _)
  rwa [Matrix.det_submatrix_equiv_self] at h

/-! ### Pure-power systems -/

variable {U P : Type*} [Fintype U] [DecidableEq U] [DecidableEq P]

/-- A square system `f_u = a z_u^{e_u} + r_u` with `deg r_u < e_u`. -/
structure System (U P : Type*) where
  e : U → ℕ
  a : ℤ
  f : U → MvPolynomial (U ⊕ P) ℤ
  r : U → MvPolynomial (U ⊕ P) ℤ
  he : ∀ u, 1 ≤ e u
  ha : a ≠ 0
  hf : ∀ u, f u = C a * X (Sum.inl u) ^ e u + r u
  hr : ∀ u, (r u).totalDegree < e u

/-- Exponent vectors of the reduced monomials. -/
abbrev Bas (e : U → ℕ) := (u : U) → Fin (e u)

/-- The reduced monomial `z^b`. -/
noncomputable def bm (e : U → ℕ) (b : Bas e) : MvPolynomial (U ⊕ P) ℤ :=
  ∏ u, X (Sum.inl u) ^ (b u : ℕ)

theorem split_eq (m : (U ⊕ P) →₀ ℕ) :
    m = (m.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr +
      ∑ u, Finsupp.single (Sum.inl u) (m (Sum.inl u)) := by
  classical
  ext i
  rcases i with u | p
  · rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ (by simp), zero_add,
      Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single u (fun v _ hv => by
      rw [Finsupp.single_apply, ite_eq_right_iff.mpr (fun h => absurd (Sum.inl_injective h) hv)])
      (fun h => absurd (Finset.mem_univ u) h), Finsupp.single_eq_same]
  · rw [Finsupp.add_apply, Finsupp.finsetSum_apply]
    simp [Sum.inr_injective, Finsupp.comapDomain_apply]

theorem monomial_split (m : (U ⊕ P) →₀ ℕ) (z : ℤ) :
    monomial m z = rename Sum.inr (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) z) *
      ∏ u, (X (Sum.inl u) : MvPolynomial (U ⊕ P) ℤ) ^ m (Sum.inl u) := by
  classical
  have hprod : ∏ u, (X (Sum.inl u) : MvPolynomial (U ⊕ P) ℤ) ^ m (Sum.inl u) =
      monomial (∑ u, Finsupp.single (Sum.inl u) (m (Sum.inl u))) 1 := by
    rw [monomial_sum_one]
    exact Finset.prod_congr rfl fun u _ => X_pow_eq_monomial
  rw [hprod, rename_monomial, monomial_mul_monomial, mul_one, ← split_eq m]

section Reduction

variable (S : System U P) {Mr K : ℕ}

omit [DecidableEq U] [DecidableEq P] in
theorem totalDegree_bm (b : Bas S.e) : (bm (P := P) S.e b).totalDegree ≤ ∑ u, (b u : ℕ) := by
  classical
  refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun u _ => ?_)
  refine (totalDegree_pow _ _).trans ?_
  rw [totalDegree_X, mul_one]

/-- The reduction statement at level `n`. -/
def Reduces (S : System U P) (K n : ℕ) (p : MvPolynomial (U ⊕ P) ℤ) : Prop :=
  ∃ c : Bas S.e → MvPolynomial P ℤ, (∀ b, SizeLE (c b) n (l1 p * K ^ n)) ∧
    C S.a ^ n * p - ∑ b, rename Sum.inr (c b) * bm S.e b ∈ Ideal.span (Set.range S.f)

/-- One monomial at level `n`, given the reduction below `n`. -/
theorem reduce_monomial (hMr : ∀ u, l1 (S.r u) ≤ Mr) (hK : Mr ≤ K) (haK : S.a.natAbs ≤ K)
    (n : ℕ) (IH : ∀ k < n, ∀ p : MvPolynomial (U ⊕ P) ℤ, p.totalDegree ≤ k → Reduces S K k p)
    (m : (U ⊕ P) →₀ ℕ) (z : ℤ) (hm : Finsupp.degree m ≤ n) :
    ∃ c : Bas S.e → MvPolynomial P ℤ, (∀ b, SizeLE (c b) n (z.natAbs * K ^ n)) ∧
      C S.a ^ n * monomial m z - ∑ b, rename Sum.inr (c b) * bm S.e b ∈
        Ideal.span (Set.range S.f) := by
  classical
  by_cases hbas : ∀ u, m (Sum.inl u) < S.e u
  · -- already reduced
    let b0 : Bas S.e := fun u => ⟨m (Sum.inl u), hbas u⟩
    let mP := m.comapDomain Sum.inr Sum.inr_injective.injOn
    have hmP : Finsupp.degree mP ≤ n :=
      (Finsupp.degree_comapDomain_le_of_canonicallyOrderedAdd _).trans hm
    refine ⟨fun b => if b = b0 then monomial mP (S.a ^ n * z) else 0, fun b => ?_, ?_⟩
    · by_cases hb : b = b0
      · simp only [hb, ite_true]
        refine ⟨(totalDegree_monomial_le _ _).trans hmP, ?_⟩
        refine (massLE_monomial mP _).mono ?_
        rw [Int.natAbs_mul, Int.natAbs_pow, mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left haK n)
      · simp only [hb, ite_false]
        exact SizeLE.zero _ _
    · have hsum : ∑ b, rename Sum.inr (if b = b0 then monomial mP (S.a ^ n * z) else 0) *
          bm (P := P) S.e b = rename Sum.inr (monomial mP (S.a ^ n * z)) * bm S.e b0 := by
        rw [Finset.sum_eq_single b0 (fun b _ hb => by rw [ite_eq_right hb, map_zero, zero_mul])
          (fun h => absurd (Finset.mem_univ b0) h), ite_eq_left rfl]
      rw [hsum]
      have hb0 : bm (P := P) S.e b0 =
          ∏ u, (X (Sum.inl u) : MvPolynomial (U ⊕ P) ℤ) ^ m (Sum.inl u) := rfl
      have hz : monomial mP (S.a ^ n * z) = C (S.a ^ n) * monomial mP z := by
        rw [C_mul_monomial]
      have heq : C S.a ^ n * monomial m z =
          rename Sum.inr (monomial mP (S.a ^ n * z)) * bm S.e b0 := by
        rw [hb0, hz, map_mul, rename_C, monomial_split m z, map_pow]
        ring
      rw [heq, sub_self]
      exact Submodule.zero_mem _
  · push Not at hbas
    obtain ⟨u, hu⟩ := hbas
    have hle : Finsupp.single (Sum.inl u) (S.e u) ≤ m := Finsupp.single_le_iff.mpr hu
    set m' := m - Finsupp.single (Sum.inl u) (S.e u) with hm'def
    have hm' : m = m' + Finsupp.single (Sum.inl u) (S.e u) := (tsub_add_cancel_of_le hle).symm
    have hdeg : Finsupp.degree m = Finsupp.degree m' + S.e u := by
      conv_lhs => rw [hm']
      rw [map_add, Finsupp.degree_single]
    have heu := S.he u
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hmono : monomial m z = X (Sum.inl u) ^ S.e u * monomial m' z := by
      rw [hm', X_pow_eq_monomial, monomial_mul_monomial, one_mul, add_comm]
    set p' : MvPolynomial (U ⊕ P) ℤ := -(S.r u * monomial m' z) with hp'
    have hp'deg : p'.totalDegree ≤ k := by
      rw [hp', totalDegree_neg]
      refine (totalDegree_mul _ _).trans ?_
      have h1 := S.hr u
      have h2 : (monomial m' z).totalDegree ≤ Finsupp.degree m' := totalDegree_monomial_le _ _
      omega
    have hp'l1 : l1 p' ≤ Mr * z.natAbs := by
      refine (l1_le (((massLE_l1 (S.r u)).mul (massLE_monomial m' z)).neg)).trans ?_
      exact Nat.mul_le_mul_right _ (hMr u)
    obtain ⟨c, hc, hmem⟩ := IH k (Nat.lt_succ_self k) p' hp'deg
    refine ⟨c, fun b => (hc b).mono (Nat.le_succ k) ?_, ?_⟩
    · calc l1 p' * K ^ k ≤ (K * z.natAbs) * K ^ k :=
            Nat.mul_le_mul_right _ (hp'l1.trans (Nat.mul_le_mul_right _ hK))
        _ = z.natAbs * K ^ (k + 1) := by ring
    · have hrw : C S.a ^ (k + 1) * monomial m z - ∑ b, rename Sum.inr (c b) * bm S.e b =
          C S.a ^ k * monomial m' z * S.f u +
            (C S.a ^ k * p' - ∑ b, rename Sum.inr (c b) * bm S.e b) := by
        rw [hmono, S.hf u, hp']
        ring
      rw [hrw]
      exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨u, rfl⟩)) hmem

/-- **Reduction.** Every polynomial of total degree at most `n` reduces at level `n`. -/
theorem reduce (hMr : ∀ u, l1 (S.r u) ≤ Mr) (hK : Mr ≤ K) (haK : S.a.natAbs ≤ K) :
    ∀ n (p : MvPolynomial (U ⊕ P) ℤ), p.totalDegree ≤ n → Reduces S K n p := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro p hp
  have hmono : ∀ m : (U ⊕ P) →₀ ℕ, ∃ c : Bas S.e → MvPolynomial P ℤ,
      (∀ b, SizeLE (c b) n ((p.coeff m).natAbs * K ^ n)) ∧
      C S.a ^ n * monomial m (p.coeff m) - ∑ b, rename Sum.inr (c b) * bm S.e b ∈
        Ideal.span (Set.range S.f) := by
    intro m
    by_cases hm : m ∈ p.support
    · exact reduce_monomial S hMr hK haK n IH m _ ((le_totalDegree hm).trans hp)
    · refine ⟨fun _ => 0, fun _ => SizeLE.zero _ _, ?_⟩
      rw [notMem_support_iff.mp hm, map_zero, mul_zero]
      simp
  choose c hc hmem using hmono
  refine ⟨fun b => ∑ m ∈ p.support, c m b, fun b => ?_, ?_⟩
  · have h := SizeLE.finsetSum' p.support (fun m => c m b)
      (fun m => (p.coeff m).natAbs * K ^ n) (fun m _ => hc m b)
    refine h.mono le_rfl (le_of_eq ?_)
    rw [← Finset.sum_mul]
    rfl
  · have hrw : C S.a ^ n * p - ∑ b, rename Sum.inr (∑ m ∈ p.support, c m b) * bm S.e b =
        ∑ m ∈ p.support, (C S.a ^ n * monomial m (p.coeff m) -
          ∑ b, rename Sum.inr (c m b) * bm S.e b) := by
      calc C S.a ^ n * p - ∑ b, rename Sum.inr (∑ m ∈ p.support, c m b) * bm S.e b
          = C S.a ^ n * (∑ m ∈ p.support, monomial m (p.coeff m)) -
              ∑ b, rename Sum.inr (∑ m ∈ p.support, c m b) * bm S.e b := by
            rw [← MvPolynomial.as_sum p]
        _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
            congr 1
            simp only [map_sum, Finset.sum_mul]
            exact Finset.sum_comm
    rw [hrw]
    exact Ideal.sum_mem _ fun m _ => hmem m

end Reduction

/-! ### The determinant trick -/

theorem det_mem_of_mulVec {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (I : Ideal R)
    (A : Matrix ι ι R) (v : ι → R) (hv : ∀ i, A.mulVec v i ∈ I) (i0 : ι) (hi0 : v i0 = 1) :
    A.det ∈ I := by
  have h : (A.adjugate * A).mulVec v = A.adjugate.mulVec (A.mulVec v) :=
    (Matrix.mulVec_mulVec _ _ _).symm
  rw [Matrix.adjugate_mul] at h
  have h0 := congrFun h i0
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, hi0, smul_eq_mul, mul_one] at h0
  rw [h0, Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv j)

section Determinant

variable (S : System U P) {Mr K : ℕ}

/-- The level `D = 1 + Σ (e_u − 1)` of the multiplication matrix. -/
def dExp : ℕ := 1 + ∑ u, (S.e u - 1)

omit [DecidableEq U] [DecidableEq P] in
theorem totalDegree_X_mul_bm (y0 : U) (b : Bas S.e) :
    (X (Sum.inl y0) * bm (P := P) S.e b).totalDegree ≤ dExp S := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X]
  have := totalDegree_bm S b
  have h2 : ∑ u, (b u : ℕ) ≤ ∑ u, (S.e u - 1) :=
    Finset.sum_le_sum fun u _ => by have := (b u).2; omega
  unfold dExp
  omega

omit [DecidableEq U] [DecidableEq P] in
theorem l1_X_mul_bm (y0 : U) (b : Bas S.e) : l1 (X (Sum.inl y0) * bm (P := P) S.e b) ≤ 1 := by
  refine l1_le ?_
  have hb : CoefficientMassLE (bm (P := P) S.e b) 1 := by
    have h := SizeLE.finsetProd (σ := U ⊕ P) Finset.univ
      (fun u => (X (Sum.inl u) : MvPolynomial (U ⊕ P) ℤ) ^ (b u : ℕ)) (d := dExp S) (M := 1)
      (fun u _ => by
        refine ⟨?_, by simpa using (CoefficientMassLE.variablePolynomial (Sum.inl u)).pow (b u : ℕ)⟩
        refine (totalDegree_pow _ _).trans ?_
        rw [totalDegree_X, mul_one]
        have := (b u).2
        have : (S.e u - 1) ≤ ∑ v, (S.e v - 1) :=
          Finset.single_le_sum (f := fun v => S.e v - 1) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ u)
        unfold dExp
        omega)
    exact (by simpa using h.2 : CoefficientMassLE (∏ u, (X (Sum.inl u) : MvPolynomial (U ⊕ P) ℤ) ^ (b u : ℕ)) 1)
  simpa using (CoefficientMassLE.variablePolynomial (Sum.inl y0)).mul hb

omit [DecidableEq U] [DecidableEq P] in
theorem one_le_dExp : 1 ≤ dExp S := by unfold dExp; omega

/-- **Determinant trick.** A polynomial `Φ(T, p)` of controlled size lies in `(f)` after
`T ↦ z_{y₀}`; for every parameter value it vanishes for only finitely many `T`. -/
theorem exists_det_eliminant (hMr : ∀ u, l1 (S.r u) ≤ Mr) (hK : Mr ≤ K)
    (haK : S.a.natAbs ≤ K) (y0 : U) :
    ∃ Φ : MvPolynomial (Option P) ℤ,
      SizeLE Φ (Fintype.card (Bas S.e) * dExp S)
        ((Fintype.card (Bas S.e)).factorial * (K ^ dExp S + K ^ dExp S) ^
          Fintype.card (Bas S.e)) ∧
      rename (fun o => Option.elim o (Sum.inl y0) Sum.inr) Φ ∈ Ideal.span (Set.range S.f) ∧
      ∀ v : P → ℝ,
        {t : ℝ | eval₂ (Int.castRingHom ℝ) (fun o => Option.elim o t v) Φ = 0}.Finite := by
  classical
  set D := dExp S with hD
  have hred := fun b => reduce S hMr hK haK D (X (Sum.inl y0) * bm (P := P) S.e b)
    (totalDegree_X_mul_bm S y0 b)
  unfold Reduces at hred
  choose c hc hmem using hred
  let A : Matrix (Bas S.e) (Bas S.e) (MvPolynomial (Option P) ℤ) := fun b b' =>
    (if b = b' then C (S.a ^ D) * X none else 0) - rename some (c b b')
  refine ⟨A.det, ?_, ?_, ?_⟩
  · refine SizeLE.det' A fun b b' => ?_
    have h1 : SizeLE (if b = b' then C (S.a ^ D) * X none else 0 : MvPolynomial (Option P) ℤ)
        D (K ^ D) := by
      split_ifs
      · refine ⟨?_, ?_⟩
        · refine (totalDegree_mul _ _).trans ?_
          rw [totalDegree_C, totalDegree_X]
          exact one_le_dExp S
        · refine ((CoefficientMassLE.constant (S.a ^ D)).mul
            (CoefficientMassLE.variablePolynomial none)).mono ?_
          rw [mul_one, Int.natAbs_pow]
          exact Nat.pow_le_pow_left haK D
      · exact SizeLE.zero _ _
    have h2 : SizeLE (rename some (c b b')) D (K ^ D) :=
      ((hc b b').rename some).mono le_rfl
        (by have := l1_X_mul_bm S y0 b; nlinarith [Nat.zero_le (K ^ D)])
    have := h1.add h2.neg
    rwa [← sub_eq_add_neg] at this
  · let j : MvPolynomial (Option P) ℤ →+* MvPolynomial (U ⊕ P) ℤ :=
      (rename (fun o => Option.elim o (Sum.inl y0) Sum.inr)).toRingHom
    change j A.det ∈ _
    rw [RingHom.map_det]
    refine det_mem_of_mulVec _ _ (fun b => bm (P := P) S.e b) (fun b => ?_)
      (fun u => ⟨0, S.he u⟩) (by simp [bm])
    have hentry : ∀ b', j (A b b') = (if b = b' then C (S.a ^ D) * X (Sum.inl y0) else 0) -
        rename Sum.inr (c b b') := by
      intro b'
      simp only [A, j, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub]
      congr 1
      · split_ifs <;> simp
      · rw [rename_rename]
        rfl
    have hsum : (j.mapMatrix A).mulVec (fun b => bm (P := P) S.e b) b =
        C S.a ^ D * (X (Sum.inl y0) * bm S.e b) - ∑ b', rename Sum.inr (c b b') * bm S.e b' := by
      simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, hentry,
        sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, map_pow]
      ring
    rw [hsum]
    exact hmem b
  · intro v
    set m : Matrix (Bas S.e) (Bas S.e) ℝ := fun b b' => eval₂ (Int.castRingHom ℝ) v (c b b')
    set α : ℝ := (S.a : ℝ) ^ D
    have hα : α ≠ 0 := pow_ne_zero _ (Int.cast_ne_zero.mpr S.ha)
    have hent : ∀ (t : ℝ) (b b' : Bas S.e),
        eval₂ (Int.castRingHom ℝ) (fun o => Option.elim o t v) (A b b') =
          α * ((if b = b' then t else 0) - α⁻¹ * m b b') := by
      intro t b b'
      simp only [A, m]
      rw [eval₂_sub, eval₂_rename]
      split_ifs
      · simp only [eval₂_mul, eval₂_C, eval₂_X, Option.elim_none, Function.comp_def,
          Option.elim_some, α]
        have h1 : (Int.castRingHom ℝ) (S.a ^ D) = (S.a : ℝ) ^ D := by simp
        rw [h1, mul_sub, mul_inv_cancel_left₀ hα]
      · simp only [eval₂_zero, Function.comp_def, Option.elim_some, α]
        rw [mul_sub, mul_inv_cancel_left₀ hα, mul_zero]
    have hval : ∀ t : ℝ, eval₂ (Int.castRingHom ℝ) (fun o => Option.elim o t v) A.det =
        α ^ Fintype.card (Bas S.e) * (α⁻¹ • m).charpoly.eval t := by
      intro t
      rw [← coe_eval₂Hom, RingHom.map_det, Matrix.eval_charpoly, ← Matrix.det_smul]
      congr 1
      ext b b'
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, coe_eval₂Hom, hent]
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
        smul_eq_mul]
    have hroot : {t : ℝ | eval₂ (Int.castRingHom ℝ) (fun o => Option.elim o t v) A.det = 0} ⊆
        {t | (α⁻¹ • m).charpoly.IsRoot t} := by
      intro t ht
      simp only [Set.mem_ofPred_eq, hval t] at ht ⊢
      exact (mul_eq_zero.mp ht).resolve_left (pow_ne_zero _ hα)
    exact (Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic _).ne_zero).subset hroot

end Determinant

end NLQCLean.PurePower
