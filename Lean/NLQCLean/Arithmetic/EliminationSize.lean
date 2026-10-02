import NLQCLean.Arithmetic.PhysicalPolynomialHeight
import NLQCLean.Arithmetic.EliminationResultant
import NLQCLean.Arithmetic.EliminationShear

/-!
# Degree and coefficient-mass bookkeeping for iterated resultants

Polynomials in `z₀, …, zₙ₋₁` over the parameter ring `ℤ[y, c]` are measured after
flattening into integer polynomials in `z` and the parameters; polynomials in an
auxiliary variable `u` over that ring are flattened with `u` as one more variable.
Total degree and the existing coefficient-mass certificates `CoefficientMassLE` are
transported through coefficient extraction, shears and Sylvester determinants.
-/

namespace NLQCLean.Elimination

open MvPolynomial NLQCLean.PhysicalPolynomial

/-- The parameter ring `ℤ[y, c]`; variable `0` is `y` and variable `1` is `c`. -/
abbrev Par := MvPolynomial (Fin 2) ℤ

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

/-! ### Flattening -/

/-- Flattening of `ℤ[y, c][z₀, …, zₙ₋₁]` into integer polynomials in `z` and the
parameters. -/
noncomputable def flat (n : ℕ) : MvPolynomial (Fin n) Par →+* MvPolynomial (Fin n ⊕ Fin 2) ℤ :=
  eval₂Hom (MvPolynomial.rename Sum.inr : Par →ₐ[ℤ] MvPolynomial (Fin n ⊕ Fin 2) ℤ).toRingHom
    (fun i => X (Sum.inl i))

/-- Flattening of `ℤ[y, c][z][u]`, with `u` as the variable `none`. -/
noncomputable def flatU (n : ℕ) :
    Polynomial (MvPolynomial (Fin n) Par) →+* MvPolynomial (Option (Fin n ⊕ Fin 2)) ℤ :=
  Polynomial.eval₂RingHom ((MvPolynomial.rename some).toRingHom.comp (flat n)) (X none)

@[simp] theorem flat_C (n : ℕ) (r : Par) : flat n (C r) = MvPolynomial.rename Sum.inr r := by
  simp [flat]

@[simp] theorem flat_X (n : ℕ) (i : Fin n) : flat n (X i) = X (Sum.inl i) := by
  simp [flat]

@[simp] theorem flatU_C (n : ℕ) (b : MvPolynomial (Fin n) Par) :
    flatU n (Polynomial.C b) = MvPolynomial.rename some (flat n b) := by
  simp [flatU]

@[simp] theorem flatU_X (n : ℕ) : flatU n Polynomial.X = X none := by
  simp [flatU]

theorem flat_eq_sumRingEquiv_symm (n : ℕ) :
    flat n = (sumRingEquiv ℤ (Fin n) (Fin 2)).symm.toRingHom := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · rw [flat_C]
    have : ((sumRingEquiv ℤ (Fin n) (Fin 2)).symm.toRingHom.comp
        (C : Par →+* MvPolynomial (Fin n) Par)) =
        (MvPolynomial.rename Sum.inr : Par →ₐ[ℤ] _).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun z => ?_) (fun k => ?_)
      · simp
      · simp [sumRingEquiv_symm_C_X]
    exact (RingHom.congr_fun this r).symm
  · simp [sumRingEquiv_symm_X]

theorem flat_injective (n : ℕ) : Function.Injective (flat n) := by
  rw [flat_eq_sumRingEquiv_symm]
  exact (sumRingEquiv ℤ (Fin n) (Fin 2)).symm.injective

/-- Reindexing `Fin (n+1) ⊕ Fin 2` with `z₀` as the distinguished variable `none`. -/
def splitFirst (n : ℕ) : Fin (n + 1) ⊕ Fin 2 → Option (Fin n ⊕ Fin 2)
  | Sum.inl i => Fin.cases none (fun j => some (Sum.inl j)) i
  | Sum.inr k => some (Sum.inr k)

theorem flatU_finSuccEquiv (n : ℕ) (P : MvPolynomial (Fin (n + 1)) Par) :
    flatU n (finSuccEquiv Par n P) = MvPolynomial.rename (splitFirst n) (flat (n + 1) P) := by
  have h : (flatU n).comp (finSuccEquiv Par n).toRingEquiv.toRingHom =
      (MvPolynomial.rename (splitFirst n)).toRingHom.comp (flat (n + 1)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, flat_C, AlgHom.toRingHom_eq_coe]
      rw [show (C r : MvPolynomial (Fin (n + 1)) Par) = algebraMap Par _ r from rfl,
        AlgEquiv.commutes]
      simp [MvPolynomial.rename_rename]
      rfl
    · cases i using Fin.cases with
      | zero => simp [finSuccEquiv_X_zero, splitFirst]
      | succ j => simp [finSuccEquiv_X_succ, splitFirst]
  exact RingHom.congr_fun h P

theorem optionEquivLeft_comp_rename_some {τ : Type*} :
    (optionEquivLeft ℤ τ).toRingEquiv.toRingHom.comp
        (MvPolynomial.rename (some : τ → Option τ)).toRingHom = Polynomial.C := by
  refine MvPolynomial.ringHom_ext (fun z => ?_) (fun i => ?_)
  · simp
  · simp [optionEquivLeft_X_some]

theorem optionEquivLeft_flatU (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) Par)) :
    optionEquivLeft ℤ _ (flatU n p) = p.map (flat n) := by
  have h : (optionEquivLeft ℤ (Fin n ⊕ Fin 2)).toRingEquiv.toRingHom.comp (flatU n) =
      Polynomial.mapRingHom (flat n) := by
    refine Polynomial.ringHom_ext (fun b => ?_) ?_
    · have := RingHom.congr_fun (optionEquivLeft_comp_rename_some (τ := Fin n ⊕ Fin 2))
        (flat n b)
      simpa using this
    · simp [optionEquivLeft_X_none]
  exact RingHom.congr_fun h p

theorem flat_coeff (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) Par)) (k : ℕ) :
    flat n (p.coeff k) = (optionEquivLeft ℤ _ (flatU n p)).coeff k := by
  rw [optionEquivLeft_flatU, Polynomial.coeff_map]

theorem SizeLE.coeff_optionEquivLeft {τ : Type*} {q : MvPolynomial (Option τ) ℤ} {d M : ℕ}
    (hq : SizeLE q d M) (k : ℕ) : SizeLE ((optionEquivLeft ℤ τ q).coeff k) d M := by
  refine ⟨(totalDegree_coeff_optionEquivLeft_le (p := q) (i := k)).trans hq.1, ?_⟩
  refine CoefficientMassLE.of_coeff_injective (fun d => d.optionElim k) ?_
    (fun d => optionEquivLeft_coeff_coeff (p := q) (m := k) (d := d)) hq.2
  intro d d' h
  ext i
  simpa using congrArg (fun t : Option τ →₀ ℕ => t (some i)) h

theorem SizeLE.flat_coeff {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) Par)} {d M : ℕ}
    (hp : SizeLE (flatU n p) d M) (k : ℕ) : SizeLE (flat n (p.coeff k)) d M := by
  rw [NLQCLean.Elimination.flat_coeff]; exact hp.coeff_optionEquivLeft k

theorem natDegree_le_totalDegree_flatU (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) Par)) :
    p.natDegree ≤ (flatU n p).totalDegree := by
  have h1 : (p.map (flat n)).natDegree = p.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (flat_injective n) p
  rw [← h1, ← optionEquivLeft_flatU, natDegree_optionEquivLeft]
  exact degreeOf_le_totalDegree _ _

theorem SizeLE.flatU_finSuccEquiv {n : ℕ} {P : MvPolynomial (Fin (n + 1)) Par} {d M : ℕ}
    (hP : SizeLE (flat (n + 1) P) d M) : SizeLE (flatU n (finSuccEquiv Par n P)) d M := by
  rw [NLQCLean.Elimination.flatU_finSuccEquiv]; exact hP.rename _


/-! ### Shears -/

/-- The shear on flattened polynomials. -/
noncomputable def flatShearVariables {n : ℕ} (b : Fin n → ℕ) :
    Fin (n + 1) ⊕ Fin 2 → MvPolynomial (Fin (n + 1) ⊕ Fin 2) ℤ
  | Sum.inl i => Fin.cases (X (Sum.inl 0))
      (fun j => X (Sum.inl j.succ) + C (b j : ℤ) * X (Sum.inl 0)) i
  | Sum.inr k => X (Sum.inr k)

theorem flat_shear {n : ℕ} (b : Fin n → ℕ) (P : MvPolynomial (Fin (n + 1)) Par) :
    flat (n + 1) (shear (fun j => (b j : Par)) P) =
      MvPolynomial.bind₁ (flatShearVariables b) (flat (n + 1) P) := by
  have h : (flat (n + 1)).comp (shear (fun j => (b j : Par))).toRingHom =
      (MvPolynomial.bind₁ (flatShearVariables b)).toRingHom.comp (flat (n + 1)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, flat_C]
      rw [show (C r : MvPolynomial (Fin (n + 1)) Par) = algebraMap Par _ r from rfl,
        AlgHom.commutes, MvPolynomial.algebraMap_eq, flat_C, bind₁_rename]
      have : (flatShearVariables b ∘ Sum.inr : Fin 2 → _) = X ∘ Sum.inr := by
        funext k; rfl
      rw [this, ← bind₁_rename, bind₁_X_left, AlgHom.id_apply]
    · cases i using Fin.cases with
      | zero => simp [shear, shearVariables, flatShearVariables]
      | succ j => simp [shear, shearVariables, flatShearVariables]
  exact RingHom.congr_fun h P

theorem SizeLE.flatShearVariables {n B : ℕ} (b : Fin n → ℕ) (hb : ∀ j, b j ≤ B)
    (v : Fin (n + 1) ⊕ Fin 2) : SizeLE (NLQCLean.Elimination.flatShearVariables b v) 1 (B + 1) := by
  rcases v with i | k
  · cases i using Fin.cases with
    | zero => exact (SizeLE.X _).mono le_rfl (by omega)
    | succ j =>
      have hC : SizeLE (C (b j : ℤ) : MvPolynomial (Fin (n + 1) ⊕ Fin 2) ℤ) 0 B :=
        ⟨(totalDegree_C _).le, (CoefficientMassLE.constant _).mono (by simpa using hb j)⟩
      have := (SizeLE.X (Sum.inl j.succ)).add ((hC.mul (SizeLE.X (Sum.inl 0))).mono
        (by omega) (le_refl (B * 1)))
      exact this.mono le_rfl (by omega)
  · exact (SizeLE.X _).mono le_rfl (by omega)

theorem SizeLE.flat_shear {n d M B : ℕ} {P : MvPolynomial (Fin (n + 1)) Par}
    (hP : SizeLE (flat (n + 1) P) d M) (b : Fin n → ℕ) (hb : ∀ j, b j ≤ B) :
    SizeLE (flat (n + 1) (shear (fun j => (b j : Par)) P)) d (M * (B + 1) ^ d) := by
  rw [NLQCLean.Elimination.flat_shear]
  refine ⟨(PhysicalPolynomial.totalDegree_bind₁_le_of_linear_variables _
    (fun v => (SizeLE.flatShearVariables b hb v).1) _).trans hP.1, ?_⟩
  exact CoefficientMassLE.bind₁_le hP.2 hP.1 _ (by omega)
    (fun v => (SizeLE.flatShearVariables b hb v).2)

/-! ### The eliminant -/

theorem sylvester_entry_cases {R : Type*} [CommRing R] (f g : Polynomial R) (m n : ℕ)
    (i j : Fin (m + n)) :
    Polynomial.sylvester f g m n i j = 0 ∨ (∃ k, Polynomial.sylvester f g m n i j = f.coeff k) ∨
      ∃ k, Polynomial.sylvester f g m n i j = g.coeff k := by
  unfold Polynomial.sylvester
  induction j using Fin.addCases with
  | left j =>
    simp only [Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
    · exact Or.inl rfl
  | right j =>
    simp only [Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inl rfl

theorem coeff_kronecker {n s : ℕ} (G : Fin s → Polynomial (MvPolynomial (Fin n) Par)) (k : ℕ) :
    (kronecker G).coeff k = ∑ i, Polynomial.C ((G i).coeff k) * Polynomial.X ^ (i : ℕ) := by
  unfold kronecker
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_map]

/-- Size of the flattened eliminant. -/
theorem SizeLE.flatU_eliminant {n s D M m n' : ℕ} (hD : 1 ≤ D) (hs : s ≤ D)
    {f : Polynomial (MvPolynomial (Fin n) Par)} {G : Fin s → Polynomial (MvPolynomial (Fin n) Par)}
    (hf : ∀ k, SizeLE (flat n (f.coeff k)) D M) (hG : ∀ i k, SizeLE (flat n ((G i).coeff k)) D M) :
    SizeLE (flatU n (eliminant f G m n')) ((m + n') * (2 * D))
      ((m + n').factorial * (D * M) ^ (m + n')) := by
  unfold eliminant Polynomial.resultant
  have hdet := RingHom.map_det (flatU n) ((f.map Polynomial.C).sylvester (kronecker G) m n')
  erw [hdet]
  refine SizeLE.det _ fun i j => ?_
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  rcases sylvester_entry_cases (f.map Polynomial.C) (kronecker G) m n' i j with h | ⟨k, h⟩ | ⟨k, h⟩
  · rw [h, map_zero]; exact SizeLE.zero _ _
  · rw [h, Polynomial.coeff_map, flatU_C]
    exact ((hf k).rename _).mono (by omega) (Nat.le_mul_of_pos_left _ hD)
  · rw [h, coeff_kronecker, map_sum]
    have hterm : ∀ i : Fin s, SizeLE (flatU n (Polynomial.C ((G i).coeff k) *
        Polynomial.X ^ (i : ℕ))) (2 * D) M := by
      intro i
      rw [map_mul, map_pow, flatU_C, flatU_X]
      have := ((hG i k).rename some).mul ((SizeLE.X (none : Option (Fin n ⊕ Fin 2))).pow i)
      refine this.mono ?_ (by simp)
      have := i.isLt
      omega
    have := SizeLE.finsetSum Finset.univ _ (fun i _ => hterm i)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this.mono le_rfl (Nat.mul_le_mul_right _ hs)

end NLQCLean.Elimination
