import NLQCLean.Arithmetic.ControlledPhaseScorePolynomial
import NLQCLean.Arithmetic.CosineTransform

/-!
# Explicit coefficient bounds for physical polynomials

Nonnegative integer polynomials explicitly majorize the absolute values of
the coefficients. Evaluation of these majorants at all ones bounds
every coefficient. All numerical height bounds are natural-number formulas;
no coefficient-height field, elimination theorem or arithmetic external
premise is supplied.
-/

noncomputable section

namespace NLQCLean.PhysicalPolynomial

attribute [local implicit_reducible] Matrix

open Matrix MvPolynomial
open scoped BigOperators

/-- Pointwise comparison with a nonnegative-coefficient polynomial. -/
def NaturalMajorizes {σ : Type*} (p : MvPolynomial σ ℤ) (q : MvPolynomial σ ℕ) : Prop :=
  ∀ m, (coeff m p).natAbs ≤ coeff m q

namespace NaturalMajorizes

variable {σ : Type*} {p r : MvPolynomial σ ℤ} {q t : MvPolynomial σ ℕ}

theorem zero (q : MvPolynomial σ ℕ) : NaturalMajorizes (0 : MvPolynomial σ ℤ) q := by
  intro m
  simp

theorem constant {a : ℤ} {b : ℕ} (h : a.natAbs ≤ b) :
    NaturalMajorizes (C a : MvPolynomial σ ℤ) (C b) := by
  classical
  intro m
  simp only [coeff_C]
  split_ifs <;> simp_all

theorem one : NaturalMajorizes (1 : MvPolynomial σ ℤ) 1 := by
  simpa only [C_1] using (constant (σ := σ) (a := 1) (b := 1) (by decide))

theorem variablePolynomial (i : σ) : NaturalMajorizes (X i : MvPolynomial σ ℤ) (X i) := by
  classical
  intro m
  simp only [coeff_X]
  split_ifs <;> simp

theorem add (hp : NaturalMajorizes p q) (hr : NaturalMajorizes r t) :
    NaturalMajorizes (p + r) (q + t) := by
  intro m
  rw [coeff_add, coeff_add]
  exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add (hp m) (hr m))

theorem neg (hp : NaturalMajorizes p q) : NaturalMajorizes (-p) q := by
  intro m
  simpa only [coeff_neg, Int.natAbs_neg] using hp m

theorem sub (hp : NaturalMajorizes p q) (hr : NaturalMajorizes r t) :
    NaturalMajorizes (p - r) (q + t) := by
  simpa only [sub_eq_add_neg] using hp.add hr.neg

theorem mul (hp : NaturalMajorizes p q) (hr : NaturalMajorizes r t) :
    NaturalMajorizes (p * r) (q * t) := by
  classical
  intro m
  rw [coeff_mul, coeff_mul]
  apply (Int.natAbs_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul (hp a.1) (hr a.2)

theorem pow (hp : NaturalMajorizes p q) (n : ℕ) : NaturalMajorizes (p ^ n) (q ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (one (σ := σ))
  | succ n ih => simpa only [pow_succ] using ih.mul hp

theorem sum {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial σ ℤ) (q : ι → MvPolynomial σ ℕ)
    (h : ∀ i ∈ s, NaturalMajorizes (p i) (q i)) :
    NaturalMajorizes (∑ i ∈ s, p i) (∑ i ∈ s, q i) := by
  intro m
  rw [coeff_sum, coeff_sum]
  exact (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => h i hi m))

theorem prod {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial σ ℤ) (q : ι → MvPolynomial σ ℕ)
    (h : ∀ i ∈ s, NaturalMajorizes (p i) (q i)) :
    NaturalMajorizes (∏ i ∈ s, p i) (∏ i ∈ s, q i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [Finset.prod_empty] using (one (σ := σ))
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end NaturalMajorizes

/-- The sum of all coefficients of a nonnegative-coefficient majorant. -/
def naturalCoefficientMass {σ : Type*} : MvPolynomial σ ℕ →+* ℕ :=
  MvPolynomial.eval (fun _ => 1)

theorem naturalCoefficientMass_eq_sum {σ : Type*} (q : MvPolynomial σ ℕ) :
    naturalCoefficientMass q = ∑ m ∈ q.support, coeff m q := by
  simp [naturalCoefficientMass, MvPolynomial.eval_eq]

theorem coefficient_le_naturalCoefficientMass {σ : Type*}
    (q : MvPolynomial σ ℕ) (m : σ →₀ ℕ) : coeff m q ≤ naturalCoefficientMass q := by
  classical
  rw [naturalCoefficientMass_eq_sum]
  by_cases hm : m ∈ q.support
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm
  · rw [notMem_support_iff.mp hm]
    exact Nat.zero_le _

/-- A proved finite majorant certificate, not a premise in the physical model. -/
def CoefficientMassLE {σ : Type*} (p : MvPolynomial σ ℤ) (H : ℕ) : Prop :=
  ∃ q : MvPolynomial σ ℕ, NaturalMajorizes p q ∧ naturalCoefficientMass q ≤ H

namespace CoefficientMassLE

variable {σ : Type*} {p r : MvPolynomial σ ℤ} {H G : ℕ}

theorem coefficient_natAbs_le (hp : CoefficientMassLE p H) (m : σ →₀ ℕ) :
    (coeff m p).natAbs ≤ H := by
  rcases hp with ⟨q, hq, hmass⟩
  exact (hq m).trans ((coefficient_le_naturalCoefficientMass q m).trans hmass)

theorem mono (hp : CoefficientMassLE p H) (h : H ≤ G) : CoefficientMassLE p G := by
  rcases hp with ⟨q, hq, hmass⟩
  exact ⟨q, hq, hmass.trans h⟩

theorem zero (H : ℕ) : CoefficientMassLE (0 : MvPolynomial σ ℤ) H :=
  ⟨0, NaturalMajorizes.zero _, by simp⟩

theorem one : CoefficientMassLE (1 : MvPolynomial σ ℤ) 1 :=
  ⟨1, NaturalMajorizes.one, by simp⟩

theorem constant (a : ℤ) : CoefficientMassLE (C a : MvPolynomial σ ℤ) a.natAbs :=
  ⟨C a.natAbs, NaturalMajorizes.constant le_rfl, by simp [naturalCoefficientMass]⟩

theorem variablePolynomial (i : σ) : CoefficientMassLE (X i : MvPolynomial σ ℤ) 1 :=
  ⟨X i, NaturalMajorizes.variablePolynomial _, by simp [naturalCoefficientMass]⟩

theorem add (hp : CoefficientMassLE p H) (hr : CoefficientMassLE r G) :
    CoefficientMassLE (p + r) (H + G) := by
  rcases hp with ⟨q, hq, hqm⟩
  rcases hr with ⟨t, ht, htm⟩
  refine ⟨q + t, hq.add ht, ?_⟩
  rw [map_add]
  exact Nat.add_le_add hqm htm

theorem neg (hp : CoefficientMassLE p H) : CoefficientMassLE (-p) H := by
  rcases hp with ⟨q, hq, hqm⟩
  exact ⟨q, hq.neg, hqm⟩

theorem sub (hp : CoefficientMassLE p H) (hr : CoefficientMassLE r G) :
    CoefficientMassLE (p - r) (H + G) := by
  simpa only [sub_eq_add_neg] using hp.add hr.neg

theorem mul (hp : CoefficientMassLE p H) (hr : CoefficientMassLE r G) :
    CoefficientMassLE (p * r) (H * G) := by
  rcases hp with ⟨q, hq, hqm⟩
  rcases hr with ⟨t, ht, htm⟩
  refine ⟨q * t, hq.mul ht, ?_⟩
  rw [map_mul]
  exact Nat.mul_le_mul hqm htm

theorem pow (hp : CoefficientMassLE p H) (n : ℕ) : CoefficientMassLE (p ^ n) (H ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (one (σ := σ))
  | succ n ih => simpa only [pow_succ] using ih.mul hp

theorem finiteSum {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℤ) (H : ι → ℕ) (hp : ∀ i, CoefficientMassLE (p i) (H i)) :
    CoefficientMassLE (∑ i, p i) (∑ i, H i) := by
  classical
  choose q hq hqm using hp
  refine ⟨∑ i, q i, NaturalMajorizes.sum _ _ _ (fun i _ => hq i), ?_⟩
  rw [map_sum]
  exact Finset.sum_le_sum (fun i _ => hqm i)

theorem sum_uniform {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℤ) (hp : ∀ i, CoefficientMassLE (p i) H) :
    CoefficientMassLE (∑ i, p i) (Fintype.card ι * H) := by
  simpa using finiteSum p (fun _ => H) hp

end CoefficientMassLE

theorem NaturalMajorizes.support_subset {σ : Type*}
    {p : MvPolynomial σ ℤ} {q : MvPolynomial σ ℕ} (hp : NaturalMajorizes p q) :
    p.support ⊆ q.support := by
  intro m hm
  rw [mem_support_iff] at hm ⊢
  intro hq
  have hzero : (coeff m p).natAbs = 0 := Nat.eq_zero_of_le_zero (by simpa [hq] using hp m)
  exact hm (Int.natAbs_eq_zero.mp hzero)

/-- Nonnegative polynomial substitution preserves coefficient
majorization; no rational-preservation contract is assumed. -/
theorem NaturalMajorizes.bind₁ {σ τ : Type*}
    {p : MvPolynomial σ ℤ} {q : MvPolynomial σ ℕ} (hp : NaturalMajorizes p q)
    (f : σ → MvPolynomial τ ℤ) (g : σ → MvPolynomial τ ℕ)
    (hfg : ∀ i, NaturalMajorizes (f i) (g i)) :
    NaturalMajorizes (MvPolynomial.bind₁ f p) (MvPolynomial.bind₁ g q) := by
  classical
  have hpexp : p = ∑ m ∈ q.support, monomial m (coeff m p) := by
    calc
      p = ∑ m ∈ p.support, monomial m (coeff m p) := p.as_sum
      _ = ∑ m ∈ q.support, monomial m (coeff m p) :=
        Finset.sum_subset hp.support_subset (fun m _ hm => by simp [notMem_support_iff.mp hm])
  have hpb : MvPolynomial.bind₁ f p =
      ∑ m ∈ q.support, MvPolynomial.bind₁ f (monomial m (coeff m p)) := by
    conv_lhs => rw [hpexp]
    rw [map_sum]
  have hqb : MvPolynomial.bind₁ g q =
      ∑ m ∈ q.support, MvPolynomial.bind₁ g (monomial m (coeff m q)) := by
    conv_lhs => rw [q.as_sum]
    rw [map_sum]
  rw [hpb, hqb]
  apply NaturalMajorizes.sum
  intro m _
  simp only [MvPolynomial.bind₁, aeval_monomial, algebraMap_eq]
  apply (NaturalMajorizes.constant (hp m)).mul
  change NaturalMajorizes (∏ i ∈ m.support, f i ^ m i) (∏ i ∈ m.support, g i ^ m i)
  exact NaturalMajorizes.prod _ _ _ (fun i _ => (hfg i).pow _)

theorem naturalCoefficientMass_bind₁_le {σ τ : Type*}
    (g : σ → MvPolynomial τ ℕ) (hg : ∀ i, naturalCoefficientMass (g i) ≤ 1)
    (q : MvPolynomial σ ℕ) :
    naturalCoefficientMass (MvPolynomial.bind₁ g q) ≤ naturalCoefficientMass q := by
  classical
  change eval₂Hom (RingHom.id ℕ) (fun _ : τ => 1) (MvPolynomial.bind₁ g q) ≤ _
  rw [eval₂Hom_bind₁]
  change MvPolynomial.eval (fun i => naturalCoefficientMass (g i)) q ≤
    MvPolynomial.eval (fun _ => 1) q
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  simp only [one_pow, Finset.prod_const_one, mul_one]
  apply Finset.sum_le_sum
  intro m _
  have hprod : (∏ i ∈ m.support, naturalCoefficientMass (g i) ^ m i) ≤ 1 := by
    calc
      _ ≤ ∏ _i ∈ m.support, (1 : ℕ) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          (fun i _ => by simpa using Nat.pow_le_pow_left (hg i) (m i))
      _ = 1 := by simp
  simpa using Nat.mul_le_mul_left (coeff m q) hprod

theorem CoefficientMassLE.bind₁ {σ τ : Type*} {p : MvPolynomial σ ℤ} {H : ℕ}
    (hp : CoefficientMassLE p H) (f : σ → MvPolynomial τ ℤ)
    (hf : ∀ i, CoefficientMassLE (f i) 1) :
    CoefficientMassLE (MvPolynomial.bind₁ f p) H := by
  classical
  rcases hp with ⟨q, hq, hqm⟩
  choose g hfg hgm using hf
  exact ⟨MvPolynomial.bind₁ g q, hq.bind₁ f g hfg,
    (naturalCoefficientMass_bind₁_le g hgm q).trans hqm⟩

theorem CoefficientMassLE.coefficient_realAbs_le {σ : Type*}
    {p : MvPolynomial σ ℤ} {H : ℕ} (hp : CoefficientMassLE p H) (m : σ →₀ ℕ) :
    |((coeff m p : ℤ) : ℝ)| ≤ (H : ℝ) := by
  have h : ((coeff m p).natAbs : ℝ) ≤ (H : ℝ) :=
    Nat.cast_le.mpr (hp.coefficient_natAbs_le m)
  simpa only [Nat.cast_natAbs, Int.cast_abs] using h

theorem unitResourceConstraint_massLE {σ ε : Type*} [Fintype ε]
    (entry : ε × Fin 2 → σ) :
    CoefficientMassLE (unitResourceConstraint entry) (2 * Fintype.card ε + 1) := by
  have hterm : ∀ e : ε, CoefficientMassLE
      ((X (entry (e, 0))) ^ 2 + (X (entry (e, 1))) ^ 2 : MvPolynomial σ ℤ) 2 := by
    intro e
    simpa using ((CoefficientMassLE.variablePolynomial _).pow 2).add
      ((CoefficientMassLE.variablePolynomial _).pow 2)
  simpa only [unitResourceConstraint, Nat.mul_comm] using
    (CoefficientMassLE.sum_uniform _ hterm).sub CoefficientMassLE.one

theorem isometryRealConstraint_massLE {σ m n : Type*} [Fintype m] [DecidableEq n]
    (entry : (m × n) × Fin 2 → σ) (i j : n) :
    CoefficientMassLE (isometryRealConstraint entry i j) (2 * Fintype.card m + 1) := by
  have hterm : ∀ k : m, CoefficientMassLE
      (X (entry ((k, i), 0)) * X (entry ((k, j), 0)) +
        X (entry ((k, i), 1)) * X (entry ((k, j), 1))) 2 := by
    intro k
    simpa using ((CoefficientMassLE.variablePolynomial _).mul
      (CoefficientMassLE.variablePolynomial _)).add
        ((CoefficientMassLE.variablePolynomial _).mul (CoefficientMassLE.variablePolynomial _))
  have hdiag : CoefficientMassLE (if i = j then (1 : MvPolynomial σ ℤ) else 0) 1 := by
    split
    · exact CoefficientMassLE.one
    · exact CoefficientMassLE.zero _
  simpa only [isometryRealConstraint, Nat.mul_comm] using
    (CoefficientMassLE.sum_uniform _ hterm).sub hdiag

theorem isometryImagConstraint_massLE {σ m n : Type*} [Fintype m]
    (entry : (m × n) × Fin 2 → σ) (i j : n) :
    CoefficientMassLE (isometryImagConstraint entry i j) (2 * Fintype.card m) := by
  have hterm : ∀ k : m, CoefficientMassLE
      (X (entry ((k, i), 0)) * X (entry ((k, j), 1)) -
        X (entry ((k, i), 1)) * X (entry ((k, j), 0))) 2 := by
    intro k
    simpa using ((CoefficientMassLE.variablePolynomial _).mul
      (CoefficientMassLE.variablePolynomial _)).sub
        ((CoefficientMassLE.variablePolynomial _).mul (CoefficientMassLE.variablePolynomial _))
  simpa only [isometryImagConstraint, Nat.mul_comm] using CoefficientMassLE.sum_uniform _ hterm

theorem isometryPartConstraint_massLE {σ m n : Type*} [Fintype m] [DecidableEq n]
    (entry : (m × n) × Fin 2 → σ) (q : (n × n) × Fin 2) :
    CoefficientMassLE (isometryPartConstraint entry q) (2 * Fintype.card m + 1) := by
  unfold isometryPartConstraint
  split
  · exact isometryRealConstraint_massLE _ _ _
  · exact (isometryImagConstraint_massLE _ _ _).mono (Nat.le_add_right _ _)

/-- A literal dimension box gives coefficient height, not a quadratic
variable-count assertion. The latter uses the separate sharp charged shapes. -/
theorem physicalConstraintPolynomial_massLE {K : ℕ} (hK : 1 ≤ K)
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) (q : PhysicalConstraintIndex 2 s) :
    CoefficientMassLE (physicalConstraintPolynomial 2 s q) (5 * K ^ 2) := by
  have hKsq : 1 ≤ K ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hK hK
  have hKK : K ≤ K ^ 2 := by simpa [pow_two] using Nat.mul_le_mul_left K hK
  have hprod (i j : Fin 8) : s i * s j ≤ K ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul (hs i) (hs j)
  rcases q with q | q | q | q | q
  · apply (unitResourceConstraint_massLE (resourceCoordinates 2 s)).mono
    simp only [ResourceEntryIndex, Fintype.card_prod, Fintype.card_fin]
    have := hprod 0 1
    omega
  · apply (isometryPartConstraint_massLE (encoderACoordinates 2 s) q).mono
    simp only [Fintype.card_prod, Fintype.card_fin]
    have := hprod 2 4
    omega
  · apply (isometryPartConstraint_massLE (encoderBCoordinates 2 s) q).mono
    simp only [Fintype.card_prod, Fintype.card_fin]
    have := hprod 3 5
    omega
  · apply (isometryPartConstraint_massLE (decoderACoordinates 2 s) q).mono
    simp only [Fintype.card_prod, Fintype.card_fin]
    have := hs 6
    omega
  · apply (isometryPartConstraint_massLE (decoderBCoordinates 2 s) q).mono
    simp only [Fintype.card_prod, Fintype.card_fin]
    have := hs 7
    omega

theorem card_physicalConstraintIndex_qubit (s : Fin 8 → ℕ) :
    Fintype.card (PhysicalConstraintIndex 2 s) =
      1 + 8 * (s 0) ^ 2 + 8 * (s 1) ^ 2 +
        2 * (s 2 * s 5) ^ 2 + 2 * (s 3 * s 4) ^ 2 := by
  simp only [PhysicalConstraintIndex, EncoderAInputIndex, EncoderBInputIndex,
    DecoderAInputIndex, DecoderBInputIndex, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_unit]
  ring

theorem card_physicalConstraintIndex_le {K : ℕ} (hK : 1 ≤ K)
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) :
    Fintype.card (PhysicalConstraintIndex 2 s) ≤ 21 * K ^ 4 := by
  have hKsq : 1 ≤ K ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hK hK
  have h24 : K ^ 2 ≤ K ^ 4 := by
    have h := Nat.mul_le_mul_left (K ^ 2) hKsq
    nlinarith
  have h0 := (Nat.pow_le_pow_left (hs 0) 2).trans h24
  have h1 := (Nat.pow_le_pow_left (hs 1) 2).trans h24
  have hprod (i j : Fin 8) : (s i * s j) ^ 2 ≤ K ^ 4 := by
    have h := Nat.pow_le_pow_left (Nat.mul_le_mul (hs i) (hs j)) 2
    exact h.trans_eq (by ring)
  rw [card_physicalConstraintIndex_qubit]
  have := hprod 2 5
  have := hprod 3 4
  omega

theorem physicalConstraintSumSquares_massLE {K : ℕ} (hK : 1 ≤ K)
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) :
    CoefficientMassLE (physicalConstraintSumSquares 2 s) (525 * K ^ 8) := by
  have h := CoefficientMassLE.sum_uniform _
    (fun q => (physicalConstraintPolynomial_massLE hK s hs q).pow 2)
  change CoefficientMassLE (physicalConstraintSumSquares 2 s)
    (Fintype.card (PhysicalConstraintIndex 2 s) * (5 * K ^ 2) ^ 2) at h
  apply h.mono
  calc
    _ ≤ (21 * K ^ 4) * (5 * K ^ 2) ^ 2 :=
      Nat.mul_le_mul_right _ (card_physicalConstraintIndex_le hK s hs)
    _ = 525 * K ^ 8 := by ring

theorem physicalConstraintPolynomial_coefficient_natAbs_le {K : ℕ} (hK : 1 ≤ K)
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) (q : PhysicalConstraintIndex 2 s)
    (m : PhysicalCoordinateIndex 2 s →₀ ℕ) :
    (coeff m (physicalConstraintPolynomial 2 s q)).natAbs ≤ 5 * K ^ 2 :=
  (physicalConstraintPolynomial_massLE hK s hs q).coefficient_natAbs_le m

theorem physicalConstraintSumSquares_coefficient_natAbs_le {K : ℕ} (hK : 1 ≤ K)
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) (m : PhysicalCoordinateIndex 2 s →₀ ℕ) :
    (coeff m (physicalConstraintSumSquares 2 s)).natAbs ≤ 525 * K ^ 8 :=
  (physicalConstraintSumSquares_massLE hK s hs).coefficient_natAbs_le m

theorem physicalConstraintPolynomial_coefficient_realAbs_le {K : ℕ} (hK : 1 ≤ K)
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) (q : PhysicalConstraintIndex 2 s)
    (m : PhysicalCoordinateIndex 2 s →₀ ℕ) :
    |((coeff m (physicalConstraintPolynomial 2 s q) : ℤ) : ℝ)| ≤ (5 * K ^ 2 : ℕ) :=
  (physicalConstraintPolynomial_massLE hK s hs q).coefficient_realAbs_le m

theorem physicalConstraintSumSquares_coefficient_realAbs_le {K : ℕ} (hK : 1 ≤ K)
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) (m : PhysicalCoordinateIndex 2 s →₀ ℕ) :
    |((coeff m (physicalConstraintSumSquares 2 s) : ℤ) : ℝ)| ≤ (525 * K ^ 8 : ℕ) :=
  (physicalConstraintSumSquares_massLE hK s hs).coefficient_realAbs_le m

namespace ComplexPair

/-- A coefficient-mass bound for each real and imaginary polynomial. -/
def MassLE {σ : Type*} (H : ℕ) (p : ComplexPair σ) : Prop :=
  CoefficientMassLE p.1 H ∧ CoefficientMassLE p.2 H

theorem mass_mono {σ : Type*} {H G : ℕ} {p : ComplexPair σ}
    (hp : MassLE H p) (h : H ≤ G) : MassLE G p :=
  ⟨hp.1.mono h, hp.2.mono h⟩

theorem mass_coordinatePair {σ : Type*} (re im : σ) :
    MassLE 1 (coordinatePair re im) :=
  ⟨CoefficientMassLE.variablePolynomial _, CoefficientMassLE.variablePolynomial _⟩

theorem mass_zero {σ : Type*} (H : ℕ) : MassLE H ((0, 0) : ComplexPair σ) :=
  ⟨CoefficientMassLE.zero _, CoefficientMassLE.zero _⟩

theorem mass_multiply {σ : Type*} {H G : ℕ} {p q : ComplexPair σ}
    (hp : MassLE H p) (hq : MassLE G q) : MassLE (2 * H * G) (multiply p q) := by
  have h : H * G + H * G ≤ 2 * H * G := le_of_eq (by ring)
  exact ⟨((hp.1.mul hq.1).sub (hp.2.mul hq.2)).mono h,
    ((hp.1.mul hq.2).add (hp.2.mul hq.1)).mono h⟩

theorem mass_conjugate {σ : Type*} {H : ℕ} {p : ComplexPair σ}
    (hp : MassLE H p) : MassLE H (conjugate p) := ⟨hp.1, hp.2.neg⟩

theorem mass_sum {σ ε : Type*} [Fintype ε] {H : ℕ}
    (p : ε → ComplexPair σ) (hp : ∀ e, MassLE H (p e)) :
    MassLE (Fintype.card ε * H) (sum p) :=
  ⟨CoefficientMassLE.sum_uniform _ (fun e => (hp e).1),
    CoefficientMassLE.sum_uniform _ (fun e => (hp e).2)⟩

theorem mass_normSquare {σ : Type*} {H : ℕ} {p : ComplexPair σ}
    (hp : MassLE H p) : CoefficientMassLE (normSquare p) (2 * H ^ 2) := by
  simpa only [normSquare, two_mul] using (hp.1.pow 2).add (hp.2.pow 2)

theorem mass_matrixVariable {σ m n : Type*} (entry : (m × n) × Fin 2 → σ) :
    ∀ i j, MassLE 1 (matrixVariable entry i j) :=
  fun _ _ => mass_coordinatePair _ _

theorem mass_matrixKronecker {σ m n k l : Type*} {H G : ℕ}
    (P : Matrix m n (ComplexPair σ)) (Q : Matrix k l (ComplexPair σ))
    (hP : ∀ i j, MassLE H (P i j)) (hQ : ∀ i j, MassLE G (Q i j)) :
    ∀ i j, MassLE (2 * H * G) (matrixKronecker P Q i j) :=
  fun i j => mass_multiply (hP i.1 j.1) (hQ i.2 j.2)

theorem mass_matrixMultiply {σ m n k : Type*} [Fintype n] {H G : ℕ}
    (P : Matrix m n (ComplexPair σ)) (Q : Matrix n k (ComplexPair σ))
    (hP : ∀ i j, MassLE H (P i j)) (hQ : ∀ i j, MassLE G (Q i j)) :
    ∀ i j, MassLE (Fintype.card n * (2 * H * G)) (matrixMultiply P Q i j) :=
  fun i j => mass_sum _ (fun q => mass_multiply (hP i q) (hQ q j))

theorem mass_resourceInsert {σ ιA ιB ρA ρB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] (entry : (ρA × ρB) × Fin 2 → σ) :
    ∀ i j, MassLE 1 (resourceInsert (ιA := ιA) (ιB := ιB) entry i j) := by
  intro i j
  dsimp only [resourceInsert, Matrix.of_apply]
  split
  · exact mass_coordinatePair _ _
  · exact mass_zero _

end ComplexPair

/-- Entrywise majorants for the five-block global matrix. The bound
uses the production exchange and regrouping; neither changes coefficients. -/
theorem physicalGlobalPolynomial_massLE {K : ℕ}
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) :
    ∀ i j, ComplexPair.MassLE (64 * K ^ 6) (physicalGlobalPolynomial 2 s i j) := by
  let VA := ComplexPair.matrixVariable (liftPhysicalScoreCoordinates (encoderACoordinates 2 s))
  let VB := ComplexPair.matrixVariable (liftPhysicalScoreCoordinates (encoderBCoordinates 2 s))
  let DA := ComplexPair.matrixVariable (liftPhysicalScoreCoordinates (decoderACoordinates 2 s))
  let DB := ComplexPair.matrixVariable (liftPhysicalScoreCoordinates (decoderBCoordinates 2 s))
  let J := ComplexPair.resourceInsert (ιA := Fin 2) (ιB := Fin 2)
    (liftPhysicalScoreCoordinates (resourceCoordinates 2 s))
  have hprod (i j : Fin 8) : s i * s j ≤ K ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul (hs i) (hs j)
  have hencBase := ComplexPair.mass_matrixMultiply _ _
    (ComplexPair.mass_matrixKronecker VA VB (ComplexPair.mass_matrixVariable _)
      (ComplexPair.mass_matrixVariable _)) (ComplexPair.mass_resourceInsert
        (ιA := Fin 2) (ιB := Fin 2) (liftPhysicalScoreCoordinates (resourceCoordinates 2 s)))
  have henc : ∀ i j, ComplexPair.MassLE (16 * K ^ 2)
      (ComplexPair.matrixMultiply (ComplexPair.matrixKronecker VA VB) J i j) := by
    intro i j
    apply ComplexPair.mass_mono (hencBase i j)
    simp only [EncoderAInputIndex, EncoderBInputIndex, Fintype.card_prod, Fintype.card_fin]
    calc
      _ = 16 * (s 0 * s 1) := by ring
      _ ≤ 16 * K ^ 2 := Nat.mul_le_mul_left 16 (hprod 0 1)
  have hdec : ∀ i j, ComplexPair.MassLE 2 (ComplexPair.matrixKronecker DA DB i j) := by
    simpa using ComplexPair.mass_matrixKronecker DA DB (ComplexPair.mass_matrixVariable _)
      (ComplexPair.mass_matrixVariable _)
  have hinner : (s 2 * s 5) * (s 3 * s 4) ≤ K ^ 4 := by
    calc
      _ ≤ (K ^ 2) * (K ^ 2) := Nat.mul_le_mul (hprod 2 5) (hprod 3 4)
      _ = K ^ 4 := by ring
  have hglobal : ∀ i j, ComplexPair.MassLE (64 * K ^ 6)
      (ComplexPair.matrixMultiply (ComplexPair.matrixKronecker DA DB)
        ((ComplexPair.matrixMultiply (ComplexPair.matrixKronecker VA VB) J).submatrix
          (exchangeEquiv (Fin (s 2)) (Fin (s 4)) (Fin (s 3)) (Fin (s 5))) id) i j) := by
    intro i j
    apply ComplexPair.mass_mono (ComplexPair.mass_matrixMultiply _ _ hdec
      (fun a b => henc
        (exchangeEquiv (Fin (s 2)) (Fin (s 4)) (Fin (s 3)) (Fin (s 5)) a) b) i j)
    simp only [DecoderAInputIndex, DecoderBInputIndex, Fintype.card_prod, Fintype.card_fin]
    calc
      _ = ((s 2 * s 5) * (s 3 * s 4)) * (64 * K ^ 2) := by ring
      _ ≤ K ^ 4 * (64 * K ^ 2) := Nat.mul_le_mul_right _ hinner
      _ = 64 * K ^ 6 := by ring
  exact fun i j => hglobal
    (outputRegroup (Fin 2) (Fin 2) (Fin (s 6)) (Fin (s 7)) i) j

theorem physicalOverlapPolynomial_massLE {K : ℕ}
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) (e : PhysicalEnvironmentIndex s) :
    ComplexPair.MassLE (2048 * K ^ 6) (physicalOverlapPolynomial 2 s e) := by
  have hterm : ∀ p : LogicalIndex 2 × LogicalIndex 2, ComplexPair.MassLE (2 * 1 * (64 * K ^ 6))
      (ComplexPair.multiply
        (ComplexPair.conjugate (ComplexPair.matrixVariable (targetScoreCoordinates 2 s) p.1 p.2))
        (physicalGlobalPolynomial 2 s (p.1, e) p.2)) := fun p =>
    ComplexPair.mass_multiply
      (ComplexPair.mass_conjugate (ComplexPair.mass_matrixVariable _ p.1 p.2))
      (physicalGlobalPolynomial_massLE s hs (p.1, e) p.2)
  unfold physicalOverlapPolynomial
  apply ComplexPair.mass_mono (ComplexPair.mass_sum _ hterm)
  simp only [LogicalIndex, Fintype.card_prod, Fintype.card_fin]
  exact le_of_eq (by ring)

/-- A coarse explicit coefficient mass for the variable-target qubit
score polynomial. Target variables remain distinct from physical variables. -/
theorem physicalScoreNumeratorPolynomial_massLE {K : ℕ}
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) :
    CoefficientMassLE (physicalScoreNumeratorPolynomial 2 s) (2 ^ 23 * K ^ 14) := by
  have h := CoefficientMassLE.sum_uniform _ (fun e =>
    ComplexPair.mass_normSquare (physicalOverlapPolynomial_massLE s hs e))
  change CoefficientMassLE (physicalScoreNumeratorPolynomial 2 s)
    (Fintype.card (PhysicalEnvironmentIndex s) * (2 * (2048 * K ^ 6) ^ 2)) at h
  apply h.mono
  simp only [PhysicalEnvironmentIndex, Fintype.card_prod, Fintype.card_fin]
  have henv : s 6 * s 7 ≤ K ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul (hs 6) (hs 7)
  calc
    _ ≤ K ^ 2 * (2 * (2048 * K ^ 6) ^ 2) := Nat.mul_le_mul_right _ henv
    _ = 2 ^ 23 * K ^ 14 := by ring

theorem phaseScoreSubstitution_massLE (s : Fin 8 → ℕ)
    (q : PhysicalScoreCoordinateIndex 2 s) :
    CoefficientMassLE (phaseScoreSubstitution s q) 1 := by
  rcases q with q | q
  · dsimp [phaseScoreSubstitution]
    split_ifs
    · exact CoefficientMassLE.variablePolynomial _
    · exact CoefficientMassLE.one
    · exact CoefficientMassLE.zero _
    · exact CoefficientMassLE.zero _
  · exact CoefficientMassLE.variablePolynomial _

/-- Integer coefficient heights for the two-parameter phase target.
The literal box `s i ≤ K` is explicit; it is not a charged-footprint premise. -/
theorem controlledPhaseScoreNumeratorPolynomial_massLE {K : ℕ}
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) :
    CoefficientMassLE (controlledPhaseScoreNumeratorPolynomial s) (2 ^ 23 * K ^ 14) :=
  (physicalScoreNumeratorPolynomial_massLE s hs).bind₁ _ (phaseScoreSubstitution_massLE s)

theorem controlledPhaseScoreNumeratorPolynomial_coefficient_natAbs_le {K : ℕ}
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) (m : PhaseScoreCoordinateIndex s →₀ ℕ) :
    (coeff m (controlledPhaseScoreNumeratorPolynomial s)).natAbs ≤ 2 ^ 23 * K ^ 14 :=
  (controlledPhaseScoreNumeratorPolynomial_massLE s hs).coefficient_natAbs_le m

theorem controlledPhaseScoreNumeratorPolynomial_coefficient_realAbs_le {K : ℕ}
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) (m : PhaseScoreCoordinateIndex s →₀ ℕ) :
    |((coeff m (controlledPhaseScoreNumeratorPolynomial s) : ℤ) : ℝ)| ≤
      (2 ^ 23 * K ^ 14 : ℕ) :=
  (controlledPhaseScoreNumeratorPolynomial_massLE s hs).coefficient_realAbs_le m

/-- An explicit linear-in-`K` binary height witness for a polynomial mass
bound. This coarse conversion avoids any logarithmic-height premise. -/
theorem CoefficientMassLE.binary_bound {σ : Type*} {p : MvPolynomial σ ℤ}
    {A a b K : ℕ} (hp : CoefficientMassLE p (A * K ^ b)) (hA : A ≤ 2 ^ a) :
    CoefficientMassLE p (2 ^ (a + b * K)) := by
  apply hp.mono
  calc
    A * K ^ b ≤ 2 ^ a * (2 ^ K) ^ b :=
      Nat.mul_le_mul hA (Nat.pow_le_pow_left (Nat.le_of_lt K.lt_two_pow_self) b)
    _ = 2 ^ (a + b * K) := by
      rw [← pow_mul, ← pow_add, Nat.mul_comm K b]

theorem physicalConstraintPolynomial_binary_massLE {K : ℕ} (hK : 1 ≤ K)
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) (q : PhysicalConstraintIndex 2 s) :
    CoefficientMassLE (physicalConstraintPolynomial 2 s q) (2 ^ (3 + 2 * K)) :=
  (physicalConstraintPolynomial_massLE hK s hs q).binary_bound (by decide : 5 ≤ 2 ^ 3)

theorem physicalConstraintSumSquares_binary_massLE {K : ℕ} (hK : 1 ≤ K)
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) :
    CoefficientMassLE (physicalConstraintSumSquares 2 s) (2 ^ (10 + 8 * K)) :=
  (physicalConstraintSumSquares_massLE hK s hs).binary_bound (by decide : 525 ≤ 2 ^ 10)

theorem controlledPhaseScoreNumeratorPolynomial_binary_massLE {K : ℕ}
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ K) :
    CoefficientMassLE (controlledPhaseScoreNumeratorPolynomial s) (2 ^ (23 + 14 * K)) :=
  (controlledPhaseScoreNumeratorPolynomial_massLE s hs).binary_bound le_rfl

/-- Applicability to a fourfold dimension box is explicit. No implication
from an abstract quantum footprint to this box is asserted here. -/
theorem physicalConstraintPolynomial_massLE_of_four_mul_box {K : ℕ} (hK : 1 ≤ K)
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ 4 * K) (q : PhysicalConstraintIndex 2 s) :
    CoefficientMassLE (physicalConstraintPolynomial 2 s q) (80 * K ^ 2) := by
  have h4 : 1 ≤ 4 * K := by omega
  apply (physicalConstraintPolynomial_massLE h4 s hs q).mono
  exact le_of_eq (by ring)

theorem physicalConstraintSumSquares_massLE_of_four_mul_box {K : ℕ} (hK : 1 ≤ K)
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ 4 * K) :
    CoefficientMassLE (physicalConstraintSumSquares 2 s) (34406400 * K ^ 8) := by
  have h4 : 1 ≤ 4 * K := by omega
  apply (physicalConstraintSumSquares_massLE h4 s hs).mono
  exact le_of_eq (by ring)

theorem controlledPhaseScoreNumeratorPolynomial_massLE_of_four_mul_box {K : ℕ}
    (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ 4 * K) :
    CoefficientMassLE (controlledPhaseScoreNumeratorPolynomial s) (2 ^ 51 * K ^ 14) := by
  apply (controlledPhaseScoreNumeratorPolynomial_massLE s hs).mono
  exact le_of_eq (by ring)

theorem controlledPhaseScoreNumeratorPolynomial_coefficient_natAbs_le_of_four_mul_box
    {K : ℕ} (s : Fin 8 → ℕ) (hs : ∀ i, s i ≤ 4 * K)
    (m : PhaseScoreCoordinateIndex s →₀ ℕ) :
    (coeff m (controlledPhaseScoreNumeratorPolynomial s)).natAbs ≤ 2 ^ 51 * K ^ 14 :=
  (controlledPhaseScoreNumeratorPolynomial_massLE_of_four_mul_box s hs).coefficient_natAbs_le m

end NLQCLean.PhysicalPolynomial

end
