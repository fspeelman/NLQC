import NLQCLean.Arithmetic.TranscriptPolynomial
import NLQCLean.Arithmetic.PhysicalPolynomialHeight

/-!
# Coefficient heights and coordinate count of the transcript family

If every block dimension is at most `4Q` and both outcome counts are at most `4Q²`, then every
coefficient of the constraint sum of squares and of the score numerator has absolute value at
most `2⁵⁵ Q¹⁸`. For the shapes produced by the transcript representative
(`kA ≤ 2ra`, `eA ≤ 2 kA b`, outcome counts at most `4r²`) the family has at most `1090 r⁴ q²`
real coordinates, `q = rab` (`eq:explicit-quantum-variables`).
-/

namespace NLQCLean.TranscriptPolynomial

open MvPolynomial PhysicalPolynomial

theorem instrumentRealConstraint_massLE {σ ξ m n : Type*} [Fintype ξ] [Fintype m]
    [DecidableEq n] (entry : ξ → (m × n) × Fin 2 → σ) (i j : n) :
    CoefficientMassLE (instrumentRealConstraint entry i j)
      (Fintype.card ξ * (Fintype.card m * 2) + 1) := by
  have hterm : ∀ (x : ξ) (k : m), CoefficientMassLE
      (X (entry x ((k, i), 0)) * X (entry x ((k, j), 0)) +
        X (entry x ((k, i), 1)) * X (entry x ((k, j), 1))) 2 := by
    intro x k
    simpa using ((CoefficientMassLE.variablePolynomial _).mul
      (CoefficientMassLE.variablePolynomial _)).add
        ((CoefficientMassLE.variablePolynomial _).mul (CoefficientMassLE.variablePolynomial _))
  have hdiag : CoefficientMassLE (if i = j then (1 : MvPolynomial σ ℤ) else 0) 1 := by
    split
    · exact CoefficientMassLE.one
    · exact CoefficientMassLE.zero _
  exact (CoefficientMassLE.sum_uniform _ fun x =>
    CoefficientMassLE.sum_uniform _ (hterm x)).sub hdiag

theorem instrumentImagConstraint_massLE {σ ξ m n : Type*} [Fintype ξ] [Fintype m]
    (entry : ξ → (m × n) × Fin 2 → σ) (i j : n) :
    CoefficientMassLE (instrumentImagConstraint entry i j)
      (Fintype.card ξ * (Fintype.card m * 2)) := by
  have hterm : ∀ (x : ξ) (k : m), CoefficientMassLE
      (X (entry x ((k, i), 0)) * X (entry x ((k, j), 1)) -
        X (entry x ((k, i), 1)) * X (entry x ((k, j), 0))) 2 := by
    intro x k
    simpa using ((CoefficientMassLE.variablePolynomial _).mul
      (CoefficientMassLE.variablePolynomial _)).sub
        ((CoefficientMassLE.variablePolynomial _).mul (CoefficientMassLE.variablePolynomial _))
  exact CoefficientMassLE.sum_uniform _ fun x => CoefficientMassLE.sum_uniform _ (hterm x)

theorem instrumentPartConstraint_massLE {σ ξ m n : Type*} [Fintype ξ] [Fintype m]
    [DecidableEq n] (entry : ξ → (m × n) × Fin 2 → σ) (q : (n × n) × Fin 2) :
    CoefficientMassLE (instrumentPartConstraint entry q)
      (Fintype.card ξ * (Fintype.card m * 2) + 1) := by
  unfold instrumentPartConstraint
  split
  · exact instrumentRealConstraint_massLE _ _ _
  · exact (instrumentImagConstraint_massLE _ _ _).mono (Nat.le_add_right _ _)

variable {s : Fin 8 → ℕ} {nA nB Q : ℕ}

theorem transcriptConstraintPolynomial_massLE (hQ : 1 ≤ Q) (hs : ∀ i, s i ≤ 4 * Q)
    (hnA : nA ≤ 4 * Q ^ 2) (hnB : nB ≤ 4 * Q ^ 2) (c : TConstraintIndex s nA nB) :
    CoefficientMassLE (transcriptConstraintPolynomial s nA nB c) (129 * Q ^ 4) := by
  have hQ2 : Q ≤ Q ^ 2 := by nlinarith
  have hQ4 : Q ^ 2 ≤ Q ^ 4 := by nlinarith [pow_le_pow_right₀ hQ (by norm_num : 2 ≤ 4)]
  have hprod (i j : Fin 8) : s i * s j ≤ 16 * Q ^ 2 := by
    calc s i * s j ≤ (4 * Q) * (4 * Q) := Nat.mul_le_mul (hs i) (hs j)
      _ = 16 * Q ^ 2 := by ring
  rcases c with c | c | c | c | c
  · apply (unitResourceConstraint_massLE (entryR s nA nB)).mono
    simp only [ResourceEntryIndex, Fintype.card_prod, Fintype.card_fin]
    have := hprod 0 1
    nlinarith
  · apply (instrumentPartConstraint_massLE (entryA s nA nB) c).mono
    simp only [Fintype.card_prod, Fintype.card_fin]
    have h := hprod 2 4
    have : nA * (s 2 * s 4 * 2) ≤ 4 * Q ^ 2 * (16 * Q ^ 2 * 2) :=
      Nat.mul_le_mul hnA (Nat.mul_le_mul_right 2 h)
    nlinarith
  · apply (instrumentPartConstraint_massLE (entryB s nA nB) c).mono
    simp only [Fintype.card_prod, Fintype.card_fin]
    have h := hprod 3 5
    have : nB * (s 3 * s 5 * 2) ≤ 4 * Q ^ 2 * (16 * Q ^ 2 * 2) :=
      Nat.mul_le_mul hnB (Nat.mul_le_mul_right 2 h)
    nlinarith
  · apply (isometryPartConstraint_massLE _ c.2).mono
    simp only [Fintype.card_prod, Fintype.card_fin]
    have := hs 6
    nlinarith
  · apply (isometryPartConstraint_massLE _ c.2).mono
    simp only [Fintype.card_prod, Fintype.card_fin]
    have := hs 7
    nlinarith

theorem card_tConstraintIndex_le (hQ : 1 ≤ Q) (hs : ∀ i, s i ≤ 4 * Q)
    (hnA : nA ≤ 4 * Q ^ 2) (hnB : nB ≤ 4 * Q ^ 2) :
    Fintype.card (TConstraintIndex s nA nB) ≤ 16641 * Q ^ 8 := by
  simp only [TConstraintIndex, EncoderAInputIndex, EncoderBInputIndex, DecoderAInputIndex,
    DecoderBInputIndex, Fintype.card_sum, Fintype.card_unit, Fintype.card_prod, Fintype.card_fin]
  have h0 := hs 0
  have h1 := hs 1
  have h25 : s 2 * s 5 ≤ 16 * Q ^ 2 := by
    calc s 2 * s 5 ≤ (4 * Q) * (4 * Q) := Nat.mul_le_mul (hs 2) (hs 5)
      _ = 16 * Q ^ 2 := by ring
  have h34 : s 3 * s 4 ≤ 16 * Q ^ 2 := by
    calc s 3 * s 4 ≤ (4 * Q) * (4 * Q) := Nat.mul_le_mul (hs 3) (hs 4)
      _ = 16 * Q ^ 2 := by ring
  have hnn : nA * nB ≤ 16 * Q ^ 4 := by
    calc nA * nB ≤ (4 * Q ^ 2) * (4 * Q ^ 2) := Nat.mul_le_mul hnA hnB
      _ = 16 * Q ^ 4 := by ring
  have hA : 2 * s 0 * (2 * s 0) * 2 ≤ 128 * Q ^ 8 := by
    have : 2 * s 0 * (2 * s 0) * 2 ≤ 2 * (4 * Q) * (2 * (4 * Q)) * 2 := by gcongr
    have hQ8 : Q ^ 2 ≤ Q ^ 8 := pow_le_pow_right₀ hQ (by norm_num)
    nlinarith
  have hB : 2 * s 1 * (2 * s 1) * 2 ≤ 128 * Q ^ 8 := by
    have : 2 * s 1 * (2 * s 1) * 2 ≤ 2 * (4 * Q) * (2 * (4 * Q)) * 2 := by gcongr
    have hQ8 : Q ^ 2 ≤ Q ^ 8 := pow_le_pow_right₀ hQ (by norm_num)
    nlinarith
  have hDA : nA * nB * (s 2 * s 5 * (s 2 * s 5) * 2) ≤ 8192 * Q ^ 8 := by
    calc nA * nB * (s 2 * s 5 * (s 2 * s 5) * 2)
        ≤ 16 * Q ^ 4 * (16 * Q ^ 2 * (16 * Q ^ 2) * 2) :=
          Nat.mul_le_mul hnn (Nat.mul_le_mul_right 2 (Nat.mul_le_mul h25 h25))
      _ = 8192 * Q ^ 8 := by ring
  have hDB : nA * nB * (s 3 * s 4 * (s 3 * s 4) * 2) ≤ 8192 * Q ^ 8 := by
    calc nA * nB * (s 3 * s 4 * (s 3 * s 4) * 2)
        ≤ 16 * Q ^ 4 * (16 * Q ^ 2 * (16 * Q ^ 2) * 2) :=
          Nat.mul_le_mul hnn (Nat.mul_le_mul_right 2 (Nat.mul_le_mul h34 h34))
      _ = 8192 * Q ^ 8 := by ring
  have hQ8 : 1 ≤ Q ^ 8 := Nat.one_le_pow _ _ hQ
  nlinarith

theorem transcriptConstraintSumSquares_massLE (hQ : 1 ≤ Q) (hs : ∀ i, s i ≤ 4 * Q)
    (hnA : nA ≤ 4 * Q ^ 2) (hnB : nB ≤ 4 * Q ^ 2) :
    CoefficientMassLE (transcriptConstraintSumSquares s nA nB) (2 ^ 55 * Q ^ 18) := by
  have h := CoefficientMassLE.sum_uniform _
    (fun c => (transcriptConstraintPolynomial_massLE hQ hs hnA hnB c).pow 2)
  apply h.mono
  have hc := card_tConstraintIndex_le hQ hs hnA hnB
  calc Fintype.card (TConstraintIndex s nA nB) * (129 * Q ^ 4) ^ 2
      ≤ 16641 * Q ^ 8 * (129 * Q ^ 4) ^ 2 := Nat.mul_le_mul_right _ hc
    _ = 276922881 * Q ^ 16 := by ring
    _ ≤ 2 ^ 55 * Q ^ 18 := by
        have : Q ^ 16 ≤ Q ^ 18 := pow_le_pow_right₀ hQ (by norm_num)
        nlinarith

theorem rename_eq_bind₁ {σ τ : Type*} (f : σ → τ) (p : MvPolynomial σ ℤ) :
    rename f p = bind₁ (fun i => X (f i)) p := by
  rw [rename_eq_aeval]
  rfl

theorem transcriptScorePolynomial_massLE (hs : ∀ i, s i ≤ 4 * Q)
    (hnA : nA ≤ 4 * Q ^ 2) (hnB : nB ≤ 4 * Q ^ 2) :
    CoefficientMassLE (transcriptScorePolynomial s nA nB) (2 ^ 55 * Q ^ 18) := by
  have hone : ∀ x y, CoefficientMassLE (rename (Sum.map id (transcriptRename s nA nB x y))
      (controlledPhaseScoreNumeratorPolynomial s)) (2 ^ 51 * Q ^ 14) := by
    intro x y
    rw [rename_eq_bind₁]
    exact (controlledPhaseScoreNumeratorPolynomial_massLE_of_four_mul_box s hs).bind₁ _
      fun _ => CoefficientMassLE.variablePolynomial _
  have h := CoefficientMassLE.sum_uniform _ fun x => CoefficientMassLE.sum_uniform _ (hone x)
  apply h.mono
  simp only [Fintype.card_fin]
  calc nA * (nB * (2 ^ 51 * Q ^ 14)) ≤ 4 * Q ^ 2 * (4 * Q ^ 2 * (2 ^ 51 * Q ^ 14)) :=
        Nat.mul_le_mul hnA (Nat.mul_le_mul_right _ hnB)
    _ = 2 ^ 55 * Q ^ 18 := by ring

/-- `32 + 2⁵⁵ Q¹⁸ < 2^{56 + 18 Q}`. -/
theorem two_pow_transcript_bit_bound (Q : ℕ) : 32 + 2 ^ 55 * Q ^ 18 < 2 ^ (56 + 18 * Q) := by
  have hQ : Q ^ 18 ≤ 2 ^ (18 * Q) := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 18
  have hX : 1 ≤ 2 ^ (18 * Q) := Nat.one_le_two_pow
  rw [pow_add]
  have h56 : (2 : ℕ) ^ 56 = 2 * 2 ^ 55 := by norm_num
  rw [h56]
  nlinarith

/-- **Coordinate count** (`eq:explicit-quantum-variables`). -/
theorem card_tCoordIndex_le {r a b kA kB eA eB : ℕ} (hr : 1 ≤ r) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hkA : kA ≤ 2 * r * a) (hkB : kB ≤ 2 * r * b) (heA : eA ≤ 2 * kA * b)
    (heB : eB ≤ 2 * kB * a) (hnA : nA ≤ 4 * r ^ 2) (hnB : nB ≤ 4 * r ^ 2) :
    Fintype.card (TCoordIndex ![r, r, kA, kB, a, b, eA, eB] nA nB) ≤
      1090 * r ^ 4 * (r * a * b) ^ 2 := by
  rw [card_tCoordIndex]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  set q := r * a * b with hq
  have hra : r ≤ q := by
    calc r = r * 1 * 1 := by ring
      _ ≤ r * a * b := Nat.mul_le_mul (Nat.mul_le_mul_left _ ha) hb
  have haq : a ≤ q := by
    calc a = 1 * a * 1 := by ring
      _ ≤ r * a * b := Nat.mul_le_mul (Nat.mul_le_mul_right _ hr) hb
  have hbq : b ≤ q := by
    calc b = 1 * 1 * b := by ring
      _ ≤ r * a * b := Nat.mul_le_mul_right _ (Nat.mul_le_mul hr ha)
  have hr4 : r ^ 2 ≤ r ^ 4 := pow_le_pow_right₀ hr (by norm_num)
  have hq1 : 1 ≤ q := hr.trans hra
  -- resource
  have t0 : r * r ≤ r ^ 4 * q ^ 2 := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    nlinarith
  -- encoders
  have t1 : nA * (kA * a * (2 * r)) ≤ 16 * r ^ 4 * q ^ 2 := by
    calc nA * (kA * a * (2 * r)) ≤ 4 * r ^ 2 * (2 * r * a * a * (2 * r)) :=
          Nat.mul_le_mul hnA (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hkA))
      _ = 16 * r ^ 4 * a ^ 2 := by ring
      _ ≤ 16 * r ^ 4 * q ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left haq 2)
  have t2 : nB * (kB * b * (2 * r)) ≤ 16 * r ^ 4 * q ^ 2 := by
    calc nB * (kB * b * (2 * r)) ≤ 4 * r ^ 2 * (2 * r * b * b * (2 * r)) :=
          Nat.mul_le_mul hnB (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hkB))
      _ = 16 * r ^ 4 * b ^ 2 := by ring
      _ ≤ 16 * r ^ 4 * q ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbq 2)
  -- decoders
  have hkb : kA * b ≤ 2 * q := by
    calc kA * b ≤ 2 * r * a * b := Nat.mul_le_mul_right _ hkA
      _ = 2 * q := by rw [hq]; ring
  have hka : kB * a ≤ 2 * q := by
    calc kB * a ≤ 2 * r * b * a := Nat.mul_le_mul_right _ hkB
      _ = 2 * q := by rw [hq]; ring
  have hnn : nA * nB ≤ 16 * r ^ 4 := by
    calc nA * nB ≤ (4 * r ^ 2) * (4 * r ^ 2) := Nat.mul_le_mul hnA hnB
      _ = 16 * r ^ 4 := by ring
  have t3 : nA * nB * (2 * eA * (kA * b)) ≤ 256 * r ^ 4 * q ^ 2 := by
    calc nA * nB * (2 * eA * (kA * b)) ≤ 16 * r ^ 4 * (2 * (2 * kA * b) * (kA * b)) :=
          Nat.mul_le_mul hnn (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ heA))
      _ = 64 * r ^ 4 * (kA * b) ^ 2 := by ring
      _ ≤ 64 * r ^ 4 * (2 * q) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkb 2)
      _ = 256 * r ^ 4 * q ^ 2 := by ring
  have t4 : nA * nB * (2 * eB * (kB * a)) ≤ 256 * r ^ 4 * q ^ 2 := by
    calc nA * nB * (2 * eB * (kB * a)) ≤ 16 * r ^ 4 * (2 * (2 * kB * a) * (kB * a)) :=
          Nat.mul_le_mul hnn (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ heB))
      _ = 64 * r ^ 4 * (kB * a) ^ 2 := by ring
      _ ≤ 64 * r ^ 4 * (2 * q) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hka 2)
      _ = 256 * r ^ 4 * q ^ 2 := by ring
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add t0 t1) t2) t3) t4
  calc 2 * (r * r + nA * (kA * a * (2 * r)) + nB * (kB * b * (2 * r)) +
        nA * nB * (2 * eA * (kA * b)) + nA * nB * (2 * eB * (kB * a)))
      ≤ 2 * (r ^ 4 * q ^ 2 + 16 * r ^ 4 * q ^ 2 + 16 * r ^ 4 * q ^ 2 + 256 * r ^ 4 * q ^ 2 +
          256 * r ^ 4 * q ^ 2) := Nat.mul_le_mul_left 2 hsum
    _ ≤ 1090 * r ^ 4 * q ^ 2 := by ring_nf; omega

end NLQCLean.TranscriptPolynomial
