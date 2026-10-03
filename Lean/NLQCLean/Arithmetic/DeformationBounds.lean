import NLQCLean.Arithmetic.DeformationFinal

/-!
# Size bounds of the deformation eliminant in the epigraph form

With `32 + H < 2^τ`, `τ ≥ 1` and `k` coordinates, the deformation eliminant has degree at
most `12^{4(k+2)}` and coefficients below `2^{τ · 12^{4(k+2)}}`. This is the shape used
downstream for the controlled-phase bounds.
-/

namespace NLQCLean.Deformation

open MvPolynomial NLQCLean.PhysicalPolynomial NLQCLean.Elimination NLQCLean.PurePower

theorem NB_le (k : ℕ) : NB k ≤ 2 ^ (5 * k + 5) := by
  unfold NB
  calc 26 * 25 ^ k ≤ 32 * 32 ^ k := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by norm_num) k)
    _ = 2 ^ (5 * k + 5) := by rw [pow_add, pow_mul]; norm_num; ring

theorem DB_le (k : ℕ) : DB k ≤ 2 ^ (k + 5) := by
  unfold DB
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h : 32 ≤ 2 ^ (k + 5) := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (k + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show k + 1 + 5 = (k + 5) + 1 by ring, pow_succ]
    omega

theorem dPhi_le (k : ℕ) : dPhi k ≤ 2 ^ (6 * k + 10) := by
  unfold dPhi
  calc NB k * DB k ≤ 2 ^ (5 * k + 5) * 2 ^ (k + 5) := Nat.mul_le_mul (NB_le k) (DB_le k)
    _ = 2 ^ (6 * k + 10) := by rw [← pow_add]; congr 1; ring

theorem R0_le (k : ℕ) : R0 k ≤ 2 ^ (k + 105) := by
  unfold R0
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h16 : (16 : ℕ) ^ 26 = 2 ^ 104 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h104 : 1 ≤ 2 ^ 104 := Nat.one_le_two_pow
  rw [h16]
  calc k + 2 ^ 104 + 1 = (k + 1) + 2 ^ 104 := by ring
    _ ≤ 2 ^ k * 2 ^ 104 + 2 ^ k * 2 ^ 104 :=
        Nat.add_le_add (hk.trans (Nat.le_mul_of_pos_right _ h104))
          (Nat.le_mul_of_pos_left _ hpos)
    _ = 2 ^ (k + 105) := by rw [← two_mul, ← pow_add, ← pow_succ']

theorem KB_le (k H τ : ℕ) (hH : 32 + H < 2 ^ τ) : KB k H ≤ 2 ^ (k + 111 + 2 * τ) := by
  unfold KB
  have hH1 : 1 + H ≤ 2 ^ τ := by omega
  have hHs : H ^ 2 + (1 + H) ^ 2 ≤ 2 ^ (2 * τ + 1) := by
    have h1 : H ^ 2 ≤ (2 ^ τ) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : (1 + H) ^ 2 ≤ (2 ^ τ) ^ 2 := Nat.pow_le_pow_left hH1 2
    calc H ^ 2 + (1 + H) ^ 2 ≤ (2 ^ τ) ^ 2 + (2 ^ τ) ^ 2 := Nat.add_le_add h1 h2
      _ = 2 ^ (2 * τ + 1) := by rw [← two_mul, ← pow_mul, pow_succ]; ring
  have hA : 26 * R0 k ≤ 2 ^ (k + 110 + 2 * τ) := by
    calc 26 * R0 k ≤ 2 ^ 5 * 2 ^ (k + 105) := Nat.mul_le_mul (by norm_num) (R0_le k)
      _ = 2 ^ (k + 110) := by rw [← pow_add]; congr 1; ring
      _ ≤ 2 ^ (k + 110 + 2 * τ) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB : (26 + 24 * k) * (H ^ 2 + (1 + H) ^ 2) ≤ 2 ^ (k + 110 + 2 * τ) := by
    calc (26 + 24 * k) * (H ^ 2 + (1 + H) ^ 2) ≤ 2 ^ (k + 5) * 2 ^ (2 * τ + 1) :=
          Nat.mul_le_mul (DB_le k) hHs
      _ = 2 ^ (k + 6 + 2 * τ) := by rw [← pow_add]; congr 1; ring
      _ ≤ 2 ^ (k + 110 + 2 * τ) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 26 * R0 k + (26 + 24 * k) * (H ^ 2 + (1 + H) ^ 2)
      ≤ 2 ^ (k + 110 + 2 * τ) + 2 ^ (k + 110 + 2 * τ) := Nat.add_le_add hA hB
    _ = 2 ^ (k + 111 + 2 * τ) := by rw [← two_mul, ← pow_succ']; congr 1; ring

/-- The exponent bounding the final mass. -/
def massExp (k τ : ℕ) : ℕ :=
  2 + 2 * ((6 * k + 11) + 2 ^ (5 * k + 5) * ((5 * k + 6) + 2 ^ (k + 5) * (k + 111 + 2 * τ)) +
    2 ^ (6 * k + 10)) + 5 * (4 * 2 ^ (6 * k + 10) + 2)

theorem MPhi_le (k H τ : ℕ) (hH : 32 + H < 2 ^ τ) :
    MPhi k H ≤ 2 ^ (2 ^ (5 * k + 5) * ((5 * k + 6) + 2 ^ (k + 5) * (k + 111 + 2 * τ))) := by
  unfold MPhi
  set kb := k + 111 + 2 * τ
  have hKB := KB_le k H τ hH
  have hfac : (NB k).factorial ≤ 2 ^ ((5 * k + 5) * NB k) := by
    calc (NB k).factorial ≤ NB k ^ NB k := Nat.factorial_le_pow _
      _ ≤ (2 ^ (5 * k + 5)) ^ NB k := Nat.pow_le_pow_left (NB_le k) _
      _ = 2 ^ ((5 * k + 5) * NB k) := by rw [← pow_mul]
  have hbase : KB k H ^ DB k + KB k H ^ DB k ≤ 2 ^ (1 + 2 ^ (k + 5) * kb) := by
    have : KB k H ^ DB k ≤ 2 ^ (2 ^ (k + 5) * kb) := by
      calc KB k H ^ DB k ≤ (2 ^ kb) ^ DB k := Nat.pow_le_pow_left hKB _
        _ = 2 ^ (kb * DB k) := by rw [← pow_mul]
        _ ≤ 2 ^ (2 ^ (k + 5) * kb) := Nat.pow_le_pow_right (by norm_num)
            (by rw [mul_comm]; exact Nat.mul_le_mul_right _ (DB_le k))
    calc KB k H ^ DB k + KB k H ^ DB k ≤ 2 ^ (2 ^ (k + 5) * kb) + 2 ^ (2 ^ (k + 5) * kb) :=
          Nat.add_le_add this this
      _ = 2 ^ (1 + 2 ^ (k + 5) * kb) := by rw [← two_mul, ← pow_succ']; congr 1; ring
  calc (NB k).factorial * (KB k H ^ DB k + KB k H ^ DB k) ^ NB k
      ≤ 2 ^ ((5 * k + 5) * NB k) * (2 ^ (1 + 2 ^ (k + 5) * kb)) ^ NB k :=
        Nat.mul_le_mul hfac (Nat.pow_le_pow_left hbase _)
    _ = 2 ^ (NB k * ((5 * k + 6) + 2 ^ (k + 5) * kb)) := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (NB_le k))

theorem mass_le_massExp (k H τ : ℕ) (hH : 32 + H < 2 ^ τ) :
    MNrm k H * 32 ^ dNrm k ≤ 2 ^ massExp k τ := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 2 ^ (5 * k + 5) * ((5 * k + 6) + 2 ^ (k + 5) * (k + 111 + 2 * τ)) :=
    ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ (6 * k + 10) := ⟨_, rfl⟩
  have hd : dPhi k ≤ P := hP ▸ dPhi_le k
  have hM : MPhi k H ≤ 2 ^ Y := hY ▸ MPhi_le k H τ hH
  have hP1 : 1 ≤ P := hP ▸ Nat.one_le_two_pow
  have hd1 : dPhi k + 1 ≤ 2 ^ (6 * k + 11) := by
    have : 2 ^ (6 * k + 11) = P + P := by rw [hP, ← two_mul, ← pow_succ']
    omega
  have hinner : (dPhi k + 1) * (MPhi k H * 2 ^ dPhi k) ≤ 2 ^ ((6 * k + 11) + Y + P) := by
    calc (dPhi k + 1) * (MPhi k H * 2 ^ dPhi k) ≤ 2 ^ (6 * k + 11) * (2 ^ Y * 2 ^ P) :=
          Nat.mul_le_mul hd1 (Nat.mul_le_mul hM (Nat.pow_le_pow_right (by norm_num) hd))
      _ = 2 ^ ((6 * k + 11) + Y + P) := by rw [← pow_add, ← pow_add]; congr 1; ring
  have hM3 : MNrm k H ≤ 2 ^ (2 + 2 * ((6 * k + 11) + Y + P)) := by
    unfold MNrm
    calc 3 * ((dPhi k + 1) * (MPhi k H * 2 ^ dPhi k)) ^ 2
        ≤ 2 ^ 2 * (2 ^ ((6 * k + 11) + Y + P)) ^ 2 :=
          Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hinner 2)
      _ = 2 ^ (2 + 2 * ((6 * k + 11) + Y + P)) := by rw [← pow_mul, ← pow_add, mul_comm _ 2]
  have h32 : (32 : ℕ) ^ dNrm k ≤ 2 ^ (5 * (4 * P + 2)) := by
    rw [show (32 : ℕ) = 2 ^ 5 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by unfold dNrm; omega)
  have hexp : massExp k τ = 2 + 2 * ((6 * k + 11) + Y + P) + 5 * (4 * P + 2) := by
    rw [hY, hP]; rfl
  calc MNrm k H * 32 ^ dNrm k ≤ 2 ^ (2 + 2 * ((6 * k + 11) + Y + P)) * 2 ^ (5 * (4 * P + 2)) :=
        Nat.mul_le_mul hM3 h32
    _ = 2 ^ massExp k τ := by rw [← pow_add, hexp]

theorem massExp_lt (k τ : ℕ) (hτ : 1 ≤ τ) : massExp k τ < τ * 12 ^ (4 * (k + 2)) := by
  unfold massExp
  set P := 2 ^ (6 * k + 10) with hP
  set A := 2 ^ (5 * k + 5) with hA
  set B := 2 ^ (k + 5) with hB
  have hAB : A * B = P := by rw [hA, hB, hP, ← pow_add]; congr 1; ring
  have hA1 : 1 ≤ A := Nat.one_le_two_pow
  have hAP : A ≤ P := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hP1 : 1024 ≤ P := by
    calc 1024 = 2 ^ 10 := by norm_num
      _ ≤ P := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk2 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  -- every term is at most a multiple of `P τ`
  have hE : 2 + 2 * ((6 * k + 11) + A * ((5 * k + 6) + B * (k + 111 + 2 * τ)) + P) +
      5 * (4 * P + 2) ≤ P * (316 * 2 ^ k) * τ := by
    have h1 : A * ((5 * k + 6) + B * (k + 111 + 2 * τ)) =
        A * (5 * k + 6) + P * (k + 111 + 2 * τ) := by rw [mul_add, ← mul_assoc, hAB]
    rw [h1]
    have h2 : A * (5 * k + 6) ≤ P * (5 * k + 6) := Nat.mul_le_mul_right _ hAP
    have h3 : 6 * k + 11 ≤ P * (k + 1) := by nlinarith
    have hτk : k + 111 + 2 * τ ≤ (k + 113) * τ := by nlinarith
    have hsum : 2 + 2 * (P * (k + 1) + (P * (5 * k + 6) + P * ((k + 113) * τ)) + P) +
        5 * (4 * P + 2) ≤ P * (316 * 2 ^ k) * τ := by
      have hk' : 12 * k + 300 ≤ 316 * 2 ^ k := by nlinarith
      nlinarith [Nat.zero_le (P * τ), Nat.zero_le (P * k * τ)]
    calc 2 + 2 * ((6 * k + 11) + (A * (5 * k + 6) + P * (k + 111 + 2 * τ)) + P) + 5 * (4 * P + 2)
        ≤ 2 + 2 * (P * (k + 1) + (P * (5 * k + 6) + P * ((k + 113) * τ)) + P) +
            5 * (4 * P + 2) := by
          gcongr
      _ ≤ _ := hsum
  have h316 : P * (316 * 2 ^ k) < 12 ^ (4 * (k + 2)) := by
    have h1 : P * (316 * 2 ^ k) < 2 ^ (7 * k + 19) := by
      calc P * (316 * 2 ^ k) < 2 ^ (6 * k + 10) * (512 * 2 ^ k) :=
            Nat.mul_lt_mul_of_pos_left (by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega)
              (by positivity)
        _ = 2 ^ (7 * k + 19) := by
            rw [show (512 : ℕ) = 2 ^ 9 by norm_num, ← pow_add, ← pow_add]; congr 1; ring
    have h2 : 2 ^ (7 * k + 19) ≤ 12 ^ (4 * (k + 2)) := by
      calc 2 ^ (7 * k + 19) ≤ 2 ^ (14 * (k + 2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ 14) ^ (k + 2) := by rw [← pow_mul]
        _ ≤ (12 ^ 4) ^ (k + 2) := Nat.pow_le_pow_left (by norm_num) _
        _ = 12 ^ (4 * (k + 2)) := by rw [← pow_mul]
    omega
  calc _ ≤ P * (316 * 2 ^ k) * τ := hE
    _ < 12 ^ (4 * (k + 2)) * τ := Nat.mul_lt_mul_of_pos_right h316 (by omega)
    _ = τ * 12 ^ (4 * (k + 2)) := mul_comm _ _

theorem dNrm_le (k : ℕ) : dNrm k ≤ 12 ^ (4 * (k + 2)) := by
  unfold dNrm
  have hd := dPhi_le k
  calc 4 * dPhi k + 2 ≤ 4 * 2 ^ (6 * k + 10) + 2 ^ (6 * k + 10) := by
        have : 2 ≤ 2 ^ (6 * k + 10) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    _ ≤ 8 * 2 ^ (6 * k + 10) := by omega
    _ = 2 ^ (6 * k + 13) := by rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; ring
    _ ≤ 2 ^ (14 * (k + 2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (2 ^ 14) ^ (k + 2) := by rw [← pow_mul]
    _ ≤ (12 ^ 4) ^ (k + 2) := Nat.pow_le_pow_left (by norm_num) _
    _ = 12 ^ (4 * (k + 2)) := by rw [← pow_mul]

/-- **The optimization eliminant in the epigraph form, without external input**, with the
exponent `a = 4`. -/
theorem exists_eliminant_explicit (κ : Type) [Fintype κ] (Cst : MvPolynomial κ ℤ)
    (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) (H τ : ℕ) (θ g : ℝ) (hτ : 1 ≤ τ)
    (hC : Cst.totalDegree ≤ 12) (hS : Sc.totalDegree ≤ 12)
    (hCm : CoefficientMassLE Cst H) (hSm : CoefficientMassLE Sc H) (hH : 32 + H < 2 ^ τ)
    (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hupper : ∀ w : κ → ℝ, PhysicalPolynomial.eval w Cst = 0 →
      PhysicalPolynomial.eval (Sum.elim ![Real.cos θ, Real.sin θ] w) Sc ≤ 16 * (1 - g))
    (hattain : ∃ w : κ → ℝ, PhysicalPolynomial.eval w Cst = 0 ∧
      PhysicalPolynomial.eval (Sum.elim ![Real.cos θ, Real.sin θ] w) Sc = 16 * (1 - g) ∧
      ∀ i, |w i| ≤ 1) :
    ∃ A : MvPolynomial (Fin 2) ℤ, A ≠ 0 ∧
      A.totalDegree ≤ 12 ^ (4 * (Fintype.card κ + 2)) ∧
      (∀ m, (A.coeff m).natAbs < 2 ^ (τ * 12 ^ (4 * (Fintype.card κ + 2)))) ∧
      MvPolynomial.eval₂ (Int.castRingHom ℝ) ![g, Real.cos θ] A = 0 := by
  classical
  obtain ⟨A, hA0, hAsz, hAz⟩ :=
    exists_deformation_eliminant Cst Sc hC hS hCm hSm θ g hg0 hg1 hupper hattain
  refine ⟨A, hA0, hAsz.1.trans (dNrm_le _), fun m => ?_, hAz⟩
  calc (A.coeff m).natAbs ≤ MNrm (Fintype.card κ) H * 32 ^ dNrm (Fintype.card κ) :=
        hAsz.2.coefficient_natAbs_le m
    _ ≤ 2 ^ massExp (Fintype.card κ) τ := mass_le_massExp _ H τ hH
    _ < 2 ^ (τ * 12 ^ (4 * (Fintype.card κ + 2))) :=
        Nat.pow_lt_pow_right (by norm_num) (massExp_lt _ τ hτ)

/-- **The optimization eliminant in the epigraph form, without external input.** -/
theorem exists_eliminant_of_family :
    ∃ a : ℕ, ∀ (κ : Type) [Fintype κ] (Cst : MvPolynomial κ ℤ)
      (Sc : MvPolynomial (Fin 2 ⊕ κ) ℤ) (H τ : ℕ) (θ g : ℝ), 1 ≤ τ →
      Cst.totalDegree ≤ 12 → Sc.totalDegree ≤ 12 →
      CoefficientMassLE Cst H → CoefficientMassLE Sc H → 32 + H < 2 ^ τ → 0 < g → g ≤ 1 →
      (∀ w : κ → ℝ, PhysicalPolynomial.eval w Cst = 0 →
        PhysicalPolynomial.eval (Sum.elim ![Real.cos θ, Real.sin θ] w) Sc ≤ 16 * (1 - g)) →
      (∃ w : κ → ℝ, PhysicalPolynomial.eval w Cst = 0 ∧
        PhysicalPolynomial.eval (Sum.elim ![Real.cos θ, Real.sin θ] w) Sc = 16 * (1 - g) ∧
        ∀ i, |w i| ≤ 1) →
      ∃ A : MvPolynomial (Fin 2) ℤ, A ≠ 0 ∧
        A.totalDegree ≤ 12 ^ (a * (Fintype.card κ + 2)) ∧
        (∀ m, (A.coeff m).natAbs < 2 ^ (τ * 12 ^ (a * (Fintype.card κ + 2)))) ∧
        MvPolynomial.eval₂ (Int.castRingHom ℝ) ![g, Real.cos θ] A = 0 :=
  ⟨4, fun κ _ Cst Sc H τ θ g hτ hC hS hCm hSm hH hg0 hg1 hupper hattain =>
    exists_eliminant_explicit κ Cst Sc H τ θ g hτ hC hS hCm hSm hH hg0 hg1 hupper hattain⟩

end NLQCLean.Deformation
