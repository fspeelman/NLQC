import NLQCLean.Arithmetic.GelfondAngleDoubling

/-!
# Numerics of Gelfond's method for `e^{iθ}`

Parameters `h = B⁴`, `J = B⁷`, `L = 4B¹¹`, `T₀ = B¹²` for `B ≥ 128` bounding the degree of `G`,
`log₂` of its coefficients, and the data `a, m, 1 + F, |θ|` of the angle. Every quantity of the
doubling conditions is bounded by an explicit power of `2`, and the two conditions are checked
along the whole chain with `ρ = 2^{-(B⁴⁸+1)}`.
-/

namespace NLQCLean.Gelfond

open Polynomial GaussianInt

theorem natPow_le_two_pow (B k : ℕ) : B ^ k ≤ 2 ^ (k * B) :=
  calc B ^ k ≤ (2 ^ B) ^ k := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
    _ = 2 ^ (k * B) := by rw [← pow_mul, mul_comm]

section Params

variable {B : ℕ} (hB : 128 ≤ B)
include hB

theorem angU_nat : (B ^ 7 + 1) * (4 * B ^ 11) ≤ 8 * B ^ 18 := by
  have : 1 ≤ B ^ 7 := Nat.one_le_pow _ _ (by omega)
  nlinarith [Nat.zero_le (B ^ 11), show B ^ 18 = B ^ 7 * B ^ 11 by ring]

theorem angU_le : (((B ^ 7 : ℕ) : ℝ) + 1) * ((4 * B ^ 11 : ℕ) : ℝ) ≤ 2 ^ (18 * B + 3) := by
  have h1 := angU_nat hB
  have h2 := natPow_le_two_pow B 18
  have h3 : (B ^ 7 + 1) * (4 * B ^ 11) ≤ 2 ^ (18 * B + 3) := by
    calc (B ^ 7 + 1) * (4 * B ^ 11) ≤ 8 * B ^ 18 := h1
      _ ≤ 8 * 2 ^ (18 * B) := by omega
      _ = 2 ^ (18 * B + 3) := by ring
  have : ((((B ^ 7 + 1) * (4 * B ^ 11) : ℕ)) : ℝ) ≤ 2 ^ (18 * B + 3) := by exact_mod_cast h3
  push_cast at this ⊢
  exact this

omit hB in
theorem angH_pow_le : ((B ^ 4 : ℕ) : ℝ) ^ (4 * B ^ 11) ≤ 2 ^ (16 * B ^ 12) := by
  have h : ((B ^ 4 : ℕ) : ℝ) ≤ 2 ^ (4 * B) := by push_cast; exact natCast_pow_le_two_pow B 4
  refine (pow_le_two_pow (by positivity) h _).trans (le_of_eq ?_)
  congr 1; ring

theorem angV_le {a : ℕ} (haB : a ≤ B) {F : ℝ} (_hF0 : 0 ≤ F) (hFB : 1 + F ≤ B) :
    (a : ℝ) * ((4 * B ^ 11 : ℕ) : ℝ) + ((B ^ 7 : ℕ) : ℝ) * (1 + F) ≤ 2 ^ (12 * B + 3) := by
  have ha : (a : ℝ) ≤ B := by exact_mod_cast haB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have h12 : (B : ℝ) ^ 12 ≤ 2 ^ (12 * B) := natCast_pow_le_two_pow B 12
  have h8 : (B : ℝ) ^ 8 ≤ (B : ℝ) ^ 12 := pow_le_pow_right₀ hB1 (by norm_num)
  push_cast
  calc (a : ℝ) * (4 * (B : ℝ) ^ 11) + (B : ℝ) ^ 7 * (1 + F)
      ≤ (B : ℝ) * (4 * (B : ℝ) ^ 11) + (B : ℝ) ^ 7 * B := by gcongr
    _ = 4 * (B : ℝ) ^ 12 + (B : ℝ) ^ 8 := by ring
    _ ≤ 8 * 2 ^ (12 * B) := by
        have : (0 : ℝ) ≤ 2 ^ (12 * B) := by positivity
        linarith
    _ = 2 ^ (12 * B + 3) := by rw [pow_add]; ring

theorem angW_le {θ : ℝ} (hθB : |θ| ≤ B) :
    ((B ^ 7 : ℕ) : ℝ) * |θ| + ((4 * B ^ 11 : ℕ) : ℝ) ≤ 2 ^ (12 * B + 3) := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have h12 : (B : ℝ) ^ 12 ≤ 2 ^ (12 * B) := natCast_pow_le_two_pow B 12
  have h8 : (B : ℝ) ^ 8 ≤ (B : ℝ) ^ 12 := pow_le_pow_right₀ hB1 (by norm_num)
  have h11 : (B : ℝ) ^ 11 ≤ (B : ℝ) ^ 12 := pow_le_pow_right₀ hB1 (by norm_num)
  push_cast
  calc (B : ℝ) ^ 7 * |θ| + 4 * (B : ℝ) ^ 11 ≤ (B : ℝ) ^ 7 * B + 4 * (B : ℝ) ^ 11 := by gcongr
    _ = (B : ℝ) ^ 8 + 4 * (B : ℝ) ^ 11 := by ring
    _ ≤ 8 * 2 ^ (12 * B) := by
        have : (0 : ℝ) ≤ 2 ^ (12 * B) := by positivity
        linarith
    _ = 2 ^ (12 * B + 3) := by rw [pow_add]; ring

/-- The Siegel coefficient bound. -/
theorem angSiegelBound_le {G : GaussianInt[X]} (hg : G.natDegree ≤ B) {a : ℕ} (haB : a ≤ B)
    {F : ℝ} (hF0 : 0 ≤ F) (hFB : 1 + F ≤ B) :
    angSiegelBound G (2 ^ B) a F (B ^ 7) (4 * B ^ 11) (B ^ 4) (B ^ 12) ≤ 2 ^ (14 * B ^ 13) := by
  have hU := angU_le hB
  have hV : ((a : ℝ) * ((4 * B ^ 11 : ℕ) : ℝ) + ((B ^ 7 : ℕ) : ℝ) * (1 + F)) ^ (B ^ 12) ≤
      2 ^ ((12 * B + 3) * B ^ 12) := pow_le_two_pow (by positivity) (angV_le hB haB hF0 hFB) _
  have ha : ((2 : ℝ) ^ B) ^ (B ^ 7 * B ^ 4) = 2 ^ (B * B ^ 11) := by
    rw [← pow_mul]; ring_nf
  have hag : (1 + ((2 : ℝ) ^ B) ^ G.natDegree) ^ (B ^ 7 * B ^ 4) ≤ 2 ^ ((B * B + 1) * B ^ 11) := by
    have h1 : 1 + ((2 : ℝ) ^ B) ^ G.natDegree ≤ 2 ^ (B * B + 1) := by
      rw [← pow_mul, pow_succ]
      have : (2 : ℝ) ^ (B * G.natDegree) ≤ 2 ^ (B * B) := two_pow_mono (Nat.mul_le_mul_left _ hg)
      have h1 : (1 : ℝ) ≤ 2 ^ (B * B) := one_le_pow₀ (by norm_num)
      linarith
    refine (pow_le_two_pow (by positivity) h1 _).trans (le_of_eq ?_)
    ring_nf
  have hU' : ((((B ^ 7 + 1) * (4 * B ^ 11) : ℕ)) : ℝ) ≤ 2 ^ (18 * B + 3) := by
    push_cast at hU ⊢; exact hU
  unfold angSiegelBound
  calc ((((B ^ 7 + 1) * (4 * B ^ 11) : ℕ)) : ℝ) * (((B ^ 4 : ℕ) : ℝ) ^ (4 * B ^ 11) *
        ((a : ℝ) * ((4 * B ^ 11 : ℕ) : ℝ) + ((B ^ 7 : ℕ) : ℝ) * (1 + F)) ^ (B ^ 12) *
        (2 ^ B) ^ (B ^ 7 * B ^ 4) * (1 + (2 ^ B) ^ G.natDegree) ^ (B ^ 7 * B ^ 4))
      ≤ 2 ^ (18 * B + 3) * (2 ^ (16 * B ^ 12) * 2 ^ ((12 * B + 3) * B ^ 12) *
          2 ^ (B * B ^ 11) * 2 ^ ((B * B + 1) * B ^ 11)) := by
        rw [ha]
        gcongr
        exact angH_pow_le
    _ = 2 ^ (18 * B + 3 + 16 * B ^ 12 + (12 * B + 3) * B ^ 12 + B * B ^ 11 +
          (B * B + 1) * B ^ 11) := by
        simp only [pow_add]; ring
    _ ≤ 2 ^ (14 * B ^ 13) := by
        apply two_pow_mono
        have f12 : 128 * B ^ 12 ≤ B ^ 13 := Bfact hB 12
        have f11 : 128 * B ^ 11 ≤ B ^ 12 := Bfact hB 11
        have f1 : B ≤ B ^ 11 := Nat.le_self_pow (by norm_num) B
        ring_nf
        omega

theorem heightQA_le' {a : ℕ} (haB : a ≤ B) {F : ℝ} (hF0 : 0 ≤ F) (hFB : 1 + F ≤ B) {Cc : ℝ}
    (hCc0 : 0 ≤ Cc) (hCc : Cc ≤ 2 ^ (14 * B ^ 13)) (t : ℕ) :
    heightQA a F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t ≤ 2 ^ (15 * B ^ 13 + (12 * B + 3) * t) := by
  unfold heightQA
  have hV : ((a : ℝ) * ((4 * B ^ 11 : ℕ) : ℝ) + ((B ^ 7 : ℕ) : ℝ) * (1 + F)) ^ t ≤
      2 ^ ((12 * B + 3) * t) := pow_le_two_pow (by positivity) (angV_le hB haB hF0 hFB) _
  calc (((B ^ 7 : ℕ) : ℝ) + 1) * ((4 * B ^ 11 : ℕ) : ℝ) * (Cc * (((B ^ 4 : ℕ) : ℝ) ^ (4 * B ^ 11) *
        ((a : ℝ) * ((4 * B ^ 11 : ℕ) : ℝ) + ((B ^ 7 : ℕ) : ℝ) * (1 + F)) ^ t))
      ≤ 2 ^ (18 * B + 3) * (2 ^ (14 * B ^ 13) * (2 ^ (16 * B ^ 12) * 2 ^ ((12 * B + 3) * t))) := by
        gcongr
        · exact angU_le hB
        · exact angH_pow_le
    _ = 2 ^ (18 * B + 3 + 14 * B ^ 13 + 16 * B ^ 12 + (12 * B + 3) * t) := by
        simp only [pow_add]; ring
    _ ≤ 2 ^ (15 * B ^ 13 + (12 * B + 3) * t) := by
        apply two_pow_mono
        have f12 : 128 * B ^ 12 ≤ B ^ 13 := Bfact hB 12
        have f1 : B ≤ B ^ 12 := Nat.le_self_pow (by norm_num) B
        omega

theorem heightS_le' {θ : ℝ} (hθB : |θ| ≤ B) {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : Cc ≤ 2 ^ (14 * B ^ 13)) (t : ℕ) :
    heightS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| t ≤ 2 ^ (15 * B ^ 13 + (12 * B + 3) * t) := by
  unfold heightS
  have hV : (((B ^ 7 : ℕ) : ℝ) * |θ| + ((4 * B ^ 11 : ℕ) : ℝ)) ^ t ≤ 2 ^ ((12 * B + 3) * t) :=
    pow_le_two_pow (by positivity) (angW_le hB hθB) _
  calc (((B ^ 7 : ℕ) : ℝ) + 1) * ((4 * B ^ 11 : ℕ) : ℝ) * (Cc * (((B ^ 4 : ℕ) : ℝ) ^ (4 * B ^ 11) *
        (((B ^ 7 : ℕ) : ℝ) * |θ| + ((4 * B ^ 11 : ℕ) : ℝ)) ^ t))
      ≤ 2 ^ (18 * B + 3) * (2 ^ (14 * B ^ 13) * (2 ^ (16 * B ^ 12) * 2 ^ ((12 * B + 3) * t))) := by
        gcongr
        · exact angU_le hB
        · exact angH_pow_le
    _ = 2 ^ (18 * B + 3 + 14 * B ^ 13 + 16 * B ^ 12 + (12 * B + 3) * t) := by
        simp only [pow_add]; ring
    _ ≤ 2 ^ (15 * B ^ 13 + (12 * B + 3) * t) := by
        apply two_pow_mono
        have f12 : 128 * B ^ 12 ≤ B ^ 13 := Bfact hB 12
        have f1 : B ≤ B ^ 12 := Nat.le_self_pow (by norm_num) B
        omega

omit hB in
theorem paramQ11_le : (((B ^ 7 * B ^ 4 : ℕ) : ℝ) + 1) ≤ 2 ^ (11 * B + 1) := by
  have h1 : B ^ 7 * B ^ 4 + 1 ≤ 2 ^ (11 * B + 1) := by
    have : B ^ 7 * B ^ 4 ≤ 2 ^ (11 * B) := by
      rw [← pow_add]; exact natPow_le_two_pow B 11
    have h2 := Nat.one_le_two_pow (n := 11 * B)
    calc B ^ 7 * B ^ 4 + 1 ≤ 2 * 2 ^ (11 * B) := by omega
      _ = 2 ^ (11 * B + 1) := by ring
  exact_mod_cast h1

omit hB in
theorem paramQ11_le' : (((B ^ 7 * B ^ 4 : ℕ) : ℝ)) ≤ 2 ^ (11 * B) := by
  have : B ^ 7 * B ^ 4 ≤ 2 ^ (11 * B) := by rw [← pow_add]; exact natPow_le_two_pow B 11
  exact_mod_cast this

theorem lipS_le' {θ : ℝ} (hθB : |θ| ≤ B) {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : Cc ≤ 2 ^ (14 * B ^ 13)) (t : ℕ) :
    lipS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| t ≤ 2 ^ (16 * B ^ 13 + (12 * B + 3) * t) := by
  unfold lipS
  have hS := heightS_le' hB hθB hCc0 hCc t
  have hS0 := heightS_nonneg (J := B ^ 7) (L := 4 * B ^ 11) (h := B ^ 4) hCc0 (abs_nonneg θ) t
  calc (((B ^ 7 * B ^ 4 : ℕ) : ℝ) + 1) * (((B ^ 7 * B ^ 4 : ℕ) : ℝ) *
        (heightS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| t * 2 ^ (B ^ 7 * B ^ 4)))
      ≤ 2 ^ (11 * B + 1) * (2 ^ (11 * B) * (2 ^ (15 * B ^ 13 + (12 * B + 3) * t) *
          2 ^ (B ^ 7 * B ^ 4))) := by
        gcongr
        · exact paramQ11_le
        · exact paramQ11_le'
    _ = 2 ^ (11 * B + 1 + 11 * B + 15 * B ^ 13 + (12 * B + 3) * t + B ^ 7 * B ^ 4) := by
        simp only [pow_add]; ring
    _ ≤ 2 ^ (16 * B ^ 13 + (12 * B + 3) * t) := by
        apply two_pow_mono
        have f12 : 128 * B ^ 12 ≤ B ^ 13 := Bfact hB 12
        have f11 : 128 * B ^ 11 ≤ B ^ 12 := Bfact hB 11
        have f1 : B ≤ B ^ 11 := Nat.le_self_pow (by norm_num) B
        have e : B ^ 7 * B ^ 4 = B ^ 11 := by ring
        omega

theorem angleE_le {m : ℕ} (hmB : m ≤ B) {F : ℝ} (hF0 : 0 ≤ F) (hFB : 1 + F ≤ B) {A : ℝ}
    {y : ℕ} (hA0 : 0 ≤ A) (hA : A ≤ 2 ^ y) :
    angleE m F (B ^ 7 * B ^ 4) A ≤ 2 ^ (2 * B ^ 2 + 12 * B + 1 + y) := by
  unfold angleE
  have hm : (m : ℝ) ≤ 2 ^ B := by
    have : m ≤ 2 ^ B := hmB.trans (Nat.lt_two_pow_self).le
    exact_mod_cast this
  have hF1 : (1 : ℝ) ≤ 1 + F := by linarith
  have hpow : (1 + F) ^ (2 * m) ≤ 2 ^ (2 * B * B) := by
    calc (1 + F) ^ (2 * m) ≤ (1 + F) ^ (2 * B) := pow_le_pow_right₀ hF1 (by omega)
      _ ≤ (B : ℝ) ^ (2 * B) := pow_le_pow_left₀ (by linarith) hFB _
      _ ≤ 2 ^ (2 * B * B) := natCast_pow_le_two_pow B (2 * B)
  calc (m : ℝ) * ((1 + F) ^ (2 * m) * ((((B ^ 7 * B ^ 4 : ℕ) : ℝ) + 1) * A))
      ≤ 2 ^ B * (2 ^ (2 * B * B) * (2 ^ (11 * B + 1) * 2 ^ y)) := by
        gcongr
        exact paramQ11_le
    _ = 2 ^ (B + 2 * B * B + (11 * B + 1) + y) := by simp only [pow_add]; ring
    _ = 2 ^ (2 * B ^ 2 + 12 * B + 1 + y) := by congr 1; ring

omit hB in
theorem angleLiouville_le {G : GaussianInt[X]} (hG0 : G ≠ 0) (hg : G.natDegree ≤ B)
    (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ 2 ^ B) {m : ℕ} (hmB : m ≤ B) {F : ℝ} {q : ℕ} {A : ℝ}
    {x : ℕ} (hE0 : 0 ≤ angleE m F q A) (hE : angleE m F q A ≤ 2 ^ x) :
    angleLiouville G m F q A ≤
      2 ^ ((B ^ 2 + B) * x + (B + 2 * B ^ 2) * q + B ^ 3 + 2 * B ^ 2 + 4 * B) := by
  unfold angleLiouville
  set E := angleE m F q A
  have hmB' : (m : ℝ) ≤ 2 ^ B := by
    have : m ≤ 2 ^ B := hmB.trans (Nat.lt_two_pow_self).le
    exact_mod_cast this
  have hm1 : (m : ℝ) + 1 ≤ 2 ^ B := by
    have : m + 1 ≤ 2 ^ B := (Nat.succ_le_succ hmB).trans Nat.lt_two_pow_self
    exact_mod_cast this
  have h2m : (2 : ℝ) ^ m ≤ 2 ^ B := two_pow_mono hmB
  have hX : (m : ℝ) * (E * 2 ^ q) ≤ 2 ^ (B + x + q) := by
    calc (m : ℝ) * (E * 2 ^ q) ≤ 2 ^ B * (2 ^ x * 2 ^ q) :=
          mul_le_mul hmB' (mul_le_mul hE le_rfl (by positivity) (by positivity))
            (by positivity) (by positivity)
      _ = 2 ^ (B + x + q) := by rw [pow_add, pow_add]; ring
  have hXm : ((m : ℝ) * (E * 2 ^ q)) ^ m ≤ 2 ^ ((B + x + q) * B) := by
    calc ((m : ℝ) * (E * 2 ^ q)) ^ m ≤ (2 ^ (B + x + q)) ^ m :=
          pow_le_pow_left₀ (by positivity) hX _
      _ ≤ (2 ^ (B + x + q)) ^ B := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hmB
      _ = 2 ^ ((B + x + q) * B) := by rw [← pow_mul]
  have hY : (m : ℝ) * E ≤ 2 ^ (B + x) := by
    rw [pow_add]; exact mul_le_mul hmB' hE hE0 (by positivity)
  have hYm : (2 : ℝ) ^ m * ((m : ℝ) * E) ^ m ≤ 2 ^ (B + (B + x) * B) := by
    rw [pow_add]
    refine mul_le_mul h2m ?_ (by positivity) (by positivity)
    calc ((m : ℝ) * E) ^ m ≤ (2 ^ (B + x)) ^ m := pow_le_pow_left₀ (by positivity) hY _
      _ ≤ (2 ^ (B + x)) ^ B := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hmB
      _ = 2 ^ ((B + x) * B) := by rw [← pow_mul]
  have hYg : ((2 : ℝ) ^ m * ((m : ℝ) * E) ^ m) ^ (G.natDegree - 1) ≤
      2 ^ ((B + (B + x) * B) * B) := by
    calc ((2 : ℝ) ^ m * ((m : ℝ) * E) ^ m) ^ (G.natDegree - 1)
        ≤ (2 ^ (B + (B + x) * B)) ^ (G.natDegree - 1) := pow_le_pow_left₀ (by positivity) hYm _
      _ ≤ (2 ^ (B + (B + x) * B)) ^ B := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)
      _ = 2 ^ ((B + (B + x) * B) * B) := by rw [← pow_mul]
  have hM : (G.map toComplex).mahlerMeasure ^ (q * m) ≤ 2 ^ (2 * B * (q * B)) := by
    have hM1 := mahlerMeasure_le hg hcoeff
    have hG1 : 1 ≤ (G.map toComplex).mahlerMeasure := one_le_mahlerMeasure_of_ne_zero hG0
    calc (G.map toComplex).mahlerMeasure ^ (q * m) ≤ (G.map toComplex).mahlerMeasure ^ (q * B) :=
          pow_le_pow_right₀ hG1 (Nat.mul_le_mul_left _ hmB)
      _ ≤ (2 ^ (2 * B)) ^ (q * B) := pow_le_pow_left₀ (mahlerMeasure_nonneg _) hM1 _
      _ = 2 ^ (2 * B * (q * B)) := by rw [← pow_mul]
  calc ((m : ℝ) + 1) * ((m : ℝ) * ((2 ^ m * ((m : ℝ) * (E * 2 ^ q)) ^ m) * 2 ^ m)) *
        ((2 ^ m * ((m : ℝ) * E) ^ m) ^ (G.natDegree - 1) * (G.map toComplex).mahlerMeasure ^ (q * m))
      ≤ 2 ^ B * (2 ^ B * ((2 ^ B * 2 ^ ((B + x + q) * B)) * 2 ^ B)) *
          (2 ^ ((B + (B + x) * B) * B) * 2 ^ (2 * B * (q * B))) := by
        gcongr
        all_goals first
          | exact mul_nonneg (pow_nonneg (mul_nonneg (by positivity)
              (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hE0) _)) _)
              (pow_nonneg (mahlerMeasure_nonneg _) _)
          | exact pow_nonneg (mahlerMeasure_nonneg _) _
    _ = 2 ^ (B + (B + (B + (B + x + q) * B + B)) + ((B + (B + x) * B) * B + 2 * B * (q * B))) := by
        simp only [pow_add]
    _ = 2 ^ ((B ^ 2 + B) * x + (B + 2 * B ^ 2) * q + B ^ 3 + 2 * B ^ 2 + 4 * B) := by
        congr 1; ring

/-- The exponent of the inverse Liouville threshold. -/
def dExpA (B t : ℕ) : ℕ :=
  B * t + (B ^ 2 + B) * (2 * B ^ 2 + 12 * B + 1 + (15 * B ^ 13 + (12 * B + 3) * t)) +
    (B + 2 * B ^ 2) * (B ^ 7 * B ^ 4) + B ^ 3 + 2 * B ^ 2 + 4 * B

theorem deltaInvA_le {G : GaussianInt[X]} (hG0 : G ≠ 0) (hg : G.natDegree ≤ B)
    (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ 2 ^ B) {a m : ℕ} (haB : a ≤ B) (hmB : m ≤ B) {F : ℝ}
    (hF0 : 0 ≤ F) (hFB : 1 + F ≤ B) {Cc : ℝ} (hCc0 : 0 ≤ Cc) (hCc : Cc ≤ 2 ^ (14 * B ^ 13))
    (t : ℕ) :
    deltaInvA G a m F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t ≤ 2 ^ dExpA B t := by
  unfold deltaInvA
  have hA := heightQA_le' hB haB hF0 hFB hCc0 hCc t
  have hA0 : 0 ≤ heightQA a F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t := by
    unfold heightQA; have : (0 : ℝ) ≤ 1 + F := by linarith
    positivity
  have hE := angleE_le hB hmB hF0 hFB hA0 hA
  have hE0 : 0 ≤ angleE m F (B ^ 7 * B ^ 4) (heightQA a F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t) := by
    unfold angleE; have : (0 : ℝ) ≤ 1 + F := by linarith
    positivity
  have hL := angleLiouville_le hG0 hg hcoeff hmB hE0 hE
  have ha : (a : ℝ) ^ t ≤ 2 ^ (B * t) := by
    have : (a : ℝ) ≤ 2 ^ B := by
      have : a ≤ 2 ^ B := haB.trans (Nat.lt_two_pow_self).le
      exact_mod_cast this
    exact pow_le_two_pow (by positivity) this t
  calc (a : ℝ) ^ t * angleLiouville G m F (B ^ 7 * B ^ 4)
        (heightQA a F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t)
      ≤ 2 ^ (B * t) * 2 ^ ((B ^ 2 + B) * (2 * B ^ 2 + 12 * B + 1 +
          (15 * B ^ 13 + (12 * B + 3) * t)) + (B + 2 * B ^ 2) * (B ^ 7 * B ^ 4) + B ^ 3 +
            2 * B ^ 2 + 4 * B) := mul_le_mul ha hL (by
              unfold angleLiouville; have := (G.map toComplex).mahlerMeasure_nonneg
              positivity) (by positivity)
    _ = 2 ^ dExpA B t := by rw [← pow_add]; unfold dExpA; congr 1; ring

theorem growthA_le {θ : ℝ} (hθB : |θ| ≤ B) {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : Cc ≤ 2 ^ (14 * B ^ 13)) :
    growthA (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| ≤ 2 ^ (15 * B ^ 13) := by
  unfold growthA
  have h8 : (8 * ((B ^ 4 : ℕ) : ℝ)) ^ (4 * B ^ 11) ≤ 2 ^ ((4 * B + 3) * (4 * B ^ 11)) := by
    refine pow_le_two_pow (by positivity) ?_ _
    push_cast
    rw [pow_add]
    have := natCast_pow_le_two_pow B 4
    nlinarith
  have hexp : Real.exp (((B ^ 7 : ℕ) : ℝ) * |θ| * (8 * ((B ^ 4 : ℕ) : ℝ))) ≤
      2 ^ (2 * (8 * B ^ 12)) := by
    have : ((B ^ 7 : ℕ) : ℝ) * |θ| * (8 * ((B ^ 4 : ℕ) : ℝ)) ≤ ((8 * B ^ 12 : ℕ) : ℝ) := by
      push_cast
      calc (B : ℝ) ^ 7 * |θ| * (8 * (B : ℝ) ^ 4) ≤ (B : ℝ) ^ 7 * B * (8 * (B : ℝ) ^ 4) := by
            gcongr
        _ = 8 * (B : ℝ) ^ 12 := by ring
    exact (Real.exp_le_exp.mpr this).trans (exp_natCast_le_two_pow _)
  calc (((B ^ 7 : ℕ) : ℝ) + 1) * ((4 * B ^ 11 : ℕ) : ℝ) * Cc *
        (8 * ((B ^ 4 : ℕ) : ℝ)) ^ (4 * B ^ 11) *
        Real.exp (((B ^ 7 : ℕ) : ℝ) * |θ| * (8 * ((B ^ 4 : ℕ) : ℝ)))
      ≤ 2 ^ (18 * B + 3) * 2 ^ (14 * B ^ 13) * 2 ^ ((4 * B + 3) * (4 * B ^ 11)) *
          2 ^ (2 * (8 * B ^ 12)) := by
        gcongr
        exact angU_le hB
    _ = 2 ^ (18 * B + 3 + 14 * B ^ 13 + (4 * B + 3) * (4 * B ^ 11) + 2 * (8 * B ^ 12)) := by
        simp only [pow_add]
    _ ≤ 2 ^ (15 * B ^ 13) := by
        apply two_pow_mono
        have f12 : 128 * B ^ 12 ≤ B ^ 13 := Bfact hB 12
        have f11 : 128 * B ^ 11 ≤ B ^ 12 := Bfact hB 11
        have f1 : B ≤ B ^ 11 := Nat.le_self_pow (by norm_num) B
        ring_nf
        omega

theorem factorial_le_angle {t : ℕ} (ht : t ≤ 2 * ((B ^ 7 + 1) * (4 * B ^ 11))) :
    (t.factorial : ℝ) ≤ 2 ^ ((18 * B + 4) * t) := by
  have h1 : t ≤ 2 ^ (18 * B + 4) := by
    have hU := angU_nat hB
    have hB18 := natPow_le_two_pow B 18
    calc t ≤ 16 * B ^ 18 := by omega
      _ ≤ 16 * 2 ^ (18 * B) := by omega
      _ = 2 ^ (18 * B + 4) := by ring
  calc (t.factorial : ℝ) ≤ ((t ^ t : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow t
    _ ≤ ((2 ^ (18 * B + 4)) ^ t : ℕ) := by exact_mod_cast Nat.pow_le_pow_left h1 t
    _ = 2 ^ ((18 * B + 4) * t) := by push_cast; rw [← pow_mul]

/-- **Condition H1** along the chain. -/
theorem condition_H1_angle {G : GaussianInt[X]} (hG0 : G ≠ 0) (hg : G.natDegree ≤ B)
    (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ 2 ^ B) {a m : ℕ} (haB : a ≤ B) (hmB : m ≤ B) {F : ℝ}
    (hF0 : 0 ≤ F) (hFB : 1 + F ≤ B) {θ : ℝ} (hθB : |θ| ≤ B) :
    ∀ T, B ^ 12 ≤ T → T < (B ^ 7 + 1) * (4 * B ^ 11) → ∀ t < 2 * T,
      t.factorial * growthA (B ^ 7) (4 * B ^ 11) (B ^ 4)
          (angSiegelBound G (2 ^ B) a F (B ^ 7) (4 * B ^ 11) (B ^ 4) (B ^ 12)) |θ| /
          7 ^ (B ^ 4 * T) *
        deltaInvA G a m F (B ^ 7) (4 * B ^ 11) (B ^ 4)
          (angSiegelBound G (2 ^ B) a F (B ^ 7) (4 * B ^ 11) (B ^ 4) (B ^ 12)) t ≤ 1 / 4 := by
  intro T hT hTU t ht
  set Cc := angSiegelBound G (2 ^ B) a F (B ^ 7) (4 * B ^ 11) (B ^ 4) (B ^ 12)
  have hCc := angSiegelBound_le hB hg haB hF0 hFB
  have hCc0 : 0 ≤ Cc := by
    simp only [Cc, angSiegelBound]
    have : (0 : ℝ) ≤ 1 + (2 ^ B) ^ G.natDegree := by positivity
    have : (0 : ℝ) ≤ 1 + F := by linarith
    positivity
  have hfac := factorial_le_angle hB (t := t) (by omega)
  have hgr := growthA_le hB hθB hCc0 hCc
  have hdi := deltaInvA_le hB hG0 hg hcoeff haB hmB hF0 hFB hCc0 hCc t
  have hgr0 : 0 ≤ growthA (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| := by
    unfold growthA; exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCc0)
      (by positivity)) (Real.exp_pos _).le
  have hdi0 : 0 ≤ deltaInvA G a m F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t := by
    unfold deltaInvA angleLiouville
    have := (G.map toComplex).mahlerMeasure_nonneg
    have : 0 ≤ angleE m F (B ^ 7 * B ^ 4) (heightQA a F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t) := by
      unfold angleE heightQA; have : (0 : ℝ) ≤ 1 + F := by linarith
      positivity
    positivity
  set E := (18 * B + 4) * t + 15 * B ^ 13 + dExpA B t
  have hnum : (t.factorial : ℝ) * growthA (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| *
      deltaInvA G a m F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t ≤ 2 ^ E := by
    calc (t.factorial : ℝ) * growthA (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| *
          deltaInvA G a m F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t
        ≤ 2 ^ ((18 * B + 4) * t) * 2 ^ (15 * B ^ 13) * 2 ^ dExpA B t := by gcongr
      _ = 2 ^ E := by simp only [E, pow_add]
  have hexp : E + 2 ≤ 2 * (B ^ 4 * T) := by
    have k0 : E + 2 = (12 * B ^ 3 + 15 * B ^ 2 + 22 * B + 4) * t +
        (15 * B ^ 13 + (B ^ 2 + B) * (2 * B ^ 2 + 12 * B + 1 + 15 * B ^ 13) +
          (B + 2 * B ^ 2) * (B ^ 7 * B ^ 4) + B ^ 3 + 2 * B ^ 2 + 4 * B + 2) := by
      simp only [E, dExpA]; ring
    have k1 : (12 * B ^ 3 + 15 * B ^ 2 + 22 * B + 4) * t ≤ 13 * B ^ 3 * (2 * T) := by
      have c1 : 12 * B ^ 3 + 15 * B ^ 2 + 22 * B + 4 ≤ 13 * B ^ 3 := by
        have : 128 * B ^ 2 ≤ B ^ 3 := Bfact hB 2
        have : 128 * B ≤ B ^ 2 := by nlinarith
        omega
      calc (12 * B ^ 3 + 15 * B ^ 2 + 22 * B + 4) * t ≤ 13 * B ^ 3 * t := Nat.mul_le_mul_right _ c1
        _ ≤ 13 * B ^ 3 * (2 * T) := Nat.mul_le_mul_left _ (by omega)
    have k2 : 15 * B ^ 13 + (B ^ 2 + B) * (2 * B ^ 2 + 12 * B + 1 + 15 * B ^ 13) +
        (B + 2 * B ^ 2) * (B ^ 7 * B ^ 4) + B ^ 3 + 2 * B ^ 2 + 4 * B + 2 ≤ 16 * B ^ 15 := by
      have f2 : 128 * B ^ 2 ≤ B ^ 3 := Bfact hB 2
      have f3 : 128 * B ^ 3 ≤ B ^ 4 := Bfact hB 3
      have f4 : 128 * B ^ 4 ≤ B ^ 5 := Bfact hB 4
      have f5 : 128 * B ^ 5 ≤ B ^ 6 := Bfact hB 5
      have f6 : 128 * B ^ 6 ≤ B ^ 7 := Bfact hB 6
      have f7 : 128 * B ^ 7 ≤ B ^ 8 := Bfact hB 7
      have f8 : 128 * B ^ 8 ≤ B ^ 9 := Bfact hB 8
      have f9 : 128 * B ^ 9 ≤ B ^ 10 := Bfact hB 9
      have f10 : 128 * B ^ 10 ≤ B ^ 11 := Bfact hB 10
      have f11 : 128 * B ^ 11 ≤ B ^ 12 := Bfact hB 11
      have f12 : 128 * B ^ 12 ≤ B ^ 13 := Bfact hB 12
      have f13 : 128 * B ^ 13 ≤ B ^ 14 := Bfact hB 13
      have f14 : 128 * B ^ 14 ≤ B ^ 15 := Bfact hB 14
      have f1 : 128 * B ≤ B ^ 2 := by nlinarith
      ring_nf
      omega
    have k3 : 16 * B ^ 15 ≤ 16 * B ^ 3 * T := by
      calc 16 * B ^ 15 = 16 * B ^ 3 * B ^ 12 := by ring
        _ ≤ 16 * B ^ 3 * T := Nat.mul_le_mul_left _ hT
    have k4 : 13 * B ^ 3 * (2 * T) + 16 * B ^ 3 * T ≤ 2 * (B ^ 4 * T) := by
      have c : 42 * B ^ 3 ≤ 2 * B ^ 4 := by
        have : 128 * B ^ 3 ≤ B ^ 4 := Bfact hB 3
        omega
      calc 13 * B ^ 3 * (2 * T) + 16 * B ^ 3 * T = 42 * B ^ 3 * T := by ring
        _ ≤ 2 * B ^ 4 * T := Nat.mul_le_mul_right _ c
        _ = 2 * (B ^ 4 * T) := by ring
    omega
  have h7 : (2 : ℝ) ^ (E + 2) ≤ 7 ^ (B ^ 4 * T) :=
    (two_pow_mono hexp).trans (two_pow_le_seven_pow _)
  have h7pos : (0 : ℝ) < 7 ^ (B ^ 4 * T) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ h7pos]
  calc (t.factorial : ℝ) * growthA (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| *
        deltaInvA G a m F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t ≤ 2 ^ E := hnum
    _ = 1 / 4 * 2 ^ (E + 2) := by rw [pow_add]; ring
    _ ≤ 1 / 4 * 7 ^ (B ^ 4 * T) := by gcongr

omit hB in
theorem paramN22_le {T : ℕ} (hT : T ≤ 8 * B ^ 18) : B ^ 4 * T ≤ 2 ^ (22 * B + 3) := by
  have hB22 := natPow_le_two_pow B 22
  calc B ^ 4 * T ≤ B ^ 4 * (8 * B ^ 18) := Nat.mul_le_mul_left _ hT
    _ = 8 * B ^ 22 := by ring
    _ ≤ 8 * 2 ^ (22 * B) := by omega
    _ = 2 ^ (22 * B + 3) := by ring

omit hB in
theorem interpConst_le_angle {T : ℕ} (hT : T ≤ 8 * B ^ 18) :
    (interpConst (B ^ 4) T : ℝ) ≤ 2 ^ ((22 * B + 3) * (B ^ 4 * T + 1) +
      (B ^ 4 * T) * ((22 * B + 3) * T + 4 * B * (B ^ 4 * T))) := by
  have hn := paramN22_le hT
  unfold interpConst
  set n := B ^ 4 * T
  have hh : B ^ 4 ≤ 2 ^ (4 * B) := natPow_le_two_pow B 4
  have h1 : n ^ (n + 1) * (n ^ T * (B ^ 4) ^ n) ^ n ≤
      (2 ^ (22 * B + 3)) ^ (n + 1) * ((2 ^ (22 * B + 3)) ^ T * (2 ^ (4 * B)) ^ n) ^ n := by
    gcongr
  have h2 : (2 ^ (22 * B + 3)) ^ (n + 1) * ((2 ^ (22 * B + 3)) ^ T * (2 ^ (4 * B)) ^ n) ^ n =
      2 ^ ((22 * B + 3) * (n + 1) + n * ((22 * B + 3) * T + 4 * B * n)) := by
    simp only [← pow_mul, ← pow_add]
    ring_nf
  have := h1.trans_eq h2
  exact_mod_cast this

omit hB in
theorem eightH4_pow_le (k : ℕ) : (8 * ((B ^ 4 : ℕ) : ℝ)) ^ k ≤ 2 ^ ((4 * B + 3) * k) := by
  refine pow_le_two_pow (by positivity) ?_ _
  push_cast
  rw [pow_add]
  have := natCast_pow_le_two_pow B 4
  nlinarith

/-- The total exponent of condition H2. -/
theorem exponent_H2_angle {T t : ℕ} (hT : T ≤ 8 * B ^ 18) (ht : t ≤ 16 * B ^ 18) :
    dExpA B t + (((22 * B + 3) + ((22 * B + 3) * (B ^ 4 * T + 1) +
        (B ^ 4 * T) * ((22 * B + 3) * T + 4 * B * (B ^ 4 * T))) + (22 * B + 3) * t +
        (4 * B + 3) * (B ^ 4 * T)) +
      (16 * B ^ 13 + (12 * B + 3) * T) + (16 * B ^ 13 + (12 * B + 3) * t) + 3) ≤ B ^ 48 := by
  set n := B ^ 4 * T with hn
  have hn' : n ≤ 8 * B ^ 22 := by
    calc n ≤ B ^ 4 * (8 * B ^ 18) := Nat.mul_le_mul_left _ hT
      _ = 8 * B ^ 22 := by ring
  have c1 : 22 * B + 3 ≤ 23 * B := by omega
  have c2 : 12 * B + 3 ≤ 13 * B := by omega
  have c3 : 4 * B + 3 ≤ 5 * B := by omega
  have pd : dExpA B t ≤ 16 * B ^ 15 + 208 * B ^ 21 + B ^ 15 := by
    have hx : dExpA B t = (12 * B ^ 3 + 15 * B ^ 2 + 4 * B) * t +
        ((B ^ 2 + B) * (2 * B ^ 2 + 12 * B + 1 + 15 * B ^ 13) + (B + 2 * B ^ 2) * (B ^ 7 * B ^ 4) +
          B ^ 3 + 2 * B ^ 2 + 4 * B) := by unfold dExpA; ring
    have q1 : (12 * B ^ 3 + 15 * B ^ 2 + 4 * B) * t ≤ 13 * B ^ 3 * (16 * B ^ 18) := by
      have : 12 * B ^ 3 + 15 * B ^ 2 + 4 * B ≤ 13 * B ^ 3 := by
        have : 128 * B ^ 2 ≤ B ^ 3 := Bfact hB 2
        have : 128 * B ≤ B ^ 2 := by nlinarith
        omega
      exact Nat.mul_le_mul this ht
    have q2 : (B ^ 2 + B) * (2 * B ^ 2 + 12 * B + 1 + 15 * B ^ 13) + (B + 2 * B ^ 2) * (B ^ 7 * B ^ 4) +
          B ^ 3 + 2 * B ^ 2 + 4 * B ≤ 16 * B ^ 15 + B ^ 15 := by
      have f2 : 128 * B ^ 2 ≤ B ^ 3 := Bfact hB 2
      have f3 : 128 * B ^ 3 ≤ B ^ 4 := Bfact hB 3
      have f4 : 128 * B ^ 4 ≤ B ^ 5 := Bfact hB 4
      have f5 : 128 * B ^ 5 ≤ B ^ 6 := Bfact hB 5
      have f6 : 128 * B ^ 6 ≤ B ^ 7 := Bfact hB 6
      have f7 : 128 * B ^ 7 ≤ B ^ 8 := Bfact hB 7
      have f8 : 128 * B ^ 8 ≤ B ^ 9 := Bfact hB 8
      have f9 : 128 * B ^ 9 ≤ B ^ 10 := Bfact hB 9
      have f10 : 128 * B ^ 10 ≤ B ^ 11 := Bfact hB 10
      have f11 : 128 * B ^ 11 ≤ B ^ 12 := Bfact hB 11
      have f12 : 128 * B ^ 12 ≤ B ^ 13 := Bfact hB 12
      have f13 : 128 * B ^ 13 ≤ B ^ 14 := Bfact hB 13
      have f14 : 128 * B ^ 14 ≤ B ^ 15 := Bfact hB 14
      have f1 : 128 * B ≤ B ^ 2 := by nlinarith
      ring_nf
      omega
    have e : 13 * B ^ 3 * (16 * B ^ 18) = 208 * B ^ 21 := by ring
    omega
  have pa : (22 * B + 3) * (n + 1) ≤ 184 * B ^ 23 + 23 * B := by
    calc (22 * B + 3) * (n + 1) ≤ (23 * B) * (8 * B ^ 22 + 1) := by gcongr
      _ = 184 * B ^ 23 + 23 * B := by ring
  have pb : n * ((22 * B + 3) * T) ≤ 1472 * B ^ 41 := by
    calc n * ((22 * B + 3) * T) ≤ (8 * B ^ 22) * ((23 * B) * (8 * B ^ 18)) := by gcongr
      _ = 1472 * B ^ 41 := by ring
  have pc : n * (4 * B * n) ≤ 256 * B ^ 45 := by
    calc n * (4 * B * n) ≤ (8 * B ^ 22) * (4 * B * (8 * B ^ 22)) := by gcongr
      _ = 256 * B ^ 45 := by ring
  have pe : (22 * B + 3) * t ≤ 368 * B ^ 19 := by
    calc (22 * B + 3) * t ≤ (23 * B) * (16 * B ^ 18) := by gcongr
      _ = 368 * B ^ 19 := by ring
  have pf : (4 * B + 3) * n ≤ 40 * B ^ 23 := by
    calc (4 * B + 3) * n ≤ (5 * B) * (8 * B ^ 22) := by gcongr
      _ = 40 * B ^ 23 := by ring
  have pg : (12 * B + 3) * T ≤ 104 * B ^ 19 := by
    calc (12 * B + 3) * T ≤ (13 * B) * (8 * B ^ 18) := by gcongr
      _ = 104 * B ^ 19 := by ring
  have ph : (12 * B + 3) * t ≤ 208 * B ^ 19 := by
    calc (12 * B + 3) * t ≤ (13 * B) * (16 * B ^ 18) := by gcongr
      _ = 208 * B ^ 19 := by ring
  have e5 : n * ((22 * B + 3) * T + 4 * B * n) = n * ((22 * B + 3) * T) + n * (4 * B * n) := by
    ring
  rw [e5]
  have f1 : 128 * B ≤ B ^ 2 := by nlinarith
  have f2 : 128 * B ^ 2 ≤ B ^ 3 := Bfact hB 2
  have f3 : 128 * B ^ 3 ≤ B ^ 4 := Bfact hB 3
  have f4 : 128 * B ^ 4 ≤ B ^ 5 := Bfact hB 4
  have f5 : 128 * B ^ 5 ≤ B ^ 6 := Bfact hB 5
  have f6 : 128 * B ^ 6 ≤ B ^ 7 := Bfact hB 6
  have f7 : 128 * B ^ 7 ≤ B ^ 8 := Bfact hB 7
  have f8 : 128 * B ^ 8 ≤ B ^ 9 := Bfact hB 8
  have f9 : 128 * B ^ 9 ≤ B ^ 10 := Bfact hB 9
  have f10 : 128 * B ^ 10 ≤ B ^ 11 := Bfact hB 10
  have f11 : 128 * B ^ 11 ≤ B ^ 12 := Bfact hB 11
  have f12 : 128 * B ^ 12 ≤ B ^ 13 := Bfact hB 12
  have f13 : 128 * B ^ 13 ≤ B ^ 14 := Bfact hB 13
  have f14 : 128 * B ^ 14 ≤ B ^ 15 := Bfact hB 14
  have f15 : 128 * B ^ 15 ≤ B ^ 16 := Bfact hB 15
  have f16 : 128 * B ^ 16 ≤ B ^ 17 := Bfact hB 16
  have f17 : 128 * B ^ 17 ≤ B ^ 18 := Bfact hB 17
  have f18 : 128 * B ^ 18 ≤ B ^ 19 := Bfact hB 18
  have f19 : 128 * B ^ 19 ≤ B ^ 20 := Bfact hB 19
  have f20 : 128 * B ^ 20 ≤ B ^ 21 := Bfact hB 20
  have f21 : 128 * B ^ 21 ≤ B ^ 22 := Bfact hB 21
  have f22 : 128 * B ^ 22 ≤ B ^ 23 := Bfact hB 22
  have f23 : 128 * B ^ 23 ≤ B ^ 24 := Bfact hB 23
  have f24 : 128 * B ^ 24 ≤ B ^ 25 := Bfact hB 24
  have f25 : 128 * B ^ 25 ≤ B ^ 26 := Bfact hB 25
  have f26 : 128 * B ^ 26 ≤ B ^ 27 := Bfact hB 26
  have f27 : 128 * B ^ 27 ≤ B ^ 28 := Bfact hB 27
  have f28 : 128 * B ^ 28 ≤ B ^ 29 := Bfact hB 28
  have f29 : 128 * B ^ 29 ≤ B ^ 30 := Bfact hB 29
  have f30 : 128 * B ^ 30 ≤ B ^ 31 := Bfact hB 30
  have f31 : 128 * B ^ 31 ≤ B ^ 32 := Bfact hB 31
  have f32 : 128 * B ^ 32 ≤ B ^ 33 := Bfact hB 32
  have f33 : 128 * B ^ 33 ≤ B ^ 34 := Bfact hB 33
  have f34 : 128 * B ^ 34 ≤ B ^ 35 := Bfact hB 34
  have f35 : 128 * B ^ 35 ≤ B ^ 36 := Bfact hB 35
  have f36 : 128 * B ^ 36 ≤ B ^ 37 := Bfact hB 36
  have f37 : 128 * B ^ 37 ≤ B ^ 38 := Bfact hB 37
  have f38 : 128 * B ^ 38 ≤ B ^ 39 := Bfact hB 38
  have f39 : 128 * B ^ 39 ≤ B ^ 40 := Bfact hB 39
  have f40 : 128 * B ^ 40 ≤ B ^ 41 := Bfact hB 40
  have f41 : 128 * B ^ 41 ≤ B ^ 42 := Bfact hB 41
  have f42 : 128 * B ^ 42 ≤ B ^ 43 := Bfact hB 42
  have f43 : 128 * B ^ 43 ≤ B ^ 44 := Bfact hB 43
  have f44 : 128 * B ^ 44 ≤ B ^ 45 := Bfact hB 44
  have f45 : 128 * B ^ 45 ≤ B ^ 46 := Bfact hB 45
  have f46 : 128 * B ^ 46 ≤ B ^ 47 := Bfact hB 46
  have f47 : 128 * B ^ 47 ≤ B ^ 48 := Bfact hB 47
  have fB : 1 ≤ B ^ 13 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The small parameter `ρ = 2^{-(B⁴⁸ + 1)}`. -/
noncomputable def rhoA (B : ℕ) : ℝ := (1 / 2) ^ (B ^ 48 + 1)

/-- **Condition H2** along the chain. -/
theorem condition_H2_angle {G : GaussianInt[X]} (hG0 : G ≠ 0) (hg : G.natDegree ≤ B)
    (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ 2 ^ B) {a m : ℕ} (haB : a ≤ B) (hmB : m ≤ B) {F : ℝ}
    (hF0 : 0 ≤ F) (hFB : 1 + F ≤ B) {θ : ℝ} (hθB : |θ| ≤ B) :
    ∀ T, B ^ 12 ≤ T → T < (B ^ 7 + 1) * (4 * B ^ 11) → ∀ t < 2 * T,
      deltaInvA G a m F (B ^ 7) (4 * B ^ 11) (B ^ 4)
          (angSiegelBound G (2 ^ B) a F (B ^ 7) (4 * B ^ 11) (B ^ 4) (B ^ 12)) t *
      (rhoA B * (lipS (B ^ 7) (4 * B ^ 11) (B ^ 4)
          (angSiegelBound G (2 ^ B) a F (B ^ 7) (4 * B ^ 11) (B ^ 4) (B ^ 12)) |θ| T + 1) *
        (t.factorial * ((((B ^ 4 * T : ℕ) : ℝ)) * interpConst (B ^ 4) T *
          (8 * ((B ^ 4 : ℕ) : ℝ)) ^ (B ^ 4 * T)) / 7 ^ (B ^ 4 * T) +
          (((B ^ 4 * T : ℕ) : ℝ)) * interpConst (B ^ 4) T *
            ((((B ^ 4 * T : ℕ) : ℝ)) ^ t * ((B ^ 4 : ℕ) : ℝ) ^ (B ^ 4 * T))) + rhoA B +
        rhoA B * lipS (B ^ 7) (4 * B ^ 11) (B ^ 4)
          (angSiegelBound G (2 ^ B) a F (B ^ 7) (4 * B ^ 11) (B ^ 4) (B ^ 12)) |θ| t) ≤
        1 / 2 := by
  intro T hT hTU t ht
  set Cc := angSiegelBound G (2 ^ B) a F (B ^ 7) (4 * B ^ 11) (B ^ 4) (B ^ 12)
  have hCc := angSiegelBound_le hB hg haB hF0 hFB
  have hCc0 : 0 ≤ Cc := by
    simp only [Cc, angSiegelBound]
    have : (0 : ℝ) ≤ 1 + (2 ^ B) ^ G.natDegree := by positivity
    have : (0 : ℝ) ≤ 1 + F := by linarith
    positivity
  have hU := angU_nat hB
  have hTle : T ≤ 8 * B ^ 18 := by omega
  have htle : t ≤ 16 * B ^ 18 := by omega
  set n := B ^ 4 * T with hn
  set d := dExpA B t
  set eK := (22 * B + 3) * (n + 1) + n * ((22 * B + 3) * T + 4 * B * n)
  set aa := (22 * B + 3) + eK + (22 * B + 3) * t + (4 * B + 3) * n
  set b := 16 * B ^ 13 + (12 * B + 3) * T
  set c := 16 * B ^ 13 + (12 * B + 3) * t
  have hD : deltaInvA G a m F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t ≤ 2 ^ d :=
    deltaInvA_le hB hG0 hg hcoeff haB hmB hF0 hFB hCc0 hCc t
  have hLT : lipS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| T ≤ 2 ^ b := lipS_le' hB hθB hCc0 hCc T
  have hLt : lipS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| t ≤ 2 ^ c := lipS_le' hB hθB hCc0 hCc t
  have hK : (interpConst (B ^ 4) T : ℝ) ≤ 2 ^ eK := interpConst_le_angle hTle
  have hnr : ((n : ℕ) : ℝ) ≤ 2 ^ (22 * B + 3) := by exact_mod_cast paramN22_le hTle
  have h8 := eightH4_pow_le (B := B) n
  have hnt : ((n : ℕ) : ℝ) ^ t ≤ 2 ^ ((22 * B + 3) * t) := pow_le_two_pow (by positivity) hnr t
  have hhn : ((B ^ 4 : ℕ) : ℝ) ^ n ≤ 2 ^ (4 * B * n) :=
    pow_le_two_pow (by positivity) (by push_cast; exact natCast_pow_le_two_pow B 4) n
  have hfac := factorial_le_angle hB (t := t) (by omega)
  have hK0 : (0 : ℝ) ≤ interpConst (B ^ 4) T := by positivity
  have hD0 : 0 ≤ deltaInvA G a m F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t := by
    unfold deltaInvA angleLiouville
    have := (G.map toComplex).mahlerMeasure_nonneg
    have : 0 ≤ angleE m F (B ^ 7 * B ^ 4) (heightQA a F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t) := by
      unfold angleE heightQA; have : (0 : ℝ) ≤ 1 + F := by linarith
      positivity
    positivity
  have hLT0 := lipS_nonneg (J := B ^ 7) (L := 4 * B ^ 11) (h := B ^ 4) hCc0 (abs_nonneg θ) T
  have hLt0 := lipS_nonneg (J := B ^ 7) (L := 4 * B ^ 11) (h := B ^ 4) hCc0 (abs_nonneg θ) t
  have hX1 : (t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
      (8 * ((B ^ 4 : ℕ) : ℝ)) ^ n) / 7 ^ n ≤ 2 ^ aa := by
    have h7 : (1 : ℝ) ≤ 7 ^ n := one_le_pow₀ (by norm_num)
    calc (t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
          (8 * ((B ^ 4 : ℕ) : ℝ)) ^ n) / 7 ^ n
        ≤ (t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
          (8 * ((B ^ 4 : ℕ) : ℝ)) ^ n) := div_le_self (by positivity) h7
      _ ≤ 2 ^ ((18 * B + 4) * t) * (2 ^ (22 * B + 3) * 2 ^ eK * 2 ^ ((4 * B + 3) * n)) := by
          gcongr
      _ = 2 ^ ((18 * B + 4) * t + (22 * B + 3) + eK + (4 * B + 3) * n) := by
          simp only [pow_add]; ring
      _ ≤ 2 ^ aa := two_pow_mono (by
          simp only [aa]
          have : (18 * B + 4) * t ≤ (22 * B + 3) * t := Nat.mul_le_mul_right _ (by omega)
          omega)
  have hX2 : ((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
      (((n : ℕ) : ℝ) ^ t * ((B ^ 4 : ℕ) : ℝ) ^ n) ≤ 2 ^ aa := by
    calc ((n : ℕ) : ℝ) * interpConst (B ^ 4) T * (((n : ℕ) : ℝ) ^ t * ((B ^ 4 : ℕ) : ℝ) ^ n)
        ≤ 2 ^ (22 * B + 3) * 2 ^ eK * (2 ^ ((22 * B + 3) * t) * 2 ^ (4 * B * n)) := by gcongr
      _ = 2 ^ ((22 * B + 3) + eK + (22 * B + 3) * t + 4 * B * n) := by
          simp only [pow_add]; ring
      _ ≤ 2 ^ aa := two_pow_mono (by
          simp only [aa]
          have : 4 * B * n ≤ (4 * B + 3) * n := Nat.mul_le_mul_right _ (by omega)
          omega)
  have hpow1 : ∀ k : ℕ, (2 : ℝ) ^ k + 1 ≤ 2 ^ (k + 1) := fun k => by
    rw [pow_succ]; linarith [one_le_pow₀ (n := k) (by norm_num : (1 : ℝ) ≤ 2)]
  have hY : deltaInvA G a m F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t *
      ((lipS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| T + 1) *
        ((t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
          (8 * ((B ^ 4 : ℕ) : ℝ)) ^ n) / 7 ^ n + ((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
          (((n : ℕ) : ℝ) ^ t * ((B ^ 4 : ℕ) : ℝ) ^ n)) + 1 +
        lipS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| t) ≤ 2 ^ (B ^ 48) := by
    have hQ1 : lipS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| T + 1 ≤ 2 ^ (b + 1) := by
      have := hpow1 b; linarith
    have hsum : (t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
          (8 * ((B ^ 4 : ℕ) : ℝ)) ^ n) / 7 ^ n + ((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
          (((n : ℕ) : ℝ) ^ t * ((B ^ 4 : ℕ) : ℝ) ^ n) ≤ 2 ^ (aa + 1) := by
      have h2a : (2 : ℝ) ^ (aa + 1) = 2 * 2 ^ aa := by ring
      linarith
    have hL1 : 1 + lipS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| t ≤ 2 ^ (c + 1) := by
      have := hpow1 c; linarith
    have hinner : (lipS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| T + 1) *
        ((t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
          (8 * ((B ^ 4 : ℕ) : ℝ)) ^ n) / 7 ^ n + ((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
          (((n : ℕ) : ℝ) ^ t * ((B ^ 4 : ℕ) : ℝ) ^ n)) + 1 +
        lipS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| t ≤ 2 ^ (aa + b + c + 3) := by
      have h1 : (lipS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| T + 1) *
          ((t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
            (8 * ((B ^ 4 : ℕ) : ℝ)) ^ n) / 7 ^ n + ((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
            (((n : ℕ) : ℝ) ^ t * ((B ^ 4 : ℕ) : ℝ) ^ n)) ≤ 2 ^ (b + 1) * 2 ^ (aa + 1) :=
        mul_le_mul hQ1 hsum (by positivity) (by positivity)
      have h2 : (2 : ℝ) ^ (b + 1) * 2 ^ (aa + 1) ≤ 2 ^ (aa + b + c + 2) := by
        rw [← pow_add]; exact two_pow_mono (by omega)
      have h3 : (2 : ℝ) ^ (c + 1) ≤ 2 ^ (aa + b + c + 2) := two_pow_mono (by omega)
      have h4 : (2 : ℝ) ^ (aa + b + c + 3) = 2 * 2 ^ (aa + b + c + 2) := by
        rw [show aa + b + c + 3 = (aa + b + c + 2) + 1 by ring, pow_succ]; ring
      linarith
    calc _ ≤ 2 ^ d * 2 ^ (aa + b + c + 3) := mul_le_mul hD hinner (by positivity) (by positivity)
      _ = 2 ^ (d + (aa + b + c + 3)) := by rw [← pow_add]
      _ ≤ 2 ^ (B ^ 48) := two_pow_mono (by
          have := exponent_H2_angle hB hTle htle
          rw [← hn] at this
          simp only [d, aa, b, c, eK]
          omega)
  have hρ : rhoA B * 2 ^ (B ^ 48) = 1 / 2 := by
    have h1 : ((1 : ℝ) / 2) ^ (B ^ 48) * 2 ^ (B ^ 48) = 1 := by
      rw [← mul_pow]; norm_num
    rw [rhoA, pow_succ]
    linear_combination (1 / 2 : ℝ) * h1
  have hρ0 : 0 ≤ rhoA B := by unfold rhoA; positivity
  calc _ = rhoA B * (deltaInvA G a m F (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc t *
        ((lipS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| T + 1) *
          ((t.factorial : ℝ) * (((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
            (8 * ((B ^ 4 : ℕ) : ℝ)) ^ n) / 7 ^ n + ((n : ℕ) : ℝ) * interpConst (B ^ 4) T *
            (((n : ℕ) : ℝ) ^ t * ((B ^ 4 : ℕ) : ℝ) ^ n)) + 1 +
          lipS (B ^ 7) (4 * B ^ 11) (B ^ 4) Cc |θ| t)) := by ring
    _ ≤ rhoA B * 2 ^ (B ^ 48) := mul_le_mul_of_nonneg_left hY hρ0
    _ = 1 / 2 := hρ

end Params

/-- **Measure for an irreducible Gaussian-integer polynomial at `e^{iθ}`.** -/
theorem norm_eval_exp_angle_ge_of_irreducible {G : GaussianInt[X]} (hG : Irreducible G)
    (hdeg : 0 < G.natDegree) {B : ℕ} (hB : 128 ≤ B) (hg : G.natDegree ≤ B)
    (hcoeff : ∀ k, ‖(G.coeff k : ℂ)‖ ≤ 2 ^ B) {a : ℕ} (ha1 : 1 ≤ a) (haB : a ≤ B)
    {f : ℤ[X]} (hf : f.Monic) {m : ℕ} (hmf : f.natDegree = m) (hm : 1 ≤ m) (hmB : m ≤ B)
    {θ : ℝ} (hθ0 : θ ≠ 0) (hθB : |θ| ≤ B) {ϑ : ℂ} (hϑa : ϑ = a * θ)
    (hϑ : f.eval₂ (Int.castRingHom ℂ) ϑ = 0) {F : ℝ} (hF0 : 0 ≤ F)
    (hF : ∀ i, |(f.coeff i : ℝ)| ≤ F) (hFB : 1 + F ≤ B) :
    (1 / 2 : ℝ) ^ (B * (B ^ 48 + 1)) ≤
      ‖(G.map toComplex).eval (Complex.exp ((θ : ℂ) * Complex.I))‖ := by
  have hρ0 : 0 < rhoA B := by unfold rhoA; positivity
  have hρ1 : rhoA B ≤ 1 := by unfold rhoA; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hcount : 2 * (B ^ 12 * B ^ 4 * G.natDegree * m * 2) ≤ (B ^ 7 + 1) * (4 * B ^ 11) := by
    have h1 : B ^ 12 * B ^ 4 * G.natDegree * m ≤ B ^ 12 * B ^ 4 * B * B :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hg) hmB
    have e : (B ^ 7 + 1) * (4 * B ^ 11) = 4 * (B ^ 12 * B ^ 4 * B * B) + 4 * B ^ 11 := by ring
    omega
  have hmain := lower_bound_of_conditions_angle hG hdeg (aG := 2 ^ B) (one_le_pow₀ (by norm_num))
    hcoeff ha1 hf hmf hm hθ0 hϑa hϑ hF0 hF
    (J := B ^ 7) (L := 4 * B ^ 11) (h := B ^ 4) (T₀ := B ^ 12)
    (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ (by omega))
    (by have := Nat.one_le_pow 11 B (by omega); omega) hcount
    hρ0 hρ1 (condition_H1_angle hB hG.ne_zero hg hcoeff haB hmB hF0 hFB hθB)
    (condition_H2_angle hB hG.ne_zero hg hcoeff haB hmB hF0 hFB hθB)
  calc (1 / 2 : ℝ) ^ (B * (B ^ 48 + 1)) = rhoA B ^ B := by
        unfold rhoA; rw [← pow_mul, mul_comm]
    _ ≤ rhoA B ^ G.natDegree := pow_le_pow_of_le_one hρ0.le hρ1 hg
    _ ≤ _ := hmain

end NLQCLean.Gelfond
