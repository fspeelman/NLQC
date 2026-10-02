import NLQCLean.Bounds.NearBellSpectra
import NLQCLean.Approx.NearBellFreezing
import NLQCLean.Approx.PVMPolynomialCoverage
import NLQCLean.Approx.PVMReachableWitnessCover

/-!
# Slim witnesses near a maximally entangled basis

An accurate protocol for a basis near the generalized Bell basis has both
messages of dimension at least `d/√2`, footprint at least `d³/2`, and frozen
environments of total Schmidt rank at most `⌈K/d⌉ + d²`. Its reverse
witness therefore has `O(K²)` real coordinates: the coordinate budget
`256 K²` is admissible. The source is `lem:bell-compression` in the revised
robust companion.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

/-- Witness shapes allowed near the Bell basis. -/
def PVMReverseShape.IsNearBell {d K : ℕ} (s : PVMReverseShape d K) : Prop :=
  (d : ℝ) ^ 2 ≤ 2 * (s.1.mA : ℝ) ^ 2 ∧ (d : ℝ) ^ 2 ≤ 2 * (s.1.mB : ℝ) ^ 2 ∧
    s.supportSize ≤ (K + d - 1) / d + d ^ 2

/-- `lem:bell-compression`: near the Bell basis the resource Schmidt rank obeys
`r ≤ 2K/d²`. -/
theorem PVMReverseShape.IsNearBell.resource_le {d K : ℕ} {s : PVMReverseShape d K}
    (hs : s.IsNearBell) : (s.1.r : ℝ) * (d : ℝ) ^ 2 ≤ 2 * K := by
  obtain ⟨hA, hB, -⟩ := hs
  have hmA : (0 : ℝ) ≤ s.1.mA := Nat.cast_nonneg _
  have hmB : (0 : ℝ) ≤ s.1.mB := Nat.cast_nonneg _
  have hprod : ((d : ℝ) ^ 2) ^ 2 ≤ (2 * ((s.1.mA : ℝ) * s.1.mB)) ^ 2 := by
    nlinarith [mul_le_mul hA hB (by positivity) (by positivity)]
  have hd2 : (d : ℝ) ^ 2 ≤ 2 * ((s.1.mA : ℝ) * s.1.mB) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hprod
  have hfoot : (s.1.r : ℝ) * s.1.mA * s.1.mB ≤ K := by exact_mod_cast s.1.footprint
  have hr : (0 : ℝ) ≤ s.1.r := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hd2 hr]

/-- `lem:bell-compression`: when `d³ ≤ 2K`, the total garbage rank is at most `4K/d`. -/
theorem PVMReverseShape.IsNearBell.supportSize_le {d K : ℕ} {s : PVMReverseShape d K}
    (hs : s.IsNearBell) (hd : 2 ≤ d) (hd3 : (d : ℝ) ^ 3 ≤ 2 * K) :
    (s.supportSize : ℝ) * d ≤ 4 * K := by
  obtain ⟨-, -, hsupp⟩ := hs
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdiv : (((K + d - 1) / d : ℕ) : ℝ) * d ≤ K + d := by
    have h := Nat.div_mul_le_self (K + d - 1) d
    have h' : (K + d - 1) / d * d ≤ K + d := by omega
    exact_mod_cast h'
  have hsupp' : (s.supportSize : ℝ) ≤ (((K + d - 1) / d : ℕ) : ℝ) + (d : ℝ) ^ 2 := by
    exact_mod_cast hsupp
  have hd1 : (d : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hsupp' (show (0 : ℝ) ≤ d by linarith)]

theorem slim_coordinate_arith {d K r a b S R2 : ℝ} (hr0 : 0 ≤ r) (hrK : r ≤ K)
    (hR2 : R2 ≤ S ^ 2) (hS2 : S ^ 2 ≤ 25 * K ^ 2) (hdKS : d * K * S ≤ 5 * K ^ 2)
    (hA : d ^ 2 * (r * a) ^ 2 ≤ 2 * K ^ 2) (hB : d ^ 2 * (r * b) ^ 2 ≤ 2 * K ^ 2) :
    2 * r ^ 2 + 2 * R2 + 2 * d ^ 2 * (r * a) ^ 2 + 2 * d ^ 2 * (r * b) ^ 2 +
      4 * (d * K + S) * S ≤ 256 * K ^ 2 := by
  have h1 : r ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hr0 hrK 2
  have h2 : 4 * (d * K + S) * S = 4 * (d * K * S) + 4 * S ^ 2 := by ring
  have h3 : 0 ≤ K ^ 2 := sq_nonneg K
  linarith

/-- The slim budget `256 K²` is admissible for near-Bell shapes once `d³ ≤ 2K`. -/
theorem PVMReverseShape.admissibleBudget_nearBell {d K : ℕ} (s : PVMReverseShape d K)
    (hd : 2 ≤ d) (hs : s.IsNearBell) (hd3 : (d : ℝ) ^ 3 ≤ 2 * K) :
    s.AdmissibleBudget (256 * K ^ 2) := by
  obtain ⟨hA, hB, hS⟩ := hs
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hKR : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hfoot : ((s.1.r * s.1.mA * s.1.mB : ℕ) : ℝ) ≤ K := by exact_mod_cast s.1.footprint
  push_cast at hfoot
  have hr1 : (1 : ℝ) ≤ s.1.r := by exact_mod_cast s.1.resource_pos
  have hmA : (1 : ℝ) ≤ s.1.mA := by exact_mod_cast s.1.messageA_pos
  have hmB : (1 : ℝ) ≤ s.1.mB := by exact_mod_cast s.1.messageB_pos
  set r : ℝ := (s.1.r : ℝ)
  set a : ℝ := (s.1.mA : ℝ)
  set b : ℝ := (s.1.mB : ℝ)
  -- support size in real form: d S ≤ 5 K
  have hSR : (d : ℝ) * s.supportSize ≤ 5 * K := by
    have h1 : ((s.supportSize : ℕ) : ℝ) ≤ (((K + d - 1) / d : ℕ) : ℝ) + (d : ℝ) ^ 2 := by
      exact_mod_cast hS
    have h2 : (d : ℝ) * (((K + d - 1) / d : ℕ) : ℝ) ≤ K + d := by
      have h := Nat.mul_div_le (K + d - 1) d
      have h' : d * ((K + d - 1) / d) ≤ K + d := by omega
      exact_mod_cast h'
    have h3 : (d : ℝ) ≤ 2 * K := by nlinarith
    have h4 : (d : ℝ) ^ 3 ≤ 2 * K := hd3
    nlinarith
  -- message products
  have hab : (r * a * b) ^ 2 ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hfoot 2
  have hrA : (d : ℝ) ^ 2 * (r * a) ^ 2 ≤ 2 * (K : ℝ) ^ 2 := by
    have h1 : (d : ℝ) ^ 2 * (r * a) ^ 2 ≤ 2 * b ^ 2 * (r * a) ^ 2 :=
      mul_le_mul_of_nonneg_right hB (sq_nonneg _)
    have h2 : 2 * b ^ 2 * (r * a) ^ 2 = 2 * (r * a * b) ^ 2 := by ring
    linarith
  have hrB : (d : ℝ) ^ 2 * (r * b) ^ 2 ≤ 2 * (K : ℝ) ^ 2 := by
    have h1 : (d : ℝ) ^ 2 * (r * b) ^ 2 ≤ 2 * a ^ 2 * (r * b) ^ 2 :=
      mul_le_mul_of_nonneg_right hA (sq_nonneg _)
    have h2 : 2 * a ^ 2 * (r * b) ^ 2 = 2 * (r * a * b) ^ 2 := by ring
    linarith
  have hr : r ≤ K := by
    have hra : r ≤ r * a := le_mul_of_one_le_right (by linarith) hmA
    have hrab : r * a ≤ r * a * b := le_mul_of_one_le_right (by positivity) hmB
    linarith
  have hd_le : (d : ℝ) ≤ 2 * K := by
    have : (d : ℝ) ≤ (d : ℝ) ^ 3 := by
      have h1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
      nlinarith
    linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast s.one_le_budget
  constructor
  · -- coordinate count
    have hf := PVMReverseBlocks.finrank_real s
    have hsq : (∑ i, s.2.rank i ^ 2) ≤ s.supportSize ^ 2 := by
      simpa only [PVMReverseShape.supportSize] using
        (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := s.2.rank)
          (fun _ _ => Nat.zero_le _))
    have hsqR : ∑ i, ((s.2.rank i : ℕ) : ℝ) ^ 2 ≤ (s.supportSize : ℝ) ^ 2 := by
      exact_mod_cast hsq
    set S : ℝ := (s.supportSize : ℝ) with hSdef
    have hS0 : 0 ≤ S := Nat.cast_nonneg _
    have hS2 : S ^ 2 ≤ 25 * (K : ℝ) ^ 2 := by
      have h1 : ((d : ℝ) * S) ^ 2 ≤ (5 * K) ^ 2 := pow_le_pow_left₀ (by positivity) hSR 2
      have h2 : S ^ 2 ≤ ((d : ℝ) * S) ^ 2 := by
        rw [mul_pow]
        have : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
        nlinarith [sq_nonneg S]
      linarith
    have hdKS : (d : ℝ) * K * S ≤ 5 * (K : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hSR hKR
      nlinarith
    have hT1 : 2 * r ^ 2 ≤ 2 * (K : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (by linarith) hr 2
      linarith
    rw [← Nat.cast_le (α := ℝ), hf]
    push_cast
    exact slim_coordinate_arith (by positivity) hr hsqR hS2 hdKS hrA hrB
  · -- speed constant
    have h1 : (d : ℝ) * Real.sqrt (10 * d * K) = Real.sqrt (10 * (d : ℝ) ^ 3 * K) := by
      rw [show (10 : ℝ) * (d : ℝ) ^ 3 * K = (d : ℝ) ^ 2 * (10 * d * K) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hdpos.le]
    have h2 : Real.sqrt (10 * (d : ℝ) ^ 3 * K) ≤ 5 * K := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    push_cast
    rw [h1]
    nlinarith

section Protocol

variable {d : ℕ} {ρA ρB κA κB μA μB eA eB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype eA] [Fintype eB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq eA] [DecidableEq eB]

theorem norm_sub_generalizedBell_le_quarter [NeZero d] {M : unitaryGroup (Fin d × Fin d) ℂ}
    (hM : M ∈ bellNeighborhood d) :
    ‖(M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - generalizedBellFinMatrix d‖ ≤ (d : ℝ) / 4 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hs : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1
  refine hM.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **Near-Bell slim witness.** -/
theorem PureProtocol.exists_pvm_reverse_witness_nearBell [NeZero d] (hd2 : 2 ≤ d)
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) eA eB)
    {M : unitaryGroup (Fin d × Fin d) ℂ} (hM : M ∈ bellNeighborhood d)
    {K : ℕ} (hK : NLQCLean.HasFootprint K P.resource μA μB) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 256)
    (hscore : 1 - ε ≤ scorePVM (M : Matrix _ _ ℂ) P.operationalChannel) :
    ∃ s : PVMReverseShape d K, s.IsNearBell ∧ ∃ x : PVMReverseBlocks s,
      PVMReverseBlocks.IsValid x ∧
      ‖PVMReverseBlocks.forward x - PVMReverseBlocks.reverse x * (M : Matrix _ _ ℂ)ᴴ‖ ≤
        (d : ℝ) * Real.sqrt (50 / 9 * ε) := by
  have hd : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hMiso : IsIsometry (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := M.property.1
  obtain ⟨hmA, hmB⟩ := P.sq_le_two_mul_message_sq_of_near_bell hMiso
    (norm_sub_generalizedBell_le_quarter hM) hε0 hε hscore
  obtain ⟨r, kA, kB, hr, hkA, hkB, Q, _, hchan⟩ := P.exists_compressed_pvm_encoders
  let mA := Fintype.card μA
  let mB := Fintype.card μB
  have hrpos : 0 < r := by
    have h := Q.resource_unit.card_pos
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact Nat.pos_of_mul_pos_right h
  have hencA : d * r ≤ kA * mA := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encA_isometry.card_le
  have hencB : d * r ≤ kB * mB := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encB_isometry.card_le
  have hma : 0 < mA := Nat.pos_of_mul_pos_left ((Nat.mul_pos hd hrpos).trans_le hencA)
  have hmb : 0 < mB := Nat.pos_of_mul_pos_left ((Nat.mul_pos hd hrpos).trans_le hencB)
  have hfoot : r * mA * mB ≤ K := by
    have h := (hasFootprint_iff K P.resource).mp hK
    simpa only [← hr] using h
  let s : ReverseShape d K := ⟨r, mA, mB, hrpos, hma, hmb, hfoot⟩
  let R := Q.reindex (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
    (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm (Equiv.refl _) (Equiv.refl _)
  have hRchan : P.operationalChannel = R.operationalChannel :=
    hchan.trans (Q.operationalChannel_reindex (Equiv.refl _) (Equiv.refl _)
      (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm
      (Equiv.refl _) (Equiv.refl _)).symm
  have hRK : NLQCLean.HasFootprint K R.resource (Fin mA) (Fin mB) := by
    refine ⟨r, mA, mB, hfoot, ?_, ?_, ?_⟩
    · simpa only [Fintype.card_fin] using schmidtRank_le_card_left R.resource
    · simp
    · simp
  have hRs : 1 - ε ≤ scorePVM (M : Matrix _ _ ℂ) R.operationalChannel := hRchan ▸ hscore
  -- flat freezing with `m = ⌈K/d⌉` grouped supports
  have hne : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hKm : K ≤ (K + d - 1) / d * Fintype.card (Fin d) := by
    rw [Fintype.card_fin]
    have := Nat.lt_div_mul_add (a := K + d - 1) hd
    generalize (K + d - 1) / d * d = Q at this ⊢
    omega
  have hc : (9 / (16 * (d : ℝ))) * Fintype.card (Fin d) = 9 / 16 := by
    rw [Fintype.card_fin]
    field_simp
  obtain ⟨v, hv, hvrank, hclose⟩ := exists_pvm_frozen_of_choi_rank_flat
    hMiso R.isIsometry_globalIsometry
    (by rw [rank_tensorChoiMatrix]; exact R.rank_normalizedLabChoiMatrix_le_of_hasFootprint hRK)
    hKm (β := 9 / (16 * (d : ℝ))) (by positivity) (by rw [hc]; norm_num)
    (fun i j => (schmidtWeights_mem_of_mem_bellNeighborhood hM i j).1) ⟨hε0, by linarith⟩
    hRs
  have hm_le : (K + d - 1) / d ≤ K := by
    have hK1 : 1 ≤ K := (mul_pos (mul_pos hrpos hma) hmb).trans_le hfoot
    refine Nat.div_le_of_le_mul ?_
    have h1 : K + d ≤ d * K + 1 := by nlinarith
    omega
  obtain ⟨a, harank, x, hx, hcross⟩ := R.exists_pvm_reverse_blocks_of_frozen s hkA hkB v hv
    (hvrank.trans (by omega))
  refine ⟨(s, a), ⟨?_, ?_, ?_⟩, x, hx, ?_⟩
  · exact hmA
  · exact hmB
  · change ∑ i, a.rank i ≤ (K + d - 1) / d + d ^ 2
    rw [Finset.sum_congr rfl fun i _ => harank i]
    simpa [Fintype.card_prod, Fintype.card_fin, sq] using hvrank
  · have hdist := norm_sub_eq_of_crossGram_eq (PVMReverseBlocks.forward x)
      (PVMReverseBlocks.reverse x) R.globalIsometry (flagIsometry v)
      (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ
      hx.isIsometry_forward hx.isIsometry_reverse R.isIsometry_globalIsometry
      (isIsometry_flagIsometry v hv) hcross
    rw [← hdist, hc] at hclose
    have hD : (Fintype.card (Fin d × Fin d) : ℝ) = (d : ℝ) ^ 2 := by simp [pow_two]
    rw [hD, Real.sqrt_sq hdR.le] at hclose
    rw [show 2 * ε * (1 + 9 / 16) / (9 / 16) = 50 / 9 * ε by ring] at hclose
    have h := (div_le_iff₀ hdR).mp hclose
    linarith

end Protocol

end NLQCLean
