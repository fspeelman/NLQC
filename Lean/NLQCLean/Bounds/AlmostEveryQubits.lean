import NLQCLean.Bounds.AlmostEveryPhysical

/-!
# Almost-every fixed-target qubit corollaries

At `d = 2ⁿ`, `n ≥ 1`, `K ≥ 1`, there is one universal
additive constant `b ≥ 0`; the error threshold still depends on the fixed target.
Real base-two logarithms. The single geometric property stays explicit.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory

/-- Qubit rates for all eight reachable sets, with one conull set and threshold. -/
theorem exists_ae_qubit_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (T : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (T ∈ pureReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ mixedReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ purePVMReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ mixedPVMReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) := by
  obtain ⟨c, hc, h⟩ := exists_ae_resource_constant_of_imageVolumeBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} hGeom
  refine ⟨max 0 (-Real.logb 2 c), le_max_left _ _, fun n hn => ?_⟩
  have hd : 2 ≤ 2 ^ n := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  filter_upwards [h (2 ^ n) hd] with T hT
  obtain ⟨e₀, h0, h1, hT⟩ := hT
  refine ⟨e₀, h0, h1, fun K _hK e he he' => ?_⟩
  have hL : 0 < Real.log (1 / e) := Real.log_pos ((one_lt_div₀ he).mpr (by linarith))
  have hq {X : Prop}
      (hX : X → c * ((2 ^ n : ℕ) : ℝ) * Real.sqrt (Real.log (1 / e)) ≤ K) (hu : X) :
      (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - max 0 (-Real.logb 2 c) ≤
        Real.logb 2 (K : ℝ) := by
    have h := hX hu
    push_cast at h
    exact qubit_lower_of_resource hc hL n h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hT K e he he'
  exact ⟨hq h₁, hq h₂, hq h₃, hq h₄, hq h₅, hq h₆, hq h₇, hq h₈⟩

/-- Unitary score qubit rate: pure and finite mixed unitary score reachability at `d = 2ⁿ`. -/
theorem exists_ae_unitary_qubit_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (T : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (T ∈ pureReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ mixedReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) := by
  obtain ⟨b, hb, h⟩ := exists_ae_qubit_constant.{0, 0, 0, 0, 0, 0, 0, 0} hGeom
  refine ⟨b, hb, fun n hn => (h n hn).mono fun T hT => ?_⟩
  obtain ⟨e₀, h0, h1, hT⟩ := hT
  exact ⟨e₀, h0, h1, fun K hK e he he' => ⟨(hT K hK e he he').1, (hT K hK e he he').2.1⟩⟩

/-- Unitary diamond qubit rate: pure and finite mixed normalized diamond reachability at `d = 2ⁿ`. -/
theorem exists_ae_diamond_qubit_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (T : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) := by
  obtain ⟨b, hb, h⟩ := exists_ae_qubit_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} hGeom
  refine ⟨b, hb, fun n hn => (h n hn).mono fun T hT => ?_⟩
  obtain ⟨e₀, h0, h1, hT⟩ := hT
  exact ⟨e₀, h0, h1, fun K hK e he he' =>
    ⟨(hT K hK e he he').2.2.2.2.1, (hT K hK e he he').2.2.2.2.2.1⟩⟩

/-- PVM score qubit rate: pure and finite mixed PVM score reachability at `d = 2ⁿ`. -/
theorem exists_ae_pvm_qubit_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (M : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (M ∈ purePVMReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (M ∈ mixedPVMReachable (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) := by
  obtain ⟨b, hb, h⟩ := exists_ae_qubit_constant.{0, 0, 0, 0, 0, 0, 0, 0} hGeom
  refine ⟨b, hb, fun n hn => (h n hn).mono fun T hT => ?_⟩
  obtain ⟨e₀, h0, h1, hT⟩ := hT
  exact ⟨e₀, h0, h1, fun K hK e he he' => ⟨(hT K hK e he he').2.2.1, (hT K hK e he he').2.2.2.1⟩⟩

/-- PVM joint-TV qubit rate: pure and finite mixed worst-case joint-TV reachability at `d = 2ⁿ`. -/
theorem exists_ae_pvm_tv_qubit_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → ∀ᵐ (M : unitaryGroup (Fin (2 ^ n) × Fin (2 ^ n)) ℂ)
      ∂unitaryHaar (Fin (2 ^ n) × Fin (2 ^ n)),
      ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ K : ℕ, 1 ≤ K → ∀ e : ℝ, 0 < e → e ≤ e₀ →
        (M ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) ∧
        (M ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} (2 ^ n) K e →
          (n : ℝ) + (1 / 2 : ℝ) * Real.logb 2 (Real.log (1 / e)) - b ≤ Real.logb 2 (K : ℝ)) := by
  obtain ⟨b, hb, h⟩ := exists_ae_qubit_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} hGeom
  refine ⟨b, hb, fun n hn => (h n hn).mono fun T hT => ?_⟩
  obtain ⟨e₀, h0, h1, hT⟩ := hT
  exact ⟨e₀, h0, h1, fun K hK e he he' =>
    ⟨(hT K hK e he he').2.2.2.2.2.2.1, (hT K hK e he he').2.2.2.2.2.2.2⟩⟩

end NLQCLean
