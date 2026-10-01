import NLQCLean.Approx.PolynomialWitnessFamily

/-!
# Finite family count and physical coverage by polynomial witnesses

At most K³ charged shapes occur, bounded by exp(3P). Every
accurate arbitrary-finite-register pure protocol is within d sqrt(2 epsilon)
of one of the polynomial images of the compact witness sources.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

namespace ReverseShape

theorem dimensions_le_budget {d K : ℕ} (s : ReverseShape d K) :
    s.r ≤ K ∧ s.mA ≤ K ∧ s.mB ≤ K := by
  have ha : s.r * s.mA ≤ K := (Nat.le_mul_of_pos_right _ s.messageB_pos).trans s.footprint
  exact ⟨(Nat.le_mul_of_pos_right _ s.messageA_pos).trans ha,
    (Nat.le_mul_of_pos_left _ s.resource_pos).trans ha,
    (Nat.le_mul_of_pos_left _ (mul_pos s.resource_pos s.messageA_pos)).trans s.footprint⟩

/-- Enumerate the three positive dimensions by zero-based indices below K. -/
def toFiniteTriple (d K : ℕ) : ReverseShape d K ↪ (Fin K × Fin K × Fin K) where
  toFun s := (⟨s.r - 1, by have h := s.dimensions_le_budget.1; have hK := s.one_le_budget; omega⟩,
    ⟨s.mA - 1, by have h := s.dimensions_le_budget.2.1; have hK := s.one_le_budget; omega⟩,
    ⟨s.mB - 1, by have h := s.dimensions_le_budget.2.2; have hK := s.one_le_budget; omega⟩)
  inj' s t h := by
    have hr := congrArg (fun p : Fin K × Fin K × Fin K => p.1.val) h
    have ha := congrArg (fun p : Fin K × Fin K × Fin K => p.2.1.val) h
    have hb := congrArg (fun p : Fin K × Fin K × Fin K => p.2.2.val) h
    change s.r - 1 = t.r - 1 at hr
    change s.mA - 1 = t.mA - 1 at ha
    change s.mB - 1 = t.mB - 1 at hb
    have hre : s.r = t.r := by have h1 := s.resource_pos; have h2 := t.resource_pos; omega
    have hae : s.mA = t.mA := by have h1 := s.messageA_pos; have h2 := t.messageA_pos; omega
    have hbe : s.mB = t.mB := by have h1 := s.messageB_pos; have h2 := t.messageB_pos; omega
    cases s
    cases t
    cases hre
    cases hae
    cases hbe
    rfl

noncomputable instance (d K : ℕ) : Fintype (ReverseShape d K) :=
  Fintype.ofInjective (toFiniteTriple d K) (toFiniteTriple d K).injective

theorem card_le_cube (d K : ℕ) : Fintype.card (ReverseShape d K) ≤ K ^ 3 := by
  have h := Fintype.card_le_of_embedding (toFiniteTriple d K)
  simpa [pow_succ, mul_assoc] using h

end ReverseShape

theorem cube_budget_le_exp_coordinateBudget {d K : ℕ} (hd : 0 < d) :
    (K : ℝ) ^ 3 ≤ Real.exp (3 * (witnessCoordinateBudget d K : ℝ)) := by
  have hk : K ≤ witnessCoordinateBudget d K := by
    have hs : K ≤ K ^ 2 := by
      by_cases hK : K = 0
      · simp [hK]
      · have hK1 : 1 ≤ K := by omega
        nlinarith
    exact hs.trans (Nat.le_mul_of_pos_left _ (by positivity : 0 < 32 * d ^ 2))
  have hr : (K : ℝ) ≤ (witnessCoordinateBudget d K : ℝ) := by exact_mod_cast hk
  have he : (K : ℝ) ≤ Real.exp (witnessCoordinateBudget d K : ℝ) := by
    have h := Real.add_one_le_exp (witnessCoordinateBudget d K : ℝ)
    linarith
  have h := pow_le_pow_left₀ (Nat.cast_nonneg K) he 3
  simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using h

theorem ReverseShape.card_le_exp_coordinateBudget {d K : ℕ} (hd : 0 < d) :
    (Fintype.card (ReverseShape d K) : ℝ) ≤ Real.exp (3 * (witnessCoordinateBudget d K : ℝ)) := by
  have h : (Fintype.card (ReverseShape d K) : ℝ) ≤ (K : ℝ) ^ 3 := by
    exact_mod_cast ReverseShape.card_le_cube d K
  exact h.trans (cube_budget_le_exp_coordinateBudget hd)

section PhysicalCoverage

variable {d : ℕ} {ρA ρB κA κB μA μB eA eB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype eA] [Fintype eB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq eA] [DecidableEq eB]

/-- Polynomial-family coverage, directly from normalized Choi score
and the original rank-based footprint, with every original finite register arbitrary. -/
theorem PureProtocol.exists_polynomial_witness_approximation
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) eA eB)
    (hd : 0 < d) {K : ℕ} {ε : ℝ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : IsIsometry U) (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hscore : 1 - ε ≤ scoreU U P.operationalChannel) :
    ∃ s : ReverseShape d K, ∃ x ∈ (ReverseBlocks.witnessFormat s hd (Real.sqrt (2 * ε))).source,
      ‖(ReverseBlocks.coordinateOverlapPolynomial s hd).eval x - overlapOutputCoordinates d U‖ ≤
        (d : ℝ) * Real.sqrt (2 * ε) := by
  obtain ⟨s, x, hx, _, hclose, _, _, hdef⟩ :=
    P.exists_reverse_witness_approximation hd U hU hK hε0 hε hscore
  have hs : (d : ℝ) ^ 2 - ‖ReverseBlocks.overlap x‖ ^ 2 ≤
      (d : ℝ) ^ 2 * (Real.sqrt (2 * ε)) ^ 2 := by
    rw [Real.sq_sqrt (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hε0)]
    exact hdef
  obtain ⟨y, hy, he⟩ := ReverseBlocks.exists_mem_witnessFormat_source s hd (Real.sqrt (2 * ε)) hx hs
  refine ⟨s, y, hy, ?_⟩
  rw [he, ← map_sub, norm_overlapOutputCoordinates]
  exact hclose

end PhysicalCoverage
end NLQCLean
