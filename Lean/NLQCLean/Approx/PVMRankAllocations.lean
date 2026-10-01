import Mathlib.Combinatorics.Enumerative.Composition
import NLQCLean.Approx.PolynomialWitnessCoverage

/-!
# Finite positive rank allocations for PVM reverse witnesses

The finite witness family uses one positive Schmidt-support rank for every PVM label, with total
rank at most the charged budget plus the number of labels.  Adding a final
positive slack block embeds these allocations into ordinary compositions,
giving an exponential family count even at zero budget or with no labels.
-/

namespace NLQCLean

open scoped BigOperators

/-- A positive support rank for every label, with the total rank bound. -/
structure PositiveRankAllocation (δ : Type*) [Fintype δ] (K : ℕ) where
  rank : δ → ℕ
  rank_pos : ∀ i, 0 < rank i
  sum_le : ∑ i, rank i ≤ K + Fintype.card δ

namespace PositiveRankAllocation

variable {δ : Type*} [Fintype δ] {K : ℕ}

/-- Encode an allocation as its positive rank blocks followed by one positive
slack block.  Its total is exactly `K + card δ + 1`. -/
noncomputable def toComposition (s : PositiveRankAllocation δ K) :
    Composition (K + Fintype.card δ + 1) where
  blocks :=
    List.ofFn (fun i : Fin (Fintype.card δ) ↦
      s.rank ((Fintype.equivFin δ).symm i)) ++
      [K + Fintype.card δ + 1 - ∑ i, s.rank i]
  blocks_pos := by
    classical
    intro n hn
    simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at hn
    rcases hn with ⟨i, rfl⟩ | rfl
    · exact s.rank_pos _
    · have hsum := s.sum_le
      omega
  blocks_sum := by
    classical
    simp only [List.sum_append, List.sum_ofFn, List.sum_singleton]
    rw [(Fintype.equivFin δ).symm.sum_comp]
    have hsum := s.sum_le
    omega

theorem toComposition_injective :
    Function.Injective
      (toComposition : PositiveRankAllocation δ K →
        Composition (K + Fintype.card δ + 1)) := by
  classical
  intro s t h
  have hblocks := congrArg Composition.blocks h
  have hprefix := congrArg (List.take (Fintype.card δ)) hblocks
  simp only [toComposition, List.length_ofFn, List.take_append_of_le_length,
    le_refl, List.take_of_length_le] at hprefix
  have hrankFin :
      (fun i : Fin (Fintype.card δ) ↦ s.rank ((Fintype.equivFin δ).symm i)) =
        fun i : Fin (Fintype.card δ) ↦ t.rank ((Fintype.equivFin δ).symm i) :=
    List.ofFn_injective hprefix
  have hrank : s.rank = t.rank := by
    funext i
    simpa using congrFun hrankFin (Fintype.equivFin δ i)
  cases s
  cases t
  cases hrank
  rfl

noncomputable def toCompositionEmbedding :
    PositiveRankAllocation δ K ↪ Composition (K + Fintype.card δ + 1) :=
  ⟨toComposition, toComposition_injective⟩

noncomputable instance : Fintype (PositiveRankAllocation δ K) :=
  Fintype.ofInjective toComposition toComposition_injective

/-- An exponential count for positive rank allocations. -/
theorem card_le_two_pow :
    Fintype.card (PositiveRankAllocation δ K) ≤
      2 ^ (K + Fintype.card δ) := by
  have h := Fintype.card_le_of_embedding
    (toCompositionEmbedding :
      PositiveRankAllocation δ K ↪ Composition (K + Fintype.card δ + 1))
  rw [composition_card] at h
  simpa using h

end PositiveRankAllocation

/-- The discrete family index: a charged architecture triple and one
positive support-rank allocation for the `d²` ordered PVM labels. -/
abbrev PVMReverseShape (d K : ℕ) :=
  ReverseShape d K × PositiveRankAllocation (Fin d × Fin d) K

namespace PVMReverseShape

/-- Charged triples cost at most `K³`, while the support allocations cost at
most `2^(K+d²)`. -/
theorem card_le (d K : ℕ) :
    Fintype.card (PVMReverseShape d K) ≤ K ^ 3 * 2 ^ (K + d ^ 2) := by
  rw [Fintype.card_prod]
  calc
    Fintype.card (ReverseShape d K) *
          Fintype.card (PositiveRankAllocation (Fin d × Fin d) K) ≤
        K ^ 3 * 2 ^ (K + Fintype.card (Fin d × Fin d)) :=
      Nat.mul_le_mul (ReverseShape.card_le_cube d K)
        PositiveRankAllocation.card_le_two_pow
    _ = K ^ 3 * 2 ^ (K + d ^ 2) := by simp [pow_two]

end PVMReverseShape

end NLQCLean
