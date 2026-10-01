import NLQCLean.Models.SwapTarget

/-!
# A normalized Frobenius neighborhood of SWAP

The near-SWAP target patch used by freezing and the restricted Haar bounds.
It is closed, hence Borel, and contains SWAP.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

/-- SWAP as an element of the unitary group on `Fin d × Fin d`. -/
noncomputable def swapElement (d : ℕ) : unitaryGroup (Fin d × Fin d) ℂ :=
  ⟨swapUnitary (Fin d), Matrix.mem_unitaryGroup_iff'.mpr (isIsometry_swapUnitary (Fin d))⟩

/-- The normalized Frobenius neighbourhood `S_d` of SWAP. -/
def swapNeighborhood (d : ℕ) : Set (unitaryGroup (Fin d × Fin d) ℂ) :=
  {U | ‖(U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - swapUnitary (Fin d)‖ / d ≤ 1 / 4}

theorem mem_swapNeighborhood_iff {d : ℕ} (hd : 0 < d) (U : unitaryGroup (Fin d × Fin d) ℂ) :
    U ∈ swapNeighborhood d ↔
      ‖(U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - swapUnitary (Fin d)‖ ≤ (d : ℝ) / 4 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [swapNeighborhood, Set.mem_ofPred_eq]
  rw [div_le_iff₀ hd']
  constructor <;> intro h <;> linarith

theorem isClosed_swapNeighborhood (d : ℕ) : IsClosed (swapNeighborhood d) :=
  isClosed_le (((continuous_subtype_val.sub continuous_const).norm).div_const _) continuous_const

theorem swapElement_mem_swapNeighborhood (d : ℕ) : swapElement d ∈ swapNeighborhood d := by
  change ‖swapUnitary (Fin d) - swapUnitary (Fin d)‖ / (d : ℝ) ≤ 1 / 4
  simp only [sub_self, norm_zero, zero_div]
  norm_num

end NLQCLean
