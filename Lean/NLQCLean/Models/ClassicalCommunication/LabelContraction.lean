import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Contraction of copied finite classical labels

The label deltas select actual sectors before any quantum amplitude is
expanded. The decoder and remaining amplitude are arbitrary functions, so
the proofs do not unfold the larger protocol telescope.
-/

namespace NLQCLean.ClassicalCommunication

private theorem sum_ite_irrel {α V : Type*} [Fintype α] [AddCommMonoid V]
    (p : Prop) [Decidable p] (f : α → V) :
    (∑ a, if p then f a else 0) = if p then ∑ a, f a else 0 := by
  by_cases h : p <;> simp [h]

variable {K M S T E : Type*}
variable [Fintype K] [Fintype M] [Fintype S] [Fintype T] [Fintype E]
variable [DecidableEq S] [DecidableEq T] [DecidableEq E]

/-- Contract a kept outcome/Kraus label and an incoming outcome label,
without expanding the remaining quantum amplitude. -/
theorem sum_label_sector_left
    (D : S → T → K → M → ℂ)
    (F : (K × (S × E)) → (M × T) → ℂ) (x : S) (y : T) (e : E) :
    (∑ k : K × (S × E), ∑ q : M × T,
      (if (x, (y, e)) = (k.2.1, (q.2, k.2.2)) then
        D k.2.1 q.2 k.1 q.1 else 0) * F k q) =
      ∑ k : K, ∑ q : M, D x y k q * F (k, (x, e)) (q, y) := by
  simp [Fintype.sum_prod_type, Prod.mk.injEq, ite_and, ite_mul]

/-- The opposite party's swapped label order contracts to the same pair of
actual outcomes and its own private Kraus label. -/
theorem sum_label_sector_right
    (D : S → T → K → M → ℂ)
    (F : (K × (T × E)) → (M × S) → ℂ) (x : S) (y : T) (e : E) :
    (∑ k : K × (T × E), ∑ q : M × S,
      (if (x, (y, e)) = (q.2, (k.2.1, k.2.2)) then
        D q.2 k.2.1 k.1 q.1 else 0) * F k q) =
      ∑ k : K, ∑ q : M, D x y k q * F (k, (y, e)) (q, x) := by
  simpa only [Prod.mk.injEq, and_left_comm] using
    (sum_label_sector_left (fun y x => D x y) F y x e)

end NLQCLean.ClassicalCommunication
