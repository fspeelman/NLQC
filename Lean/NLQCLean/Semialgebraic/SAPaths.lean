import NLQCLean.Semialgebraic.Definable
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Interval.Set.Basic

/-!
# Semialgebraic paths

`IsSAPath c` says that `c : ℝ → ℝ^m` is continuous on `[0,1]` and its graph over
`[0,1]` is semialgebraic (time is the extra coordinate `none`). A set is
*semialgebraically path connected* when any two of its points are joined by a
semialgebraic path inside it.
-/

noncomputable section

namespace NLQCLean

open Set

variable {m n : ℕ}

/-- The graph over `[0,1]` of a path, with time as coordinate `none`. -/
def pathGraph (c : ℝ → Fin m → ℝ) : Set (Option (Fin m) → ℝ) :=
  {h | h none ∈ Icc (0 : ℝ) 1 ∧ ∀ i, h (some i) = c (h none) i}

/-- A continuous semialgebraic path on `[0,1]`. -/
structure IsSAPath (c : ℝ → Fin m → ℝ) : Prop where
  continuousOn : ContinuousOn c (Icc 0 1)
  graph : SAOn (pathGraph c)

/-- Any two points are joined by a semialgebraic path inside the set. -/
def SAPathConnected (S : Set (Fin m → ℝ)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃ c : ℝ → Fin m → ℝ, IsSAPath c ∧ c 0 = x ∧ c 1 = y ∧ MapsTo c (Icc 0 1) S

theorem saOn_unitInterval_time {ι : Type*} (τ : ι) :
    SAOn {h : ι → ℝ | h τ ∈ Icc (0 : ℝ) 1} :=
  ((SAOn.le 0 (MvPolynomial.X τ)).inter (SAOn.le (MvPolynomial.X τ) 1)).congr fun h => by
    simp [Set.mem_Icc]

theorem IsSAPath.const (x : Fin m → ℝ) : IsSAPath fun _ : ℝ => x := by
  refine ⟨continuousOn_const, ?_⟩
  refine ((saOn_unitInterval_time none).inter
    (SAOn.fintype_iInter fun i => SAOn.eq (MvPolynomial.X (some i)) (MvPolynomial.C (x i)))).congr
    fun h => ?_
  simp [pathGraph]

/-- Lifting a base path by a last coordinate. -/
theorem IsSAPath.snoc {γ : ℝ → Fin n → ℝ} {Y : ℝ → ℝ} (hγ : ContinuousOn γ (Icc 0 1))
    (hY : ContinuousOn Y (Icc 0 1))
    (hgraph : SAOn {h : Option (Fin (n + 1)) → ℝ | h none ∈ Icc (0 : ℝ) 1 ∧
      (∀ i : Fin n, h (some i.castSucc) = γ (h none) i) ∧ h (some (Fin.last n)) = Y (h none)}) :
    IsSAPath fun t => (Fin.snoc (γ t) (Y t) : Fin (n + 1) → ℝ) := by
  refine ⟨?_, hgraph.congr fun h => ?_⟩
  · refine continuousOn_pi.mpr fun i => ?_
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hY
    · simpa using (continuousOn_pi.mp hγ) i
  · simp only [Set.mem_ofPred_eq, pathGraph]
    constructor
    · rintro ⟨ht, hb, hl⟩
      refine ⟨ht, fun i => ?_⟩
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hl
      · simpa using hb i
    · rintro ⟨ht, h'⟩
      refine ⟨ht, fun i => ?_, ?_⟩
      · simpa using h' i.castSucc
      · simpa using h' (Fin.last n)

/-- The graph of a base path, pulled back to the lifted coordinates. -/
theorem saOn_basePathGraph {γ : ℝ → Fin n → ℝ} (hγ : IsSAPath γ) :
    SAOn {h : Option (Fin (n + 1)) → ℝ | h none ∈ Icc (0 : ℝ) 1 ∧
      ∀ i : Fin n, h (some i.castSucc) = γ (h none) i} :=
  (hγ.graph.comap (Option.map Fin.castSucc)).congr fun h => by
    simp [pathGraph, Function.comp_def]

theorem SAPathConnected.isPreconnected {S : Set (Fin m → ℝ)} (hS : SAPathConnected S) :
    IsPreconnected S := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  obtain ⟨c, hc, hc0, hc1, hmaps⟩ := hS x hx y hy
  refine ⟨c '' Icc 0 1, hmaps.image_subset, ⟨0, ⟨le_refl 0, zero_le_one⟩, hc0⟩,
    ⟨1, ⟨zero_le_one, le_refl 1⟩, hc1⟩, ?_⟩
  exact isPreconnected_Icc.image c hc.continuousOn

theorem SAPathConnected.of_subsingleton {S : Set (Fin m → ℝ)} (hS : S.Subsingleton) :
    SAPathConnected S := by
  intro x hx y hy
  obtain rfl := hS hx hy
  exact ⟨fun _ => x, IsSAPath.const x, rfl, rfl, fun _ _ => hx⟩

end NLQCLean
