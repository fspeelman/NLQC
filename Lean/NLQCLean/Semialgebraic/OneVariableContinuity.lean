import NLQCLean.Semialgebraic.DefinableChoice
import NLQCLean.Semialgebraic.Components
import NLQCLean.Semialgebraic.PiecewiseC1

/-!
# Continuity of one-variable semialgebraic functions near `0⁺`

A function `f` whose graph over `(0, ∞)` is semialgebraic is continuous on some
interval `(0, ε)`. Its value at `r` is a root of a derivative-closed family
(a band would contain other points of the graph), and the semialgebraic sets
of `r` with a given root count and a given root index have finite frontier,
so one of them contains a right neighbourhood of `0`, on which the root
function is continuous.
-/

noncomputable section

namespace NLQCLean

open Set Filter Topology Sundog.TarskiQE

theorem subset_or_subset_of_frontier {S U : Set ℝ} (hU : IsPreconnected U)
    (hdisj : ∀ x ∈ U, x ∉ frontier S) : U ⊆ S ∨ U ⊆ Sᶜ := by
  have hcover : U ⊆ interior S ∪ interior Sᶜ := by
    intro x hx
    have h := hdisj x hx
    rw [frontier, Set.mem_sdiff, not_and_or, not_not] at h
    rcases h with h | h
    · right
      rw [interior_compl]
      exact h
    · left
      exact h
  rcases hU.subset_or_subset isOpen_interior isOpen_interior
    (disjoint_compl_right.mono interior_subset interior_subset) hcover with h | h
  · exact Or.inl (h.trans interior_subset)
  · exact Or.inr (h.trans interior_subset)

/-- A set of reals with finite frontier contains or avoids a right
neighbourhood of each point. -/
theorem eventually_right_of_finite_frontier {S : Set ℝ} (hS : (frontier S).Finite) (x₀ : ℝ) :
    (∀ᶠ x in 𝓝[>] x₀, x ∈ S) ∨ (∀ᶠ x in 𝓝[>] x₀, x ∉ S) := by
  have hc : IsClosed (frontier S \ {x₀}) := (hS.sdiff).isClosed
  have hn : (frontier S \ {x₀})ᶜ ∈ 𝓝 x₀ := hc.isOpen_compl.mem_nhds (by simp)
  have h : ∀ᶠ x in 𝓝[>] x₀, x ∉ frontier S := by
    filter_upwards [nhdsWithin_le_nhds hn, self_mem_nhdsWithin] with x hx hgt hxf
    exact hx ⟨hxf, ne_of_gt hgt⟩
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  rcases subset_or_subset_of_frontier isPreconnected_Ioo (fun x hx => hsub hx) with h1 | h1
  · exact Or.inl (mem_of_superset (Ioo_mem_nhdsGT hu) h1)
  · exact Or.inr (mem_of_superset (Ioo_mem_nhdsGT hu) h1)

theorem finite_frontier_of_saOn {S : Set ℝ} (hS : SAOn {g : Fin 1 → ℝ | g 0 ∈ S}) :
    (frontier S).Finite :=
  finite_frontier_of_semialgebraic_line ((semialgebraic_iff_saOn _).mpr hS)

variable {n : ℕ}

/-- A height off the roots shares its slot with another height. -/
theorem exists_ne_slotIndex_eq {F : List (ParamPoly n)} {g : Fin n → ℝ} {y : ℝ}
    (hy : y ∉ rootSet F g) : ∃ y' ≠ y, slotIndex F g y' = slotIndex F g y := by
  classical
  have hT := rootSet_finite F g
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hT.isClosed.isOpen_compl y hy
  refine ⟨y + δ / 2, by linarith, ?_⟩
  have hnot : ∀ z ∈ Icc y (y + δ / 2), z ∉ rootSet F g := by
    intro z hz
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  have hcount : countBelow (rootSet F g) (y + δ / 2) = countBelow (rootSet F g) y := by
    unfold countBelow
    congr 1
    ext z
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hz, hzy⟩
      refine ⟨hz, ?_⟩
      by_contra hle
      exact hnot z ⟨not_lt.mp hle, hzy.le⟩ hz
    · rintro ⟨hz, hzy⟩
      exact ⟨hz, by linarith⟩
  unfold slotIndex
  rw [hcount, ite_eq_right (hnot _ ⟨by linarith, le_refl _⟩), ite_eq_right hy]

/-- **One-variable continuity.** -/
theorem exists_continuousOn_Ioo_of_saOn_graph {f : ℝ → ℝ}
    (hf : SAOn {h : Fin 2 → ℝ | 0 < h 0 ∧ h 1 = f (h 0)}) :
    ∃ ε > 0, ContinuousOn f (Ioo 0 ε) := by
  classical
  obtain ⟨F, hF, hslot⟩ := exists_adapted_family hf
  let G : Set (Fin 2 → ℝ) := {h | 0 < h 0 ∧ h 1 = f (h 0)}
  let c : ℝ → Fin 1 → ℝ := fun r _ => r
  have hsnoc : ∀ r y, (Fin.snoc (c r) y : Fin 2 → ℝ) ∈ G ↔ 0 < r ∧ y = f r := by
    intro r y
    simp [G, c, Fin.snoc]
  -- the value is a root
  have hroot : ∀ r, 0 < r → f r ∈ rootSet F (c r) := by
    intro r hr
    by_contra hnot
    obtain ⟨y', hne, hy'⟩ := exists_ne_slotIndex_eq hnot
    have := (hslot (c r) y' (f r) hy').mpr ((hsnoc r (f r)).mpr ⟨hr, rfl⟩)
    exact hne ((hsnoc r y').mp this).2
  let N := ∑ P ∈ F.toFinset, P.natDegree
  let P : ℕ → ℕ → Set ℝ := fun k i =>
    {r | 0 < r ∧ (rootSet F (c r)).ncard = k ∧ countBelow (rootSet F (c r)) (f r) = i}
  have hPsa : ∀ k i, SAOn {g : Fin 1 → ℝ | g 0 ∈ P k i} := by
    intro k i
    have hA : SAOn {h : Fin 2 → ℝ | h ∈ G ∧ h ∈ slotSet F (2 * i + 1)} := hf.inter (saOn_slotSet F _)
    refine (((SAOn.pos (MvPolynomial.X 0)).inter (saOn_ncard_rootSet_eq F k)).inter
      (SAOn.exists_snoc hA)).congr fun g => ?_
    obtain ⟨r, rfl⟩ : ∃ r, g = c r := ⟨g 0, funext fun j => by rw [Subsingleton.elim j 0]⟩
    have hc0 : c r 0 = r := rfl
    simp only [mem_inter_iff, mem_ofPred_eq, MvPolynomial.eval_X, P, hc0]
    simp only [slotSet, mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last, hsnoc]
    constructor
    · rintro ⟨⟨hr, hk⟩, y, ⟨-, rfl⟩, hy⟩
      refine ⟨hr, hk, ?_⟩
      rw [slotIndex_eq_iff] at hy
      omega
    · rintro ⟨hr, hk, hi⟩
      refine ⟨⟨hr, hk⟩, f r, ⟨hr, rfl⟩, ?_⟩
      rw [slotIndex_eq_iff]
      exact ⟨by omega, iff_of_true (hroot _ hr) (by omega)⟩
  -- one pair holds on a right neighbourhood of `0`
  have hcover : ∀ r, 0 < r → ∃ k ∈ Finset.range (N + 1), ∃ i ∈ Finset.range (N + 1), r ∈ P k i := by
    intro r hr
    have hk := ncard_rootSet_le F (c r)
    have hi := countBelow_le_ncard (rootSet_finite F (c r)) (f r)
    exact ⟨_, Finset.mem_range.mpr (by omega), _, Finset.mem_range.mpr (by omega), hr, rfl, rfl⟩
  have hex : ∃ k i, ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ P k i := by
    by_contra hall
    push Not at hall
    have hout : ∀ k i, ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∉ P k i := fun k i =>
      (eventually_right_of_finite_frontier (finite_frontier_of_saOn (hPsa k i)) 0).resolve_left
        (Filter.not_eventually.mpr (hall k i))
    have hall' : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧
        ∀ k ∈ Finset.range (N + 1), ∀ i ∈ Finset.range (N + 1), r ∉ P k i :=
      eventually_mem_nhdsWithin |>.and ((Finset.eventually_all _).mpr fun k _ =>
        (Finset.eventually_all _).mpr fun i _ => hout k i)
    obtain ⟨r, hr, hnot⟩ := hall'.exists
    obtain ⟨k, hk, i, hi, hP⟩ := hcover r hr
    exact hnot k hk i hi hP
  obtain ⟨k, i, hev⟩ := hex
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨ε, hε, ?_⟩
  let D : Set (Fin 1 → ℝ) := c '' Ioo 0 ε
  have hD : ∀ g ∈ D, (rootSet F g).ncard = k := by
    rintro _ ⟨r, hr, rfl⟩
    exact (hsub hr).2.1
  have hcont : ContinuousOn (fun r => rootFn F (c r) i) (Ioo 0 ε) := by
    have hi : i < k := by
      obtain ⟨r, hr⟩ : (Ioo (0 : ℝ) ε).Nonempty := nonempty_Ioo.mpr hε
      have h := hsub hr
      rw [← h.2.1, ← h.2.2]
      exact countBelow_lt_ncard (rootSet_finite F _) (hroot r h.1)
    exact (continuousOn_rootFn hF hD hi).comp (continuous_pi fun _ => continuous_id).continuousOn
      (mapsTo_image c _)
  refine hcont.congr fun r hr => ?_
  have h := hsub hr
  have hfin := rootSet_finite F (c r)
  have hlt : i < (rootSet F (c r)).ncard := by
    rw [← h.2.2]
    exact countBelow_lt_ncard hfin (hroot r h.1)
  exact (eq_nthElem_iff hfin hlt).mpr ⟨hroot r h.1, h.2.2⟩

end NLQCLean
