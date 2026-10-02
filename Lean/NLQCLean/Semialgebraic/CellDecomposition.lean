import NLQCLean.Semialgebraic.Cells

/-!
# Decomposition into semialgebraically path-connected pieces

Every semialgebraic subset of `ℝⁿ` is a finite union of semialgebraic sets,
each semialgebraically path connected. The proof is a cylindrical induction on
`n`: the defining polynomials, closed under the derivative in the last
variable, have finitely many roots over each parameter; the parameter space is
cut by the number of roots and by which slots meet the set, each piece is
decomposed by induction, and the slots over each resulting piece are path
connected (`SAPathConnected.cell`) and lie inside or outside the set.
-/

noncomputable section

namespace NLQCLean

open Set Polynomial Sundog.TarskiQE

variable {n : ℕ}

/-- The polynomial in the last variable with the same values. -/
def toParam (q : MvPolynomial (Fin (n + 1)) ℝ) : ParamPoly n :=
  MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.rename (Fin.snoc Fin.succ 0) q)

theorem eval_toParam (q : MvPolynomial (Fin (n + 1)) ℝ) (g : Fin n → ℝ) (y : ℝ) :
    (spec g (toParam q)).eval y = MvPolynomial.eval (Fin.snoc g y) q := by
  have hcomp : (Fin.cons y g : Fin (n + 1) → ℝ) ∘ (Fin.snoc Fin.succ 0) = Fin.snoc g y := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j
      simp
  rw [toParam, ← spec_eval_cons, MvPolynomial.eval_rename, hcomp]

/-- All iterated `y`-derivatives of a family. -/
def derivClosure (F : List (ParamPoly n)) : List (ParamPoly n) :=
  F.flatMap fun P => (List.range (P.natDegree + 1)).map fun l => derivative^[l] P

theorem mem_derivClosure_self {F : List (ParamPoly n)} {P : ParamPoly n} (hP : P ∈ F) :
    P ∈ derivClosure F :=
  List.mem_flatMap.mpr ⟨P, hP, List.mem_map.mpr ⟨0, List.mem_range.mpr (Nat.succ_pos _), rfl⟩⟩

theorem derivClosed_derivClosure (F : List (ParamPoly n)) : DerivClosed (derivClosure F) := by
  intro P hP hne
  obtain ⟨P₀, hP₀, hmem⟩ := List.mem_flatMap.mp hP
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hmem
  refine List.mem_flatMap.mpr ⟨P₀, hP₀, List.mem_map.mpr ⟨l + 1, List.mem_range.mpr ?_, ?_⟩⟩
  · by_contra hge
    apply hne
    rw [← Function.iterate_succ_apply' derivative]
    exact iterate_derivative_eq_zero (by omega)
  · rw [Function.iterate_succ_apply']

theorem ncard_rootSet_le (F : List (ParamPoly n)) (g : Fin n → ℝ) :
    (rootSet F g).ncard ≤ ∑ P ∈ F.toFinset, P.natDegree := by
  classical
  have hsub : rootSet F g ⊆ ↑(F.toFinset.biUnion fun P => (spec g P).roots.toFinset) := by
    rintro y ⟨P, hP, h0, hy⟩
    simp only [Finset.coe_biUnion, mem_iUnion, List.mem_toFinset, Finset.mem_coe,
      Multiset.mem_toFinset, exists_prop]
    exact ⟨P, hP, (mem_roots h0).mpr hy⟩
  calc (rootSet F g).ncard ≤ (F.toFinset.biUnion fun P => (spec g P).roots.toFinset).card := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ ∑ P ∈ F.toFinset, ((spec g P).roots.toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ P ∈ F.toFinset, P.natDegree := by
        refine Finset.sum_le_sum fun P _ => ?_
        calc ((spec g P).roots.toFinset).card ≤ (spec g P).roots.card :=
              Multiset.toFinset_card_le _
          _ ≤ (spec g P).natDegree := card_roots' _
          _ ≤ P.natDegree := natDegree_map_le

/-- A derivative-closed family along whose slots membership in `T` is constant. -/
theorem exists_adapted_family {T : Set (Fin (n + 1) → ℝ)} (hT : SAOn T) :
    ∃ F : List (ParamPoly n), DerivClosed F ∧ ∀ (g : Fin n → ℝ) (y y' : ℝ),
      slotIndex F g y = slotIndex F g y' →
        ((Fin.snoc g y : Fin (n + 1) → ℝ) ∈ T ↔ (Fin.snoc g y' : Fin (n + 1) → ℝ) ∈ T) := by
  obtain ⟨F₀, sigs, hF₀⟩ := hT
  refine ⟨derivClosure (F₀.map toParam), derivClosed_derivClosure _, fun g y y' h => ?_⟩
  rw [hF₀, hF₀]
  have : F₀.map (fun q => SignType.sign (MvPolynomial.eval (Fin.snoc g y) q)) =
      F₀.map (fun q => SignType.sign (MvPolynomial.eval (Fin.snoc g y') q)) := by
    refine List.map_congr_left fun q hq => ?_
    rw [← eval_toParam, ← eval_toParam]
    exact sign_eq_of_slotIndex_eq (mem_derivClosure_self (List.mem_map.mpr ⟨q, hq, rfl⟩)) h
  rw [this]

/-- **Decomposition theorem.** -/
theorem exists_saPathConnected_decomposition :
    ∀ (n : ℕ) (S : Set (Fin n → ℝ)), SAOn S → ∃ 𝒟 : Set (Set (Fin n → ℝ)), 𝒟.Finite ∧
      (∀ D ∈ 𝒟, SAOn D ∧ SAPathConnected D) ∧ S = ⋃₀ 𝒟
  | 0, S, hS => by
    refine ⟨{S}, finite_singleton S, ?_, by simp⟩
    rintro D rfl
    exact ⟨hS, SAPathConnected.of_subsingleton fun x _ y _ => Subsingleton.elim x y⟩
  | n + 1, S, hS => by
    classical
    obtain ⟨F₀, sigs, hF₀⟩ := hS
    let F := derivClosure (F₀.map toParam)
    have hF : DerivClosed F := derivClosed_derivClosure _
    -- membership is constant along slots
    have hslot : ∀ (g : Fin n → ℝ) (y y' : ℝ), slotIndex F g y = slotIndex F g y' →
        ((Fin.snoc g y : Fin (n + 1) → ℝ) ∈ S ↔ (Fin.snoc g y' : Fin (n + 1) → ℝ) ∈ S) := by
      intro g y y' h
      rw [hF₀, hF₀]
      have : F₀.map (fun q => SignType.sign (MvPolynomial.eval (Fin.snoc g y) q)) =
          F₀.map (fun q => SignType.sign (MvPolynomial.eval (Fin.snoc g y') q)) := by
        refine List.map_congr_left fun q hq => ?_
        rw [← eval_toParam, ← eval_toParam]
        exact sign_eq_of_slotIndex_eq
          (mem_derivClosure_self (List.mem_map.mpr ⟨q, hq, rfl⟩)) h
      rw [this]
    have hS : SAOn S := ⟨F₀, sigs, hF₀⟩
    let N := ∑ P ∈ F.toFinset, P.natDegree
    let M : ℕ → Set (Fin n → ℝ) := fun j =>
      {g | ∃ y, (Fin.snoc g y : Fin (n + 1) → ℝ) ∈ slotSet F j ∩ S}
    have hM : ∀ j, SAOn (M j) := fun j => SAOn.exists_snoc ((saOn_slotSet F j).inter hS)
    let E : ℕ → Finset ℕ → Set (Fin n → ℝ) := fun k J =>
      {g | (rootSet F g).ncard = k} ∩ ⋂ j ∈ Finset.range (2 * N + 1), if j ∈ J then M j else (M j)ᶜ
    have hE : ∀ k J, SAOn (E k J) := by
      intro k J
      refine (saOn_ncard_rootSet_eq F k).inter (SAOn.finset_iInter _ fun j _ => ?_)
      split_ifs
      · exact hM j
      · exact (hM j).compl
    choose 𝒟E h𝒟fin h𝒟prop h𝒟eq using fun k J => exists_saPathConnected_decomposition n (E k J) (hE k J)
    let 𝒟 : Set (Set (Fin (n + 1) → ℝ)) :=
      ⋃ k ∈ (Finset.range (N + 1) : Set ℕ), ⋃ J ∈ ((Finset.range (2 * N + 1)).powerset : Set (Finset ℕ)),
        ⋃ D ∈ 𝒟E k J, (fun j => cell F D j) '' (J : Set ℕ)
    refine ⟨𝒟, ?_, ?_, ?_⟩
    · exact (Finset.finite_toSet _).biUnion fun k _ => (Finset.finite_toSet _).biUnion fun J _ =>
        (h𝒟fin k J).biUnion fun D _ => (Finset.finite_toSet J).image _
    · intro C hC
      simp only [𝒟, mem_iUnion, mem_image, exists_prop] at hC
      obtain ⟨k, -, J, -, D, hD, j, -, rfl⟩ := hC
      obtain ⟨hDsa, hDpc⟩ := h𝒟prop k J D hD
      have hDE : D ⊆ E k J := by
        rw [h𝒟eq k J]
        exact subset_sUnion_of_mem hD
      exact ⟨saOn_cell hDsa j, hDpc.cell hF (fun g hg => (hDE hg).1) j⟩
    · ext h
      constructor
      · intro hh
        set g := Fin.init h
        set y := h (Fin.last n)
        have hsnoc : (Fin.snoc g y : Fin (n + 1) → ℝ) = h := Fin.snoc_init_self h
        let k := (rootSet F g).ncard
        have hkN : k ≤ N := ncard_rootSet_le F g
        let J := (Finset.range (2 * N + 1)).filter fun j => g ∈ M j
        have hgE : g ∈ E k J := by
          refine ⟨rfl, mem_iInter₂.mpr fun j hj => ?_⟩
          by_cases hgj : g ∈ M j
          · have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨hj, hgj⟩
            rw [ite_eq_left hjJ]
            exact hgj
          · have hjJ : j ∉ J := fun h => hgj (Finset.mem_filter.mp h).2
            rw [ite_eq_right hjJ]
            exact hgj
        rw [h𝒟eq k J] at hgE
        obtain ⟨D, hD, hgD⟩ := hgE
        let j := slotIndex F g y
        have hjN : j < 2 * N + 1 := by
          have := slotIndex_le F g y
          omega
        have hgMj : g ∈ M j := by
          refine ⟨y, ?_, ?_⟩
          · simp only [slotSet, Fin.init_snoc, Fin.snoc_last, mem_ofPred_eq]
            rfl
          · rw [hsnoc]
            exact hh
        have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjN, hgMj⟩
        refine ⟨cell F D j, ?_, ?_⟩
        · simp only [𝒟, mem_iUnion, mem_image, exists_prop, Finset.coe_range, mem_Iio,
            Finset.coe_powerset, mem_preimage, mem_powerset_iff]
          exact ⟨k, by omega, J, fun x hx => Finset.mem_range.mp (Finset.mem_filter.mp hx).1, D, hD, j,
            hjJ, rfl⟩
        · rw [← hsnoc]
          exact snoc_mem_cell.mpr ⟨hgD, rfl⟩
      · rintro ⟨C, hC, hhC⟩
        simp only [𝒟, mem_iUnion, mem_image, exists_prop] at hC
        obtain ⟨k, -, J, hJ, D, hD, j, hjJ, rfl⟩ := hC
        obtain ⟨hgD, hslotj⟩ := hhC
        have hDE : D ⊆ E k J := by
          rw [h𝒟eq k J]
          exact subset_sUnion_of_mem hD
        have hgE := (hDE hgD).2
        have hjr : j ∈ Finset.range (2 * N + 1) := by
          have := Finset.mem_powerset.mp hJ
          exact this (Finset.mem_coe.mp hjJ)
        have hgM := mem_iInter₂.mp hgE j hjr
        rw [ite_eq_left (Finset.mem_coe.mp hjJ)] at hgM
        obtain ⟨y', hy'slot, hy'S⟩ := hgM
        have hs' : slotIndex F (Fin.init h) y' = j := by
          simpa [slotSet] using hy'slot
        have := (hslot (Fin.init h) y' (h (Fin.last n)) (hs'.trans hslotj.symm)).mp hy'S
        rwa [Fin.snoc_init_self] at this

end NLQCLean
