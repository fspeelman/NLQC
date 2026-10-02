import NLQCLean.Semialgebraic.CellDecomposition

/-!
# Semialgebraic choice

For a semialgebraic `T ⊆ ℝⁿ × ℝ` there is a function `φ : ℝⁿ → ℝ` with
semialgebraic graph such that `(g, φ g) ∈ T` whenever the fibre of `T` over
`g` is nonempty: take the first slot meeting the fibre and a canonical point of
that slot (the root itself, the midpoint of a bounded band, one unit beyond the
extreme root, or `0`).
-/

noncomputable section

namespace NLQCLean

open Set Sundog.TarskiQE

variable {n : ℕ}

/-- Slot conditions after a polynomial change of coordinates. -/
theorem saOn_slot_eval (F : List (ParamPoly n)) (j : ℕ) {ι : Type*}
    (q : Fin (n + 1) → MvPolynomial ι ℝ) :
    SAOn {w : ι → ℝ | slotIndex F (fun l => MvPolynomial.eval w (q l.castSucc))
      (MvPolynomial.eval w (q (Fin.last n))) = j} :=
  (saOn_slotSet F j).preimage q

/-- A canonical point of slot `j` at `g`. -/
def slotPoint (F : List (ParamPoly n)) (g : Fin n → ℝ) (j : ℕ) : ℝ :=
  if j % 2 = 1 then rootFn F g (j / 2)
  else if j / 2 = 0 then (if (rootSet F g).ncard = 0 then 0 else rootFn F g 0 - 1)
  else if j / 2 < (rootSet F g).ncard then (rootFn F g (j / 2 - 1) + rootFn F g (j / 2)) / 2
  else rootFn F g (j / 2 - 1) + 1

/-- The defining relation of `slotPoint`, for `k` roots. -/
def SlotPointRel (F : List (ParamPoly n)) (k j : ℕ) (g : Fin n → ℝ) (y : ℝ) : Prop :=
  if j % 2 = 1 then slotIndex F g y = j
  else if j / 2 = 0 then (if k = 0 then y = 0 else slotIndex F g (y + 1) = 1)
  else if j / 2 < k then ∃ b, slotIndex F g b = j + 1 ∧ slotIndex F g (2 * y - b) = j - 1
  else slotIndex F g (y - 1) = j - 1

theorem eq_slotPoint_iff {F : List (ParamPoly n)} {g : Fin n → ℝ} {j : ℕ}
    (hj : j ≤ 2 * (rootSet F g).ncard) (y : ℝ) :
    y = slotPoint F g j ↔ SlotPointRel F (rootSet F g).ncard j g y := by
  set k := (rootSet F g).ncard with hk
  have hfin := rootSet_finite F g
  unfold slotPoint SlotPointRel
  by_cases hodd : j % 2 = 1
  · rw [ite_eq_left hodd, ite_eq_left hodd]
    obtain ⟨i, rfl⟩ : ∃ i, j = 2 * i + 1 := ⟨j / 2, by omega⟩
    have e1 : (2 * i + 1) / 2 = i := by omega
    rw [e1, slotIndex_odd_iff (by omega)]
  rw [ite_eq_right hodd, ite_eq_right hodd]
  by_cases h0 : j / 2 = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    by_cases hk0 : k = 0
    · rw [ite_eq_left hk0, ite_eq_left hk0]
    · rw [ite_eq_right hk0, ite_eq_right hk0]
      have := slotIndex_odd_iff (F := F) (g := g) (i := 0) (by omega) (y + 1)
      rw [Nat.mul_zero, zero_add] at this
      rw [this]
      constructor <;> intro h <;> linarith
  rw [ite_eq_right h0, ite_eq_right h0]
  have hi1 : j / 2 - 1 < k := by omega
  have hodd' : j - 1 = 2 * (j / 2 - 1) + 1 := by omega
  by_cases hlt : j / 2 < k
  · rw [ite_eq_left hlt, ite_eq_left hlt]
    have hodd'' : j + 1 = 2 * (j / 2) + 1 := by omega
    simp only [hodd', hodd'', slotIndex_odd_iff hlt, slotIndex_odd_iff hi1, exists_eq_left]
    constructor <;> intro h <;> linarith
  · rw [ite_eq_right hlt, ite_eq_right hlt, hodd', slotIndex_odd_iff hi1]
    constructor <;> intro h <;> linarith

theorem slotIndex_slotPoint {F : List (ParamPoly n)} {g : Fin n → ℝ} {j : ℕ}
    (hj : j ≤ 2 * (rootSet F g).ncard) : slotIndex F g (slotPoint F g j) = j := by
  set k := (rootSet F g).ncard with hk
  have hfin := rootSet_finite F g
  by_cases hodd : j % 2 = 1
  · have hj' : j = 2 * (j / 2) + 1 := by omega
    have hi : j / 2 < k := by omega
    conv_rhs => rw [hj']
    rw [slotIndex_odd_iff hi]
    simp [slotPoint, hodd]
  · have hj' : j = 2 * (j / 2) := by omega
    have hi : j / 2 ≤ k := by omega
    conv_rhs => rw [hj']
    rw [slotIndex_even_iff hi]
    simp only [slotPoint, hodd, ite_false]
    by_cases h0 : j / 2 = 0
    · simp only [h0, ite_true]
      refine ⟨fun h => absurd h (lt_irrefl 0), fun hk0 => ?_⟩
      rw [ite_eq_right (by omega)]
      linarith
    · simp only [h0, ite_false]
      by_cases hlt : j / 2 < k
      · rw [ite_eq_left hlt]
        have := nthElem_lt_nthElem hfin (show j / 2 - 1 < j / 2 by omega) hlt
        unfold rootFn
        constructor <;> intro <;> linarith
      · rw [ite_eq_right hlt]
        exact ⟨fun _ => by linarith, fun h => absurd h hlt⟩

theorem saOn_slotPointRel (F : List (ParamPoly n)) (k j : ℕ) :
    SAOn {h : Fin (n + 1) → ℝ | SlotPointRel F k j (Fin.init h) (h (Fin.last n))} := by
  unfold SlotPointRel
  split_ifs with h1 h2 h3 h4
  · exact (saOn_slotSet F j).congr fun h => Iff.rfl
  · exact (SAOn.eq (MvPolynomial.X (Fin.last n)) 0).congr fun h => by simp
  · refine (saOn_slot_eval F 1 (Fin.lastCases (MvPolynomial.X (Fin.last n) + 1)
      fun l => MvPolynomial.X l.castSucc)).congr fun h => ?_
    simp
    exact Iff.rfl
  · -- one auxiliary coordinate for the upper root
    let q₁ : Fin (n + 1) → MvPolynomial (Fin (n + 2)) ℝ :=
      Fin.lastCases (MvPolynomial.X (Fin.last (n + 1))) fun l => MvPolynomial.X l.castSucc.castSucc
    let q₂ : Fin (n + 1) → MvPolynomial (Fin (n + 2)) ℝ :=
      Fin.lastCases (2 * MvPolynomial.X (Fin.last n).castSucc - MvPolynomial.X (Fin.last (n + 1)))
        fun l => MvPolynomial.X l.castSucc.castSucc
    have hA := (saOn_slot_eval F (j + 1) q₁).inter (saOn_slot_eval F (j - 1) q₂)
    refine (SAOn.exists_snoc hA).congr fun h => ?_
    simp [q₁, q₂]
    exact Iff.rfl
  · refine (saOn_slot_eval F (j - 1) (Fin.lastCases (MvPolynomial.X (Fin.last n) - 1)
      fun l => MvPolynomial.X l.castSucc)).congr fun h => ?_
    simp [sub_eq_add_neg]
    exact Iff.rfl

/-- **Semialgebraic choice in one variable.** -/
theorem exists_saChoice {T : Set (Fin (n + 1) → ℝ)} (hT : SAOn T) :
    ∃ φ : (Fin n → ℝ) → ℝ, SAOn {h : Fin (n + 1) → ℝ | h (Fin.last n) = φ (Fin.init h)} ∧
      ∀ g, (∃ y, (Fin.snoc g y : Fin (n + 1) → ℝ) ∈ T) →
        (Fin.snoc g (φ g) : Fin (n + 1) → ℝ) ∈ T := by
  classical
  obtain ⟨F, -, hslot⟩ := exists_adapted_family hT
  let N := ∑ P ∈ F.toFinset, P.natDegree
  let M : ℕ → Set (Fin n → ℝ) := fun j =>
    {g | ∃ y, (Fin.snoc g y : Fin (n + 1) → ℝ) ∈ slotSet F j ∩ T}
  have hM : ∀ j, SAOn (M j) := fun j => SAOn.exists_snoc ((saOn_slotSet F j).inter hT)
  have hMle : ∀ j g, g ∈ M j → j ≤ 2 * (rootSet F g).ncard := by
    rintro j g ⟨y, hy, -⟩
    have := slotIndex_le F g y
    simp only [slotSet, mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hy
    omega
  let jstar : (Fin n → ℝ) → ℕ := fun g => if h : ∃ j, g ∈ M j then Nat.find h else 0
  have hjstar_le : ∀ g, jstar g ≤ 2 * (rootSet F g).ncard := by
    intro g
    by_cases h : ∃ j, g ∈ M j
    · simp only [jstar, dite_eq_left h]
      exact hMle _ g (Nat.find_spec h)
    · simp only [jstar, dite_eq_right h]
      exact Nat.zero_le _
  refine ⟨fun g => slotPoint F g (jstar g), ?_, ?_⟩
  · -- the graph
    have hJ : ∀ j, SAOn {g : Fin n → ℝ | jstar g = j} := by
      intro j
      have hnone : SAOn {g : Fin n → ℝ | ∀ j' ∈ Finset.range (2 * N + 1), g ∉ M j'} :=
        (SAOn.finset_iInter (Finset.range (2 * N + 1)) fun j' _ => (hM j').compl).congr
          fun g => by simp
      have hfirst : SAOn {g : Fin n → ℝ | g ∈ M j ∧ ∀ j' ∈ Finset.range j, g ∉ M j'} :=
        (hM j).inter ((SAOn.finset_iInter (Finset.range j) fun j' _ => (hM j').compl).congr
          fun g => by simp; rfl)
      have hex : ∀ g, (∃ j', g ∈ M j') ↔ ∃ j' ∈ Finset.range (2 * N + 1), g ∈ M j' := by
        intro g
        constructor
        · rintro ⟨j', hj'⟩
          refine ⟨j', Finset.mem_range.mpr ?_, hj'⟩
          have := hMle j' g hj'
          have := ncard_rootSet_le F g
          omega
        · rintro ⟨j', -, hj'⟩
          exact ⟨j', hj'⟩
      by_cases hj0 : j = 0
      · subst hj0
        refine (hfirst.union hnone).congr fun g => ?_
        simp only [mem_union, mem_ofPred_eq, jstar]
        by_cases h : ∃ j', g ∈ M j'
        · rw [dite_eq_left h, Nat.find_eq_zero]
          constructor
          · rintro (⟨h0, -⟩ | hn)
            · exact h0
            · obtain ⟨j', hj', hgj'⟩ := (hex g).mp h
              exact absurd hgj' (hn j' hj')
          · intro h0
            exact Or.inl ⟨h0, by simp⟩
        · rw [dite_eq_right h]
          simp only [iff_true]
          right
          intro j' _ hj'
          exact h ⟨j', hj'⟩
      · refine hfirst.congr fun g => ?_
        simp only [mem_ofPred_eq, jstar, Finset.mem_range]
        constructor
        · rintro ⟨hgj, hmin⟩
          have h : ∃ j', g ∈ M j' := ⟨j, hgj⟩
          rw [dite_eq_left h]
          refine le_antisymm (Nat.find_min' h hgj) ?_
          by_contra hlt
          exact hmin _ (not_le.mp hlt) (Nat.find_spec h)
        · intro hgj
          by_cases h : ∃ j', g ∈ M j'
          · rw [dite_eq_left h] at hgj
            subst hgj
            exact ⟨Nat.find_spec h, fun j' hj' => Nat.find_min h hj'⟩
          · rw [dite_eq_right h] at hgj
            exact absurd hgj.symm hj0
    have hG : {h : Fin (n + 1) → ℝ | h (Fin.last n) = slotPoint F (Fin.init h) (jstar (Fin.init h))} =
        ⋃ k ∈ Finset.range (N + 1), ⋃ j ∈ Finset.range (2 * N + 1),
          {h : Fin (n + 1) → ℝ | (rootSet F (Fin.init h)).ncard = k ∧ jstar (Fin.init h) = j ∧
            SlotPointRel F k j (Fin.init h) (h (Fin.last n))} := by
      ext h
      rw [mem_iUnion₂]
      constructor
      · intro hh
        have hkN := ncard_rootSet_le F (Fin.init h)
        have hjN := hjstar_le (Fin.init h)
        refine ⟨(rootSet F (Fin.init h)).ncard, Finset.mem_range.mpr (by omega), ?_⟩
        rw [mem_iUnion₂]
        exact ⟨jstar (Fin.init h), Finset.mem_range.mpr (by omega), rfl, rfl,
          (eq_slotPoint_iff (hjstar_le _) _).mp hh⟩
      · rintro ⟨k, -, hh⟩
        rw [mem_iUnion₂] at hh
        obtain ⟨j, -, hk, hj, hrel⟩ := hh
        subst hk hj
        exact (eq_slotPoint_iff (hjstar_le _) _).mpr hrel
    rw [hG]
    refine SAOn.finset_iUnion _ fun k _ => SAOn.finset_iUnion _ fun j _ => ?_
    exact ((saOn_ncard_rootSet_eq F k).comap Fin.castSucc).inter
      (((hJ j).comap Fin.castSucc).inter (saOn_slotPointRel F k j))
  · rintro g ⟨y, hy⟩
    have h : ∃ j, g ∈ M j := ⟨slotIndex F g y, y, by simp [slotSet], hy⟩
    have hjs : jstar g = Nat.find h := by simp only [jstar, dite_eq_left h]
    obtain ⟨y', hy'slot, hy'T⟩ := Nat.find_spec h
    simp only [slotSet, mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hy'slot
    have hpt := slotIndex_slotPoint (F := F) (g := g) (hjstar_le g)
    show (Fin.snoc g (slotPoint F g (jstar g)) : Fin (n + 1) → ℝ) ∈ T
    rw [hjs] at hpt ⊢
    exact (hslot g y' _ (hy'slot.trans hpt.symm)).mp hy'T

/-- One-variable choice for any finite parameter type. -/
theorem exists_saChoice_option {ι : Type*} [Fintype ι] {T : Set (Option ι → ℝ)} (hT : SAOn T) :
    ∃ φ : (ι → ℝ) → ℝ, SAOn {w : Option ι → ℝ | w none = φ (w ∘ some)} ∧
      ∀ x, (∃ y, (fun o => o.elim y x) ∈ T) → (fun o => o.elim (φ x) x) ∈ T := by
  classical
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let E : Option ι ≃ Fin (n + 1) := (Equiv.optionCongr e).trans (finSuccEquivLast (n := n)).symm
  have hE : ∀ (x : ι → ℝ) (y : ℝ),
      (Fin.snoc (x ∘ e.symm) y : Fin (n + 1) → ℝ) ∘ E = fun o => o.elim y x := by
    intro x y
    funext o
    cases o with
    | none => simp [E]
    | some i => simp [E]
  have hT' : SAOn {h : Fin (n + 1) → ℝ | h ∘ E ∈ T} := hT.comap E
  obtain ⟨φ₀, hgraph, hspec⟩ := exists_saChoice hT'
  refine ⟨fun x => φ₀ (x ∘ e.symm), ?_, fun x ⟨y, hy⟩ => ?_⟩
  · refine (hgraph.comap E.symm).congr fun w => ?_
    simp only [mem_ofPred_eq]
    have h1 : (w ∘ E.symm) (Fin.last n) = w none := by
      simp [E]
      rfl
    have h2 : Fin.init (w ∘ E.symm) = (w ∘ some) ∘ e.symm := by
      funext i
      simp [E, Fin.init]
      rfl
    rw [h1, h2]
  · have := hspec (x ∘ e.symm) ⟨y, by simpa [mem_ofPred_eq, hE] using hy⟩
    simpa [mem_ofPred_eq, hE] using this

theorem exists_saChoice_sum_aux (κ : Type) [Fintype κ] : ∀ (ι : Type) [Fintype ι]
    (T : Set (ι ⊕ κ → ℝ)), SAOn T → ∃ φ : (ι → ℝ) → (κ → ℝ),
      SAOn {w : ι ⊕ κ → ℝ | w ∘ Sum.inr = φ (w ∘ Sum.inl)} ∧
        ∀ x, (∃ y, Sum.elim x y ∈ T) → Sum.elim x (φ x) ∈ T := by
  classical
  refine Fintype.induction_empty_option (P := fun κ _ => ∀ (ι : Type) [Fintype ι]
    (T : Set (ι ⊕ κ → ℝ)), SAOn T → ∃ φ : (ι → ℝ) → (κ → ℝ),
      SAOn {w : ι ⊕ κ → ℝ | w ∘ Sum.inr = φ (w ∘ Sum.inl)} ∧
        ∀ x, (∃ y, Sum.elim x y ∈ T) → Sum.elim x (φ x) ∈ T) ?_ ?_ ?_ κ
  · intro α β _ e ih ι _ T hT
    have hT' : SAOn {z : ι ⊕ α → ℝ | z ∘ (Equiv.sumCongr (Equiv.refl ι) e).symm ∈ T} :=
      hT.comap _
    obtain ⟨φ, hgraph, hspec⟩ := ih ι _ hT'
    have hcomp : ∀ (x : ι → ℝ) (y : α → ℝ),
        Sum.elim x y ∘ (Equiv.sumCongr (Equiv.refl ι) e).symm = Sum.elim x (y ∘ e.symm) := by
      intro x y
      funext z
      cases z <;> simp
    refine ⟨fun x => φ x ∘ e.symm, ?_, fun x ⟨y, hy⟩ => ?_⟩
    · refine (hgraph.comap (Equiv.sumCongr (Equiv.refl ι) e)).congr fun w => ?_
      simp only [mem_ofPred_eq]
      constructor
      · intro h
        funext b
        have := congrFun h (e.symm b)
        simpa [Function.comp_def] using this
      · intro h
        funext a
        have := congrFun h (e a)
        simpa [Function.comp_def] using this
    · have h1 : Sum.elim x (y ∘ e) ∘ ⇑(Equiv.sumCongr (Equiv.refl ι) e).symm = Sum.elim x y := by
        rw [hcomp]
        congr 1
        funext b
        simp
      have := hspec x ⟨y ∘ e, by show _ ∈ T; rw [h1]; exact hy⟩
      change Sum.elim x (φ x) ∘ _ ∈ T at this
      rwa [hcomp] at this
  · intro ι _ T _
    refine ⟨fun _ => PEmpty.elim, SAOn.univ.congr fun w => ?_, fun x ⟨y, hy⟩ => ?_⟩
    · simp only [mem_univ, true_iff, mem_ofPred_eq]
      funext z
      exact z.elim
    · convert hy using 2
      funext z
      exact z.elim
  · intro α _ ih ι _ T hT
    -- first the coordinates of `α`
    let reorg : (ι ⊕ α → ℝ) → ℝ → (ι ⊕ Option α → ℝ) := fun u t => fun z => match z with
      | Sum.inl i => u (Sum.inl i)
      | Sum.inr none => t
      | Sum.inr (some a) => u (Sum.inr a)
    have hU : SAOn {v : Option (ι ⊕ α) → ℝ | reorg (v ∘ some) (v none) ∈ T} :=
      (hT.preimage fun z => match z with
        | Sum.inl i => MvPolynomial.X (some (Sum.inl i))
        | Sum.inr none => MvPolynomial.X none
        | Sum.inr (some a) => MvPolynomial.X (some (Sum.inr a))).congr fun v => by
        simp only [mem_ofPred_eq]
        constructor <;> intro h <;> convert h using 1 <;> funext z <;>
          rcases z with i | _ | a <;> simp [reorg]
    have hT₁ : SAOn {u : ι ⊕ α → ℝ | ∃ t, reorg u t ∈ T} :=
      (SAOn.exists_option hU).congr fun u => by simp [mem_ofPred_eq, Function.comp_def]
    obtain ⟨φ₁, hgraph₁, hspec₁⟩ := ih ι _ hT₁
    obtain ⟨ψ, hgraphψ, hspecψ⟩ := exists_saChoice_option hU
    let φ : (ι → ℝ) → (Option α → ℝ) := fun x o => o.elim (ψ (Sum.elim x (φ₁ x))) (φ₁ x)
    have hreorg : ∀ (x : ι → ℝ) (y : Option α → ℝ),
        Sum.elim x y = reorg (Sum.elim x (y ∘ some)) (y none) := by
      intro x y
      funext z
      rcases z with i | _ | a <;> rfl
    refine ⟨φ, ?_, fun x ⟨y, hy⟩ => ?_⟩
    · -- the graph: the `α`-part, then the new coordinate
      let pα : ι ⊕ α → ι ⊕ Option α := Sum.map id some
      let pβ : Option (ι ⊕ α) → ι ⊕ Option α := fun o => o.elim (Sum.inr none) pα
      refine ((hgraph₁.comap pα).inter (hgraphψ.comap pβ)).congr fun w => ?_
      simp only [mem_inter_iff, mem_ofPred_eq]
      have e4 : (w ∘ pβ) ∘ some = Sum.elim (w ∘ Sum.inl) ((w ∘ Sum.inr) ∘ some) := by
        funext z
        cases z <;> rfl
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : (w ∘ Sum.inr) ∘ some = φ₁ (w ∘ Sum.inl) := by
          funext a
          exact congrFun h1 a
        rw [e4, h1'] at h2
        funext o
        cases o with
        | none => exact h2
        | some a => exact congrFun h1' a
      · intro h
        have h1 : (w ∘ Sum.inr) ∘ some = φ₁ (w ∘ Sum.inl) := by
          funext a
          exact congrFun h (some a)
        refine ⟨by funext a; exact congrFun h1 a, ?_⟩
        rw [e4, h1]
        exact congrFun h none
    · have hx₁ : Sum.elim x (φ₁ x) ∈ {u : ι ⊕ α → ℝ | ∃ t, reorg u t ∈ T} :=
        hspec₁ x ⟨y ∘ some, y none, by rw [← hreorg]; exact hy⟩
      obtain ⟨t, ht⟩ := hx₁
      have hψ := hspecψ (Sum.elim x (φ₁ x)) ⟨t, by simpa [mem_ofPred_eq, Function.comp_def] using ht⟩
      simp only [mem_ofPred_eq, Function.comp_def, Option.elim] at hψ
      rw [hreorg]
      exact hψ

/-- **Semialgebraic choice.** For a semialgebraic `T ⊆ ℝ^ι × ℝ^κ` there is a
map `φ` with semialgebraic graph choosing a point of every nonempty fibre. -/
theorem exists_saChoice_sum {ι κ : Type} [Fintype ι] [Fintype κ] {T : Set (ι ⊕ κ → ℝ)}
    (hT : SAOn T) : ∃ φ : (ι → ℝ) → (κ → ℝ),
      SAOn {w : ι ⊕ κ → ℝ | w ∘ Sum.inr = φ (w ∘ Sum.inl)} ∧
        ∀ x, (∃ y, Sum.elim x y ∈ T) → Sum.elim x (φ x) ∈ T :=
  exists_saChoice_sum_aux κ ι T hT

end NLQCLean
