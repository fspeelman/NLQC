import NLQCLean.Vendor.Sundog.SemialgebraicProjection
import NLQCLean.Semialgebraic.SundogBridge

/-!
# First-order definability of semialgebraic sets

`SAOn S` says that `S ⊆ (ι → ℝ)` is a sign-vector condition on a finite list of
real polynomials in the coordinates `ι`. These sets are closed under Boolean
operations, preimages under polynomial maps, and existential quantification
over any finite set of coordinates (Tarski–Seidenberg, via the vendored
`Sundog.TarskiQE.sadef_proj`). For `ι = Fin n` the notion agrees with the
project's `Semialgebraic` predicate on `RealEuclidean n`.
-/

noncomputable section

namespace NLQCLean

open MvPolynomial Sundog.TarskiQE

/-- A sign-vector condition on finitely many real polynomials. -/
def SAOn {ι : Type*} (S : Set (ι → ℝ)) : Prop :=
  ∃ (F : List (MvPolynomial ι ℝ)) (sigs : List (List SignType)),
    ∀ x, x ∈ S ↔ F.map (fun q => SignType.sign (eval x q)) ∈ sigs

namespace SAOn

variable {ι κ : Type*}

theorem congr {S T : Set (ι → ℝ)} (hS : SAOn S) (h : ∀ x, x ∈ S ↔ x ∈ T) : SAOn T := by
  obtain ⟨F, sigs, hF⟩ := hS
  exact ⟨F, sigs, fun x => (h x).symm.trans (hF x)⟩

theorem of_eq {S T : Set (ι → ℝ)} (hS : SAOn S) (h : S = T) : SAOn T := h ▸ hS

theorem compl {S : Set (ι → ℝ)} (hS : SAOn S) : SAOn Sᶜ := by
  obtain ⟨F, sigs, hch⟩ := hS
  refine ⟨F, (allSignVecs F.length).filter (fun τ => τ ∉ sigs), fun h => ?_⟩
  constructor
  · intro hc
    rw [List.mem_filter]
    refine ⟨mem_allSignVecs (by simp), ?_⟩
    simp only [decide_eq_true_eq]
    exact fun hmem => hc ((hch h).mpr hmem)
  · intro hmem hA'
    rw [List.mem_filter] at hmem
    have h2 := hmem.2
    simp only [decide_eq_true_eq] at h2
    exact h2 ((hch h).mp hA')

theorem union {S T : Set (ι → ℝ)} (hS : SAOn S) (hT : SAOn T) : SAOn (S ∪ T) := by
  obtain ⟨FA, sigsA, hchA⟩ := hS
  obtain ⟨FB, sigsB, hchB⟩ := hT
  refine ⟨FA ++ FB, (allSignVecs (FA ++ FB).length).filter
    (fun τ => τ.take FA.length ∈ sigsA ∨ τ.drop FA.length ∈ sigsB), fun h => ?_⟩
  have hsplit : (FA ++ FB).map (fun q => SignType.sign (eval h q))
      = (FA.map fun q => SignType.sign (eval h q))
        ++ (FB.map fun q => SignType.sign (eval h q)) := by
    rw [List.map_append]
  have htake : ((FA ++ FB).map (fun q => SignType.sign (eval h q))).take FA.length
      = FA.map fun q => SignType.sign (eval h q) := by
    rw [hsplit]
    exact List.take_left' (by rw [List.length_map])
  have hdrop : ((FA ++ FB).map (fun q => SignType.sign (eval h q))).drop FA.length
      = FB.map fun q => SignType.sign (eval h q) := by
    rw [hsplit]
    exact List.drop_left' (by rw [List.length_map])
  constructor
  · intro hmem
    rw [List.mem_filter]
    refine ⟨mem_allSignVecs (by simp), ?_⟩
    simp only [decide_eq_true_eq]
    rcases hmem with hA' | hB'
    · exact Or.inl (by rw [htake]; exact (hchA h).mp hA')
    · exact Or.inr (by rw [hdrop]; exact (hchB h).mp hB')
  · intro hmem
    rw [List.mem_filter] at hmem
    have h2 := hmem.2
    simp only [decide_eq_true_eq] at h2
    rcases h2 with hA' | hB'
    · exact Or.inl ((hchA h).mpr (by rw [htake] at hA'; exact hA'))
    · exact Or.inr ((hchB h).mpr (by rw [hdrop] at hB'; exact hB'))

theorem inter {S T : Set (ι → ℝ)} (hS : SAOn S) (hT : SAOn T) : SAOn (S ∩ T) := by
  have h := (hS.compl.union hT.compl).compl
  rwa [Set.compl_union, compl_compl, compl_compl] at h

theorem diff {S T : Set (ι → ℝ)} (hS : SAOn S) (hT : SAOn T) : SAOn (S \ T) :=
  hS.inter hT.compl

/-- The basic sign set of one polynomial. -/
theorem sign_eq (q : MvPolynomial ι ℝ) (s : SignType) :
    SAOn {x : ι → ℝ | SignType.sign (eval x q) = s} :=
  ⟨[q], [[s]], fun x => by simp⟩

theorem univ : SAOn (Set.univ : Set (ι → ℝ)) :=
  ⟨[], [[]], fun x => by simp⟩

theorem empty : SAOn (∅ : Set (ι → ℝ)) := by
  have h := (univ (ι := ι)).compl
  rwa [Set.compl_univ] at h

theorem zero (q : MvPolynomial ι ℝ) : SAOn {x : ι → ℝ | eval x q = 0} :=
  (sign_eq q 0).congr fun x => by simp

theorem pos (q : MvPolynomial ι ℝ) : SAOn {x : ι → ℝ | 0 < eval x q} :=
  (sign_eq q 1).congr fun x => by simp [sign_eq_one_iff]

theorem ne_zero (q : MvPolynomial ι ℝ) : SAOn {x : ι → ℝ | eval x q ≠ 0} :=
  (zero q).compl

theorem lt (p q : MvPolynomial ι ℝ) : SAOn {x : ι → ℝ | eval x p < eval x q} :=
  (pos (q - p)).congr fun x => by simp

theorem le (p q : MvPolynomial ι ℝ) : SAOn {x : ι → ℝ | eval x p ≤ eval x q} :=
  (lt q p).compl.congr fun x => by simp

theorem eq (p q : MvPolynomial ι ℝ) : SAOn {x : ι → ℝ | eval x p = eval x q} :=
  (zero (p - q)).congr fun x => by simp [sub_eq_zero]

theorem list_iUnion {α : Type*} (l : List α) {S : α → Set (ι → ℝ)}
    (h : ∀ a ∈ l, SAOn (S a)) : SAOn (⋃ a ∈ l, S a) := by
  induction l with
  | nil => exact empty.of_eq (by simp)
  | cons a l ih =>
    refine ((h a List.mem_cons_self).union
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))).of_eq ?_
    ext x
    simp

theorem list_iInter {α : Type*} (l : List α) {S : α → Set (ι → ℝ)}
    (h : ∀ a ∈ l, SAOn (S a)) : SAOn (⋂ a ∈ l, S a) := by
  induction l with
  | nil => exact univ.of_eq (by simp)
  | cons a l ih =>
    refine ((h a List.mem_cons_self).inter
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))).of_eq ?_
    ext x
    simp

theorem finset_iUnion {α : Type*} (s : Finset α) {S : α → Set (ι → ℝ)}
    (h : ∀ a ∈ s, SAOn (S a)) : SAOn (⋃ a ∈ s, S a) :=
  (list_iUnion s.toList fun a ha => h a (Finset.mem_toList.mp ha)).of_eq (by simp)

theorem finset_iInter {α : Type*} (s : Finset α) {S : α → Set (ι → ℝ)}
    (h : ∀ a ∈ s, SAOn (S a)) : SAOn (⋂ a ∈ s, S a) :=
  (list_iInter s.toList fun a ha => h a (Finset.mem_toList.mp ha)).of_eq (by simp)

theorem fintype_iUnion {α : Type*} [Fintype α] {S : α → Set (ι → ℝ)}
    (h : ∀ a, SAOn (S a)) : SAOn (⋃ a, S a) :=
  (finset_iUnion Finset.univ fun a _ => h a).of_eq (by simp)

theorem fintype_iInter {α : Type*} [Fintype α] {S : α → Set (ι → ℝ)}
    (h : ∀ a, SAOn (S a)) : SAOn (⋂ a, S a) :=
  (finset_iInter Finset.univ fun a _ => h a).of_eq (by simp)

/-- Preimages under polynomial maps. -/
theorem preimage {S : Set (κ → ℝ)} (hS : SAOn S) (Q : κ → MvPolynomial ι ℝ) :
    SAOn {x : ι → ℝ | (fun j => eval x (Q j)) ∈ S} := by
  obtain ⟨F, sigs, hF⟩ := hS
  refine ⟨F.map (bind₁ Q), sigs, fun x => ?_⟩
  rw [Set.mem_ofPred_eq, hF, List.map_map]
  have : ((fun q => SignType.sign (eval x q)) ∘ bind₁ Q) =
      fun q => SignType.sign (eval (fun j => eval x (Q j)) q) := by
    funext q
    simp only [Function.comp_apply]
    congr 1
    induction q using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  rw [this]

/-- Preimages under coordinate maps. -/
theorem comap {S : Set (κ → ℝ)} (hS : SAOn S) (e : κ → ι) :
    SAOn {x : ι → ℝ | x ∘ e ∈ S} :=
  (hS.preimage fun j => X (e j)).congr fun x => by simp [Function.comp_def]

end SAOn

theorem sadef_signVec_eq {n : ℕ} (F : List (MvPolynomial (Fin n) ℝ)) :
    ∀ σ : List SignType,
      SADef n {x : Fin n → ℝ | F.map (fun q => SignType.sign (eval x q)) = σ} := by
  induction F with
  | nil =>
    intro σ
    by_cases hσ : σ = []
    · subst hσ
      have e : {x : Fin n → ℝ | ([] : List (MvPolynomial (Fin n) ℝ)).map
          (fun q => SignType.sign (eval x q)) = []} = Set.univ := by ext; simp
      rw [e]
      exact SADef.univ
    · have e : {x : Fin n → ℝ | ([] : List (MvPolynomial (Fin n) ℝ)).map
          (fun q => SignType.sign (eval x q)) = σ} = ∅ := by
        ext
        simp [eq_comm, hσ]
      rw [e]
      exact SADef.empty
  | cons q F ih =>
    intro σ
    cases σ with
    | nil =>
      have e : {x : Fin n → ℝ | (q :: F).map (fun q => SignType.sign (eval x q)) = []} = ∅ := by
        ext
        simp
      rw [e]
      exact SADef.empty
    | cons s σ =>
      have e : {x : Fin n → ℝ | (q :: F).map (fun q => SignType.sign (eval x q)) = s :: σ} =
          {x | SignType.sign (eval x q) = s} ∩
            {x | F.map (fun q => SignType.sign (eval x q)) = σ} := by
        ext
        simp
      rw [e]
      exact (SADef.signEq q s).inter (ih σ)

/-- On `Fin n`, `SAOn` is Sundog's `SADef`. -/
theorem saOn_iff_sadef {n : ℕ} (S : Set (Fin n → ℝ)) : SAOn S ↔ SADef n S := by
  constructor
  · rintro ⟨F, sigs, hF⟩
    have : S = ⋃ σ ∈ sigs, {x | F.map (fun q => SignType.sign (eval x q)) = σ} := by
      ext x
      simp [hF x]
    rw [this]
    exact SADef.list_biUnion fun σ _ => sadef_signVec_eq F σ
  · intro h
    obtain ⟨F, sigs, hF⟩ := sadef_sign_char h
    exact ⟨F, sigs, hF⟩

namespace SAOn

variable {ι κ : Type*}

/-- Equivalent index types. -/
theorem equiv {S : Set (κ → ℝ)} (hS : SAOn S) (e : ι ≃ κ) :
    SAOn {x : ι → ℝ | x ∘ e.symm ∈ S} :=
  hS.comap e.symm

theorem of_equiv {S : Set (ι → ℝ)} (e : ι ≃ κ) (hS : SAOn {x : κ → ℝ | x ∘ e ∈ S}) :
    SAOn S :=
  (hS.equiv e).congr fun x => by simp [Function.comp_def]

/-- Elimination of the last coordinate. -/
theorem exists_snoc {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} (hA : SAOn A) :
    SAOn {g : Fin n → ℝ | ∃ y : ℝ, Fin.snoc g y ∈ A} :=
  (saOn_iff_sadef _).mpr (sadef_proj ((saOn_iff_sadef _).mp hA))

/-- Elimination of one adjoined coordinate. -/
theorem exists_option [Fintype ι] {A : Set (Option ι → ℝ)} (hA : SAOn A) :
    SAOn {x : ι → ℝ | ∃ y : ℝ, (fun o => o.elim y x) ∈ A} := by
  classical
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let E : Option ι ≃ Fin (n + 1) :=
    (Equiv.optionCongr e).trans (finSuccEquivLast (n := n)).symm
  have hA' : SAOn {h : Fin (n + 1) → ℝ | h ∘ E ∈ A} := hA.equiv E.symm |>.congr fun h => by
    simp [Function.comp_def]
  have hP := exists_snoc hA'
  refine of_equiv e ((hP.comap id).congr fun g => ?_)
  simp only [Set.mem_ofPred_eq, Function.comp_id]
  refine exists_congr fun y => ?_
  have : (Fin.snoc g y : Fin (n + 1) → ℝ) ∘ E = fun o => o.elim y (g ∘ e) := by
    funext o
    cases o with
    | none => simp [E]
    | some i => simp [E]
  rw [this]

theorem exists_sum_aux (κ : Type) [Fintype κ] : ∀ (ι : Type) [Fintype ι]
    (A : Set (ι ⊕ κ → ℝ)), SAOn A → SAOn {x : ι → ℝ | ∃ y : κ → ℝ, Sum.elim x y ∈ A} := by
  classical
  refine Fintype.induction_empty_option (P := fun κ _ => ∀ (ι : Type) [Fintype ι]
    (A : Set (ι ⊕ κ → ℝ)), SAOn A → SAOn {x : ι → ℝ | ∃ y : κ → ℝ, Sum.elim x y ∈ A})
    ?_ ?_ ?_ κ
  · intro α β _ e ih ι _ A hA
    have h := ih ι {z | z ∘ (Equiv.sumCongr (Equiv.refl ι) e).symm ∈ A}
      (hA.equiv (Equiv.sumCongr (Equiv.refl ι) e))
    refine h.congr fun x => ?_
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y ∘ e.symm, ?_⟩
      convert hy using 1
      funext z
      cases z <;> simp
    · rintro ⟨y, hy⟩
      refine ⟨y ∘ e, ?_⟩
      convert hy using 1
      funext z
      cases z <;> simp
  · intro ι _ A hA
    refine (hA.comap (Sum.elim id fun e => e.elim)).congr fun x => ?_
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨PEmpty.elim, ?_⟩
      convert h using 1
      funext z
      cases z with
      | inl i => rfl
      | inr e => exact e.elim
    · rintro ⟨y, hy⟩
      convert hy using 1
      funext z
      cases z with
      | inl i => rfl
      | inr e => exact e.elim
  · intro α _ ih ι _ A hA
    -- move the new coordinate to the front, then eliminate it and the rest
    let r : Option (ι ⊕ α) → ι ⊕ Option α := fun o => match o with
      | none => Sum.inr none
      | some (Sum.inl i) => Sum.inl i
      | some (Sum.inr a) => Sum.inr (some a)
    have h1 : SAOn {w : Option (ι ⊕ α) → ℝ | (fun z => match z with
        | Sum.inl i => w (some (Sum.inl i))
        | Sum.inr none => w none
        | Sum.inr (some a) => w (some (Sum.inr a))) ∈ A} :=
      (hA.preimage fun z => match z with
        | Sum.inl i => X (some (Sum.inl i))
        | Sum.inr none => X none
        | Sum.inr (some a) => X (some (Sum.inr a))).congr fun w => by
        simp only [Set.mem_ofPred_eq]
        constructor <;> intro h <;> convert h using 1 <;> funext z <;>
          rcases z with i | _ | a <;> simp
    have h2 := ih ι _ (exists_option h1)
    refine h2.congr fun x => ?_
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, t, hyt⟩
      refine ⟨fun o => o.elim t y, ?_⟩
      convert hyt using 1
      funext z
      rcases z with i | _ | a <;> rfl
    · rintro ⟨y, hy⟩
      refine ⟨y ∘ some, y none, ?_⟩
      convert hy using 1
      funext z
      rcases z with i | _ | a <;> rfl

/-- Elimination of finitely many coordinates. -/
theorem exists_sum {ι κ : Type} [Fintype ι] [Fintype κ] {A : Set (ι ⊕ κ → ℝ)} (hA : SAOn A) :
    SAOn {x : ι → ℝ | ∃ y : κ → ℝ, Sum.elim x y ∈ A} :=
  exists_sum_aux κ ι A hA

end SAOn

end NLQCLean
