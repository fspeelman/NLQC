import NLQCLean.Semialgebraic.Lojasiewicz

/-!
# Stability for maxima of polynomial families

Fix a compact semialgebraic domain `D ⊆ ℝ^τ`, finitely many compact semialgebraic sets
`P s ⊆ ℝ^{κ s}` and real polynomials `N s (x, c)`. The value
`M(x) = max {N s (x, c) : s, c ∈ P s}` is continuous with semialgebraic graph. If `M ≤ 1`
on `D` and `E = {x ∈ D : M x = 1}` is nonempty, the Łojasiewicz inequality gives
`dist(x, E)^{2N} ≤ C (1 - M x)` for all `x ∈ D`.
-/

noncomputable section

namespace NLQCLean

open Set MvPolynomial

/-- The maximum of a continuous family over a finite union of compact sets is continuous. -/
theorem continuous_sSup_iUnion_image {γ S : Type*} [TopologicalSpace γ] [Finite S]
    {β : S → Type*} [∀ s, TopologicalSpace (β s)] {P : ∀ s, Set (β s)}
    (hP : ∀ s, IsCompact (P s)) {φ : ∀ s, γ → β s → ℝ} (hφ : ∀ s, Continuous ↿(φ s)) :
    Continuous fun x => sSup (⋃ s, φ s x '' P s) := by
  let P' : Set (Σ s, β s) := ⋃ s, Sigma.mk s '' P s
  have hP' : IsCompact P' := isCompact_iUnion fun s => (hP s).image continuous_sigmaMk
  let Φ : γ → (Σ s, β s) → ℝ := fun x z => φ z.1 x z.2
  have hset : ∀ x, (⋃ s, φ s x '' P s) = Φ x '' P' := by
    intro x
    ext v
    simp only [mem_iUnion, mem_image, P', Φ]
    constructor
    · rintro ⟨s, c, hc, rfl⟩
      exact ⟨⟨s, c⟩, ⟨s, c, hc, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, c, hc, rfl⟩, rfl⟩
      exact ⟨s, c, hc, rfl⟩
  have hΦ : Continuous ↿Φ := by
    let e := (Homeomorph.prodComm γ (Σ s, β s)).trans (Homeomorph.sigmaProdDistrib (X := β))
    have hF : Continuous fun w : Σ s, β s × γ => φ w.1 w.2.2 w.2.1 :=
      continuous_sigma fun s => (hφ s).comp continuous_swap
    have : ↿Φ = (fun w : Σ s, β s × γ => φ w.1 w.2.2 w.2.1) ∘ e := by
      funext ⟨x, ⟨s, c⟩⟩
      rfl
    rw [this]
    exact hF.comp e.continuous
  simp_rw [hset]
  exact hP'.continuous_sSup hΦ

section PolynomialFamily

variable {τ S : Type} [Fintype τ] [Fintype S] {κ : S → Type} [∀ s, Fintype (κ s)]

/-- The value of the polynomial family at a target point. -/
def familyValues (P : ∀ s, Set (κ s → ℝ)) (N : ∀ s, MvPolynomial (τ ⊕ κ s) ℝ)
    (x : τ → ℝ) : Set ℝ :=
  ⋃ s, (fun c => eval (Sum.elim x c) (N s)) '' P s

/-- The maximum of the polynomial family. -/
def familyMax (P : ∀ s, Set (κ s → ℝ)) (N : ∀ s, MvPolynomial (τ ⊕ κ s) ℝ)
    (x : τ → ℝ) : ℝ :=
  sSup (familyValues P N x)

variable {P : ∀ s, Set (κ s → ℝ)} {N : ∀ s, MvPolynomial (τ ⊕ κ s) ℝ}

omit [Fintype τ] [Fintype S] [∀ s, Fintype (κ s)] in
theorem continuous_eval_sumElim (p : MvPolynomial (τ ⊕ κ s) ℝ) :
    Continuous ↿(fun (x : τ → ℝ) (c : κ s → ℝ) => eval (Sum.elim x c) p) := by
  refine (MvPolynomial.continuous_eval p).comp (continuous_pi fun i => ?_)
  rcases i with i | j
  · exact (continuous_apply i).comp continuous_fst
  · exact (continuous_apply j).comp continuous_snd

omit [Fintype τ] [Fintype S] [∀ s, Fintype (κ s)] in
theorem continuous_eval_sumElim_right (p : MvPolynomial (τ ⊕ κ s) ℝ) (x : τ → ℝ) :
    Continuous fun c : κ s → ℝ => eval (Sum.elim x c) p := by
  refine (MvPolynomial.continuous_eval p).comp (continuous_pi fun i => ?_)
  rcases i with i | j
  · exact continuous_const
  · exact continuous_apply j

omit [Fintype τ] [∀ s, Fintype (κ s)] in
theorem continuous_familyMax (hP : ∀ s, IsCompact (P s)) : Continuous (familyMax P N) :=
  continuous_sSup_iUnion_image hP fun s => continuous_eval_sumElim (N s)

omit [Fintype τ] [∀ s, Fintype (κ s)] in
theorem isGreatest_familyMax (hP : ∀ s, IsCompact (P s)) (hne : ∃ s, (P s).Nonempty)
    (x : τ → ℝ) : IsGreatest (familyValues P N x) (familyMax P N x) := by
  have hc : IsCompact (familyValues P N x) :=
    isCompact_iUnion fun s => (hP s).image (continuous_eval_sumElim_right (N s) x)
  obtain ⟨s, c, hc'⟩ := hne
  have hne' : (familyValues P N x).Nonempty := ⟨_, mem_iUnion.mpr ⟨s, c, hc', rfl⟩⟩
  exact ⟨hc.sSup_mem hne', fun v hv => le_csSup hc.bddAbove hv⟩

omit [Fintype τ] [Fintype S] [∀ s, Fintype (κ s)] in
private theorem eval_rename_mapSome (w : Option τ ⊕ κ s → ℝ) (p : MvPolynomial (τ ⊕ κ s) ℝ) :
    eval w (rename (Sum.map some id) p) =
      eval (Sum.elim (fun i => w (Sum.inl (some i))) fun j => w (Sum.inr j)) p := by
  have h : (w ∘ Sum.map some id) =
      Sum.elim (fun i => w (Sum.inl (some i))) fun j => w (Sum.inr j) := by
    funext i
    rcases i with i | j <;> rfl
  rw [eval_rename, h]

omit [Fintype S] in
/-- Points where some family value equals, or some value exceeds, `1 - y`. -/
private theorem saOn_exists_value (hPsa : ∀ s, SAOn (P s)) (s : S) (strict : Bool) :
    SAOn {z : Option τ → ℝ | ∃ c ∈ P s,
      if strict then 1 - z none < eval (Sum.elim ((fun i => z (some i))) c) (N s)
      else eval (Sum.elim ((fun i => z (some i))) c) (N s) = 1 - z none} := by
  classical
  have hPc := (hPsa s).comap (Sum.inr : κ s → Option τ ⊕ κ s)
  have hcmp : SAOn {w : Option τ ⊕ κ s → ℝ |
      if strict then eval w (1 - X (Sum.inl none)) < eval w (rename (Sum.map some id) (N s))
      else eval w (rename (Sum.map some id) (N s)) = eval w (1 - X (Sum.inl none))} := by
    cases strict
    · exact (SAOn.eq (rename (Sum.map some id) (N s)) (1 - X (Sum.inl none))).congr
        fun w => by simp
    · exact (SAOn.lt (1 - X (Sum.inl none)) (rename (Sum.map some id) (N s))).congr
        fun w => by simp
  refine (SAOn.exists_sum (hPc.inter hcmp)).congr fun z => ?_
  simp only [mem_inter_iff, mem_ofPred_eq, Function.comp_def, eval_rename_mapSome,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨c, hc, hv⟩
    exact ⟨c, hc, by cases strict <;> simpa using hv⟩
  · rintro ⟨c, hc, hv⟩
    exact ⟨c, hc, by cases strict <;> simpa using hv⟩

/-- The graph of `1 - M` over `D` is semialgebraic. -/
theorem saOn_graph_one_sub_familyMax {D : Set (τ → ℝ)} (hDsa : SAOn D)
    (hP : ∀ s, IsCompact (P s)) (hPsa : ∀ s, SAOn (P s)) (hne : ∃ s, (P s).Nonempty) :
    SAOn {z : Option τ → ℝ | (fun i => z (some i)) ∈ D ∧
      z none = 1 - familyMax P N (fun i => z (some i))} := by
  classical
  have hD := hDsa.comap (some : τ → Option τ)
  have hEx := SAOn.fintype_iUnion fun s => saOn_exists_value (N := N) hPsa s false
  have hUp := SAOn.fintype_iInter fun s => (saOn_exists_value (N := N) hPsa s true).compl
  refine ((hD.inter hEx).inter hUp).congr fun z => ?_
  set x : τ → ℝ := fun i => z (some i) with hx
  have hG := isGreatest_familyMax (N := N) hP hne x
  simp only [mem_inter_iff, mem_iUnion, mem_iInter, mem_compl_iff, mem_ofPred_eq,
    Function.comp_def, Bool.false_eq_true, ite_false, ite_true, not_exists, not_and, not_lt]
  constructor
  · rintro ⟨⟨hzD, s, c, hc, hv⟩, hup⟩
    refine ⟨hzD, ?_⟩
    have hmem : 1 - z none ∈ familyValues P N x := mem_iUnion.mpr ⟨s, c, hc, hv⟩
    have hupper : 1 - z none ∈ upperBounds (familyValues P N x) := by
      rintro v hv'
      obtain ⟨s', c', hc', rfl⟩ := mem_iUnion.mp hv'
      exact hup s' c' hc'
    have := hG.unique ⟨hmem, hupper⟩
    linarith
  · rintro ⟨hzD, hz⟩
    have hval : 1 - z none = familyMax P N x := by linarith
    have hmem : 1 - z none ∈ familyValues P N x := hval ▸ hG.1
    obtain ⟨s, c, hc, hv⟩ := mem_iUnion.mp hmem
    refine ⟨⟨hzD, s, c, hc, hv⟩, fun s' c' hc' => ?_⟩
    rw [hval]
    exact hG.2 (mem_iUnion.mpr ⟨s', c', hc', rfl⟩)

/-- **Stability of polynomial maxima.** If `M ≤ 1` on a compact semialgebraic domain and the
level set `E = {M = 1}` is nonempty, then every `x ∈ D` has a point `e ∈ E` with
`|x - e|^{2n} ≤ C (1 - M x)`. -/
theorem exists_stability_of_familyMax {D : Set (τ → ℝ)} (hDc : IsCompact D) (hDsa : SAOn D)
    (hP : ∀ s, IsCompact (P s)) (hPsa : ∀ s, SAOn (P s)) (hne : ∃ s, (P s).Nonempty)
    (hle : ∀ x ∈ D, familyMax P N x ≤ 1) (hE : ∃ x ∈ D, familyMax P N x = 1) :
    ∃ C > 0, ∃ n : ℕ, 0 < n ∧ ∀ x ∈ D, ∃ e ∈ D, familyMax P N e = 1 ∧
      (∑ i, (x i - e i) ^ 2) ^ n ≤ C * (1 - familyMax P N x) := by
  classical
  set M := familyMax P N with hMdef
  have hMc : Continuous M := continuous_familyMax hP
  set E := {x | x ∈ D ∧ M x = 1} with hEdef
  have hEc : IsCompact E :=
    hDc.of_isClosed_subset (hDc.isClosed.inter (isClosed_eq hMc continuous_const))
      fun x hx => hx.1
  obtain ⟨x₀, hx₀D, hx₀⟩ := hE
  have hEne : E.Nonempty := ⟨x₀, hx₀D, hx₀⟩
  let dist2 : (τ → ℝ) → (τ → ℝ) → ℝ := fun x e => ∑ i, (x i - e i) ^ 2
  have hd2 : Continuous ↿dist2 :=
    continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp continuous_fst).sub
        ((continuous_apply i).comp continuous_snd)).pow 2
  have hd2r : ∀ x, Continuous (dist2 x) := fun x =>
    continuous_finsetSum _ fun i _ => (continuous_const.sub (continuous_apply i)).pow 2
  have hbdd : ∀ x, BddBelow (dist2 x '' E) := fun x =>
    ⟨0, by rintro _ ⟨_, _, rfl⟩; exact Finset.sum_nonneg fun i _ => sq_nonneg _⟩
  let G : (τ → ℝ) → ℝ := fun x => sInf (dist2 x '' E)
  have hGc : Continuous G := hEc.continuous_sInf hd2
  have hGmin : ∀ x, ∃ e ∈ E, dist2 x e = G x := by
    intro x
    obtain ⟨e, he, hmin⟩ := hEc.exists_isMinOn hEne (hd2r x).continuousOn
    refine ⟨e, he, ?_⟩
    have hleast : IsLeast (dist2 x '' E) (dist2 x e) :=
      ⟨⟨e, he, rfl⟩, by rintro _ ⟨e', he', rfl⟩; exact hmin he'⟩
    exact hleast.csInf_eq.symm
  have hGnonneg : ∀ x, 0 ≤ G x := by
    intro x
    obtain ⟨e, -, he⟩ := hGmin x
    rw [← he]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  -- semialgebraic graphs
  have hfgraph := saOn_graph_one_sub_familyMax (N := N) hDsa hP hPsa hne
  have hEsa : SAOn E := by
    have h := SAOn.exists_option (hfgraph.inter (SAOn.zero (X none)))
    refine h.congr fun x => ?_
    simp only [mem_inter_iff, mem_ofPred_eq, eval_X, Option.elim]
    constructor
    · rintro ⟨y, ⟨hxD, hy⟩, hy0⟩
      refine ⟨hxD, ?_⟩
      rw [hy0] at hy
      linarith
    · rintro ⟨hxD, hx1⟩
      refine ⟨0, ⟨hxD, ?_⟩, rfl⟩
      change (0 : ℝ) = 1 - M x
      rw [hx1]
      ring
  have hGgraph : SAOn {z : Option τ → ℝ | (fun i => z (some i)) ∈ D ∧
      z none = G (fun i => z (some i))} := by
    let dpoly : MvPolynomial (Option τ ⊕ τ) ℝ :=
      ∑ i, (X (Sum.inl (some i)) - X (Sum.inr i)) ^ 2
    have heval : ∀ w : Option τ ⊕ τ → ℝ, eval w dpoly =
        dist2 (fun i => w (Sum.inl (some i))) (fun i => w (Sum.inr i)) := by
      intro w
      simp [dpoly, dist2]
    have hEw := hEsa.comap (Sum.inr : τ → Option τ ⊕ τ)
    have hA := SAOn.exists_sum (hEw.inter (SAOn.eq dpoly (X (Sum.inl none))))
    have hB := SAOn.exists_sum (hEw.inter (SAOn.lt dpoly (X (Sum.inl none))))
    refine (((hDsa.comap (some : τ → Option τ)).inter hA).inter hB.compl).congr fun z => ?_
    simp only [mem_inter_iff, mem_compl_iff, mem_ofPred_eq, Function.comp_def, heval, eval_X,
      Sum.elim_inl, Sum.elim_inr, not_exists, not_and, not_lt]
    obtain ⟨e₀, he₀, he₀G⟩ := hGmin (fun i => z (some i))
    constructor
    · rintro ⟨⟨hzD, e, he, hv⟩, hup⟩
      refine ⟨hzD, le_antisymm ?_ ?_⟩
      · rw [← he₀G]
        exact hup e₀ he₀
      · rw [← hv]
        exact csInf_le (hbdd _) ⟨e, he, rfl⟩
    · rintro ⟨hzD, hz⟩
      refine ⟨⟨hzD, e₀, he₀, by rw [he₀G, hz]⟩, fun e he => ?_⟩
      rw [hz]
      exact csInf_le (hbdd _) ⟨e, he, rfl⟩
  obtain ⟨C, hC, n, hn, hloj⟩ := lojasiewicz_inequality hDc
    (f := fun x => 1 - M x) (g := G) (continuous_const.sub hMc).continuousOn
    hGc.continuousOn hfgraph hGgraph
    (fun x hx => by have := hle x hx; show 0 ≤ 1 - M x; linarith)
    (fun x hx h0 => by
      have h0' : 1 - M x = 0 := h0
      have hxE : x ∈ E := ⟨hx, by linarith⟩
      refine le_antisymm ?_ (hGnonneg x)
      calc G x ≤ dist2 x x := csInf_le (hbdd x) ⟨x, hxE, rfl⟩
        _ = 0 := by simp [dist2])
  refine ⟨C, hC, n, hn, fun x hx => ?_⟩
  obtain ⟨e, ⟨heD, he1⟩, heG⟩ := hGmin x
  refine ⟨e, heD, he1, ?_⟩
  have := hloj x hx
  rw [abs_of_nonneg (hGnonneg x), ← heG] at this
  exact this

end PolynomialFamily

end NLQCLean
