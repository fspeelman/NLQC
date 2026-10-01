/-
Derived from sundogcert (https://github.com/humiliati/sundogcert) at commit
c5c8d2b21cc118a2f1be1138b9800a991b57e084, licensed under Apache-2.0
(see NLQCLean/Vendor/Sundog/LICENSE).
Modified for NLQCLean: rational coefficient restrictions and closure proofs;
uses the original real sign-diagram semantics without changing them.
-/

import NLQCLean.Semialgebraic.RationalCoefficients
import NLQCLean.Vendor.Sundog.SignDiagrams

/-!
# Rational polynomial sign descriptions and diagram partitions

This is the coefficient-preserving version of Sundog's Boolean parameter-set
bookkeeping. The meaning of a sign diagram is the original `Realizes` predicate.
-/

namespace NLQCLean.RationalQE

open Polynomial Sundog.TarskiQE

variable {n : ℕ}

/-- Quantifier-free semialgebraic subsets of the parameter space. -/
inductive SADef (n : ℕ) : Set (Fin n → ℝ) → Prop
  | pos (f : MvPolynomial (Fin n) ℝ) (hf : f ∈ rationalPolynomialSubring (Fin n)) : SADef n {g | 0 < MvPolynomial.eval g f}
  | compl {s : Set (Fin n → ℝ)} : SADef n s → SADef n sᶜ
  | union {s t : Set (Fin n → ℝ)} : SADef n s → SADef n t → SADef n (s ∪ t)

namespace SADef

theorem inter {s t : Set (Fin n → ℝ)} (hs : SADef n s) (ht : SADef n t) :
    SADef n (s ∩ t) := by
  have h := (hs.compl.union ht.compl).compl
  rwa [Set.compl_union, compl_compl, compl_compl] at h

theorem empty : SADef n (∅ : Set (Fin n → ℝ)) := by
  have h := SADef.pos (n := n) 0 (rationalPolynomialSubring _).zero_mem
  have e : {g : Fin n → ℝ | 0 < MvPolynomial.eval g 0} = ∅ := by
    ext g
    simp
  rwa [e] at h

theorem univ : SADef n (Set.univ : Set (Fin n → ℝ)) := by
  have h := (empty (n := n)).compl
  rwa [Set.compl_empty] at h

theorem neg (f : MvPolynomial (Fin n) ℝ) (hf : f ∈ rationalPolynomialSubring (Fin n)) :
    SADef n {g | MvPolynomial.eval g f < 0} := by
  have h := SADef.pos (-f) ((rationalPolynomialSubring _).neg_mem hf)
  have e : {g : Fin n → ℝ | 0 < MvPolynomial.eval g (-f)}
      = {g | MvPolynomial.eval g f < 0} := by
    ext g
    simp
  rwa [e] at h

theorem zero (f : MvPolynomial (Fin n) ℝ) (hf : f ∈ rationalPolynomialSubring (Fin n)) :
    SADef n {g | MvPolynomial.eval g f = 0} := by
  have h := ((SADef.pos f hf).union (neg f hf)).compl
  have e : ({g : Fin n → ℝ | 0 < MvPolynomial.eval g f}
      ∪ {g | MvPolynomial.eval g f < 0})ᶜ = {g | MvPolynomial.eval g f = 0} := by
    ext g
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt]
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 h2
    · intro h
      rw [h]
      exact ⟨le_refl 0, le_refl 0⟩
  rwa [e] at h

/-- The sign-condition atom. -/
theorem signEq (f : MvPolynomial (Fin n) ℝ) (hf : f ∈ rationalPolynomialSubring (Fin n)) (s : SignType) :
    SADef n {g | SignType.sign (MvPolynomial.eval g f) = s} := by
  cases s
  · have e : {g : Fin n → ℝ | SignType.sign (MvPolynomial.eval g f) = SignType.zero}
        = {g | MvPolynomial.eval g f = 0} := by
      ext g
      simp [sign_eq_zero_iff]
    rw [e]
    exact zero f hf
  · have e : {g : Fin n → ℝ | SignType.sign (MvPolynomial.eval g f) = SignType.neg}
        = {g | MvPolynomial.eval g f < 0} := by
      ext g
      simp [sign_eq_neg_one_iff]
    rw [e]
    exact neg f hf
  · have e : {g : Fin n → ℝ | SignType.sign (MvPolynomial.eval g f) = SignType.pos}
        = {g | 0 < MvPolynomial.eval g f} := by
      ext g
      simp [sign_eq_one_iff]
    rw [e]
    exact SADef.pos f hf

theorem list_biUnion {α : Type*} {l : List α} {f : α → Set (Fin n → ℝ)}
    (h : ∀ a ∈ l, SADef n (f a)) : SADef n (⋃ a ∈ l, f a) := by
  induction l with
  | nil =>
    have e : (⋃ a ∈ ([] : List α), f a) = (∅ : Set (Fin n → ℝ)) := by
      simp
    rw [e]
    exact empty
  | cons a l ih =>
    have e : (⋃ x ∈ (a :: l), f x) = f a ∪ ⋃ x ∈ l, f x := by
      ext g
      simp [List.mem_cons]
    rw [e]
    exact (h a List.mem_cons_self).union (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

end SADef


/-- Forgetting coefficient restrictions gives the checked real description. -/
theorem SADef.to_real {s : Set (Fin n → ℝ)} (hs : SADef n s) :
    Sundog.TarskiQE.SADef n s := by
  induction hs with
  | pos f _ => exact Sundog.TarskiQE.SADef.pos f
  | compl _ ih => exact ih.compl
  | union _ _ ihs iht => exact ihs.union iht

/-- Every member of the parametric family has rational polynomial coefficients. -/
def RationalFamily (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) : Prop :=
  ∀ P ∈ F, P ∈ polynomialSubring (rationalPolynomialSubring (Fin n))

/-- **THE PARAMETRIC SIGN-DIAGRAM STATEMENT** (to be proven for every family by the
Cohen–Hörmander induction, 2d-2/2d-3): finitely many semialgebraic branches, each carrying
one diagram valid across the whole branch. -/
def DiagramPartition (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) : Prop :=
  ∃ branches : List (Set (Fin n → ℝ) × List (List SignType)),
    (∀ b ∈ branches, SADef n b.1 ∧ ∀ g ∈ b.1, Realizes g F b.2) ∧
    (∀ g : Fin n → ℝ, ∃ b ∈ branches, g ∈ b.1)

/-- **The elimination, given the summit**: the existential sign set is the finite union of
the branches whose diagram contains the queried column. -/
theorem elim_of_diagramPartition {F : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (h : DiagramPartition F) (σ : List SignType) :
    SADef n {g | ∃ y : ℝ, signVec F g y = σ} := by
  classical
  obtain ⟨branches, hbr, hcover⟩ := h
  have he : {g | ∃ y : ℝ, signVec F g y = σ}
      = ⋃ b ∈ branches.filter (fun b => σ ∈ b.2), b.1 := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨b, hbmem, hbg⟩ := hcover g
      refine ⟨b, ⟨hbmem, ?_⟩, hbg⟩
      exact (realizes_exists_iff ((hbr b hbmem).2 g hbg) σ).mp ⟨y, hy⟩
    · rintro ⟨b, ⟨hbmem, hbσ⟩, hbg⟩
      exact (realizes_exists_iff ((hbr b hbmem).2 g hbg) σ).mpr hbσ
  rw [he]
  exact SADef.list_biUnion fun b hb =>
    (hbr b (List.mem_of_mem_filter hb)).1

private theorem SADef_mapSign (l : List (MvPolynomial (Fin n) ℝ))
    (hl : ∀ p ∈ l, p ∈ rationalPolynomialSubring (Fin n)) (τ : List SignType) :
    SADef n {g | l.map (fun c => SignType.sign (MvPolynomial.eval g c)) = τ} := by
  revert hl
  induction l generalizing τ with
  | nil =>
    intro hl
    cases τ with
    | nil =>
      have e : {g : Fin n → ℝ | ([] : List (MvPolynomial (Fin n) ℝ)).map
          (fun c => SignType.sign (MvPolynomial.eval g c)) = []} = Set.univ := by
        ext g
        simp
      rw [e]
      exact SADef.univ
    | cons t ts =>
      have e : {g : Fin n → ℝ | ([] : List (MvPolynomial (Fin n) ℝ)).map
          (fun c => SignType.sign (MvPolynomial.eval g c)) = t :: ts} = ∅ := by
        ext g
        simp
      rw [e]
      exact SADef.empty
  | cons c cs ih =>
    intro hl
    cases τ with
    | nil =>
      have e : {g : Fin n → ℝ | (c :: cs).map
          (fun c => SignType.sign (MvPolynomial.eval g c)) = []} = ∅ := by
        ext g
        simp
      rw [e]
      exact SADef.empty
    | cons t ts =>
      have e : {g : Fin n → ℝ | (c :: cs).map
          (fun c => SignType.sign (MvPolynomial.eval g c)) = t :: ts}
          = {g | SignType.sign (MvPolynomial.eval g c) = t}
            ∩ {g | cs.map (fun c => SignType.sign (MvPolynomial.eval g c)) = ts} := by
        ext g
        simp
      rw [e]
      exact (SADef.signEq c (hl c List.mem_cons_self) t).inter
        (ih ts fun p hp => hl p (List.mem_cons_of_mem _ hp))

/-- **The base case: a constant family has a diagram partition.** -/
theorem diagramPartition_of_constants (F : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (hF : ∀ P ∈ F, P.natDegree = 0) (hrat : RationalFamily F) : DiagramPartition F := by
  classical
  refine ⟨(allSignVecs F.length).map fun τ =>
    ({g | F.map (fun P => SignType.sign (MvPolynomial.eval g (P.coeff 0))) = τ}, [τ]),
    ?_, ?_⟩
  · rintro b hb
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hb
    constructor
    · have e : {g : Fin n → ℝ | F.map
          (fun P => SignType.sign (MvPolynomial.eval g (P.coeff 0))) = τ}
          = {g | (F.map (fun P => P.coeff 0)).map
              (fun c => SignType.sign (MvPolynomial.eval g c)) = τ} := by
        ext g
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, List.map_map]
        rfl
      rw [e]
      apply SADef_mapSign _ _ τ
      intro p hp
      obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hp
      exact polynomialSubring.coeff_mem (hrat P hP) 0
    · intro g hg
      refine ⟨[], List.Pairwise.nil, ?_, ?_⟩
      · intro P hP h0 y hy
        exfalso
        apply h0
        have hC := Polynomial.eq_C_of_natDegree_eq_zero (hF P hP)
        rw [hC] at hy ⊢
        rw [spec, Polynomial.map_C] at hy ⊢
        have hc0 : MvPolynomial.eval g (P.coeff 0) = 0 := by
          have h' := hy
          simp only [Polynomial.IsRoot, Polynomial.eval_C] at h'
          exact h'
        rw [hc0, Polynomial.C_0]
      · change ∀ y : ℝ, (∀ l ∈ (none : Option ℝ), l < y) → signVec F g y = τ
        intro y _
        rw [← hg, signVec]
        refine List.map_congr_left fun P hP => ?_
        have hC := Polynomial.eq_C_of_natDegree_eq_zero (hF P hP)
        conv_lhs => rw [hC, spec, Polynomial.map_C, Polynomial.eval_C]
  · intro g
    exact ⟨({g' | F.map (fun P => SignType.sign (MvPolynomial.eval g' (P.coeff 0)))
        = F.map fun P => SignType.sign (MvPolynomial.eval g (P.coeff 0))},
        [F.map fun P => SignType.sign (MvPolynomial.eval g (P.coeff 0))]),
      List.mem_map.mpr ⟨_, mem_allSignVecs (by simp), rfl⟩, rfl⟩

end NLQCLean.RationalQE
