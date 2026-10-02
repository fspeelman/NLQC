/-
Derived from sundogcert (https://github.com/humiliati/sundogcert) at commit
c5c8d2b21cc118a2f1be1138b9800a991b57e084, licensed under Apache-2.0
(see NLQCLean/Vendor/Sundog/LICENSE).
Modified for NLQCLean: rational coefficient restrictions and closure proofs;
the resolution map and all specialization semantics are unchanged.
-/

import NLQCLean.Semialgebraic.RationalSignDiagrams
import NLQCLean.Vendor.Sundog.DiagramBranches

/-!
# Rational descriptions of resolution fibers

The branch conditions only inspect leading coefficients of successive
truncations. Rational inputs therefore give rational parameter conditions.
-/

namespace NLQCLean.RationalQE

open Polynomial Sundog.TarskiQE

variable {n : ℕ}

private theorem sadef_resolve_fiber_zero (t : Polynomial (MvPolynomial (Fin n) ℝ)) :
    SADef n {g : Fin n → ℝ | resolve g 0 = t} := by
  have he : ∀ g : Fin n → ℝ,
      resolve g (0 : Polynomial (MvPolynomial (Fin n) ℝ)) = 0 :=
    fun g => (resolve_eq_self_iff g 0).mpr (Or.inl rfl)
  by_cases ht : (0 : Polynomial (MvPolynomial (Fin n) ℝ)) = t
  · subst ht
    have e : {g : Fin n → ℝ | resolve g 0 = 0} = Set.univ :=
      Set.ext fun g => by simp [he g]
    rw [e]
    exact SADef.univ
  · have e : {g : Fin n → ℝ | resolve g 0 = t} = ∅ :=
      Set.ext fun g => by simp [he g, ht]
    rw [e]
    exact SADef.empty

/-- The fiber of the resolution map is semialgebraic in the parameters. -/
theorem sadef_resolve_fiber (q t : Polynomial (MvPolynomial (Fin n) ℝ))
    (hrat : q ∈ polynomialSubring (rationalPolynomialSubring (Fin n))) :
    SADef n {g : Fin n → ℝ | resolve g q = t} := by
  suffices H : ∀ (N : ℕ) (q : Polynomial (MvPolynomial (Fin n) ℝ)),
      q.support.card ≤ N → q ∈ polynomialSubring (rationalPolynomialSubring (Fin n)) →
      SADef n {g : Fin n → ℝ | resolve g q = t} from
    H q.support.card q le_rfl hrat
  intro N
  induction N with
  | zero =>
    intro q hq hrat
    have h0 : q = 0 :=
      Polynomial.support_eq_empty.mp (Finset.card_eq_zero.mp (by omega))
    subst h0
    exact sadef_resolve_fiber_zero t
  | succ N ih =>
    intro q hq hrat
    by_cases hq0 : q = 0
    · subst hq0
      exact sadef_resolve_fiber_zero t
    · have e : {g : Fin n → ℝ | resolve g q = t}
          = ({g | MvPolynomial.eval g q.leadingCoeff = 0}
              ∩ {g | resolve g q.eraseLead = t})
            ∪ ({g | MvPolynomial.eval g q.leadingCoeff = 0}ᶜ
              ∩ (if q = t then Set.univ else ∅)) := by
        ext g
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
          Set.mem_compl_iff]
        by_cases hl : MvPolynomial.eval g q.leadingCoeff = 0
        · rw [resolve_of_lead_vanish g hq0 hl]
          simp [hl]
        · rw [(resolve_eq_self_iff g q).mpr (Or.inr hl)]
          by_cases hqt : q = t
          · exact iff_of_true hqt
              (Or.inr ⟨hl, by rw [ite_eq_left hqt]; exact Set.mem_univ g⟩)
          · refine iff_of_false hqt ?_
            rintro (⟨h1, -⟩ | ⟨-, h2⟩)
            · exact hl h1
            · rw [ite_eq_right hqt] at h2
              simp at h2
      rw [e]
      refine ((SADef.zero _ (polynomialSubring.leadingCoeff_mem hrat)).inter
        (ih q.eraseLead ?_ (polynomialSubring.eraseLead_mem hrat))).union
        (((SADef.zero _ (polynomialSubring.leadingCoeff_mem hrat)).compl).inter ?_)
      · have := Polynomial.eraseLead_support_card_lt hq0
        omega
      · by_cases hqt : q = t
        · rw [ite_eq_left hqt]
          exact SADef.univ
        · rw [ite_eq_right hqt]
          exact SADef.empty

/-- A family's resolve-cell is SADef. -/
theorem sadef_resolve_cell (F T : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (hrat : RationalFamily F) :
    SADef n {g : Fin n → ℝ | List.Forall₂ (fun q t => resolve g q = t) F T} := by
  revert hrat
  induction F generalizing T with
  | nil =>
    intro hrat
    match T with
    | [] =>
      have e : {g : Fin n → ℝ |
          List.Forall₂ (fun q t => resolve g q = t) [] []} = Set.univ :=
        Set.ext fun g => by simp
      rw [e]
      exact SADef.univ
    | t :: T =>
      have e : {g : Fin n → ℝ |
          List.Forall₂ (fun q t => resolve g q = t) [] (t :: T)} = ∅ :=
        Set.ext fun g => by simp
      rw [e]
      exact SADef.empty
  | cons q F ih =>
    intro hrat
    match T with
    | [] =>
      have e : {g : Fin n → ℝ |
          List.Forall₂ (fun q t => resolve g q = t) (q :: F) []} = ∅ :=
        Set.ext fun g => by simp
      rw [e]
      exact SADef.empty
    | t :: T =>
      have e : {g : Fin n → ℝ |
          List.Forall₂ (fun q' t' => resolve g q' = t') (q :: F) (t :: T)}
          = {g | resolve g q = t}
            ∩ {g | List.Forall₂ (fun q' t' => resolve g q' = t') F T} :=
        Set.ext fun g => by simp [List.forall₂_cons]
      rw [e]
      exact (sadef_resolve_fiber q t (hrat q List.mem_cons_self)).inter
        (ih T fun p hp => hrat p (List.mem_cons_of_mem _ hp))

end NLQCLean.RationalQE
