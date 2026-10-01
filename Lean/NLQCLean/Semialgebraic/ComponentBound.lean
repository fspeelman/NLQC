/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.ConnectedComponents
import NLQCLean.Semialgebraic.FormatParameters
import NLQCLean.External.SemialgebraicTextbook

/-!
# Uniform component bounds from the audited conjunction theorem

Translate signed atoms, bound each conjunction using
`SemialgebraicComponentBoundTheorem`, compare a finite DNF union and absorb fixed-format factors into one
exponential base. No elimination or coefficient restriction is used.
-/

section

open Set
open scoped BigOperators

namespace NLQCLean

noncomputable def PolynomialSignAtom.toSystemAtom {n : ℕ}
    (A : PolynomialSignAtom n) : PolynomialSystemAtom n :=
  match A.sign with
  | .negative => ⟨-A.polynomial, .positive⟩
  | .zero => ⟨A.polynomial, .zero⟩
  | .positive => ⟨A.polynomial, .positive⟩

theorem PolynomialSignAtom.toSystemAtom_holds {n : ℕ} (A : PolynomialSignAtom n)
    (x : RealEuclidean n) :
    A.toSystemAtom.relation.Holds (MvPolynomial.eval (fun i => x i) A.toSystemAtom.polynomial) ↔
      A.Holds x := by
  rcases A with ⟨p, s⟩
  cases s <;> simp [toSystemAtom, PolynomialSystemRelation.Holds, Holds, PolynomialSign.Holds]

theorem PolynomialSignAtom.toSystemAtom_degree_le {n : ℕ} (A : PolynomialSignAtom n) :
    A.toSystemAtom.polynomial.totalDegree ≤ A.polynomial.totalDegree := by
  rcases A with ⟨p, s⟩
  cases s <;> simp [toSystemAtom]

theorem polynomialSystemSource_toSystemAtoms {n : ℕ} (L : List (PolynomialSignAtom n)) :
    polynomialSystemSource (L.map PolynomialSignAtom.toSystemAtom) =
      {x | PolynomialSignDNF.clauseHolds L x} := by
  ext x
  simp only [polynomialSystemSource, PolynomialSignDNF.clauseHolds,
    mem_ofPred_eq, List.forall_mem_map, PolynomialSignAtom.toSystemAtom_holds]

theorem finite_card_connectedComponents_clause
    (hComponents : SemialgebraicComponentBoundTheorem)
    {n c D : ℕ} (hn : 1 ≤ n) (L : List (PolynomialSignAtom n))
    (hc : L.length ≤ c + 1) (hD : ∀ A ∈ L, A.polynomial.totalDegree ≤ D) :
    Finite (ConnectedComponents {x : RealEuclidean n | PolynomialSignDNF.clauseHolds L x}) ∧
      Nat.card (ConnectedComponents {x : RealEuclidean n | PolynomialSignDNF.clauseHolds L x}) ≤
        max D 2 * (2 * max D 2 - 1) ^ (n + c) := by
  have hE : 2 ≤ max D 2 := le_max_right _ _
  have hb : 1 ≤ 2 * max D 2 - 1 := by omega
  by_cases hL : L = []
  · subst L
    have heq : {x : RealEuclidean n | PolynomialSignDNF.clauseHolds [] x} = univ := by
      simp [PolynomialSignDNF.clauseHolds]
    rw [heq]
    have : ConnectedSpace (univ : Set (RealEuclidean n)) :=
      isConnected_iff_connectedSpace.mp isConnected_univ
    have hcard : Nat.card (ConnectedComponents (univ : Set (RealEuclidean n))) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    refine ⟨inferInstance, ?_⟩
    rw [hcard]
    exact one_le_mul (by omega) (one_le_pow₀ hb)
  · have hpos : 1 ≤ L.length := List.length_pos_iff.mpr hL
    obtain ⟨hfin, hbound⟩ := hComponents n (max D 2) hn hE
      (L.map PolynomialSignAtom.toSystemAtom) (by simpa using hpos) (by
        simp only [List.forall_mem_map]
        intro A hA
        exact A.toSystemAtom_degree_le.trans ((hD A hA).trans (le_max_left _ _)))
    rw [polynomialSystemSource_toSystemAtoms] at hfin hbound
    refine ⟨hfin, hbound.trans ?_⟩
    simp only [List.length_map]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (by omega))

theorem PolynomialSignDNF.source_eq_iUnion_clauses {n : ℕ} (F : PolynomialSignDNF n) :
    F.source = ⋃ i : Fin F.clauses.length, {x | clauseHolds (F.clauses.get i) x} := by
  ext x
  simp [source, List.exists_mem_iff_get]

theorem finite_card_connectedComponents_bounded_dnf
    (hComponents : SemialgebraicComponentBoundTheorem)
    {n c D : ℕ} (hn : 1 ≤ n) (F : PolynomialSignDNF n)
    (hr : F.clauses.length ≤ c + 1)
    (hb : ∀ L ∈ F.clauses, L.length ≤ c + 1)
    (hD : ∀ L ∈ F.clauses, ∀ A ∈ L, A.polynomial.totalDegree ≤ D) :
    Finite (ConnectedComponents F.source) ∧ Nat.card (ConnectedComponents F.source) ≤
      (c + 1) * (max D 2 * (2 * max D 2 - 1) ^ (n + c)) := by
  have hclause (i : Fin F.clauses.length) := finite_card_connectedComponents_clause
    hComponents hn (F.clauses.get i) (hb _ (List.get_mem _ _)) (hD _ (List.get_mem _ _))
  obtain ⟨hfin, hbound⟩ := finite_card_connectedComponents_iUnion
    (fun i : Fin F.clauses.length => {x | PolynomialSignDNF.clauseHolds (F.clauses.get i) x})
    (fun i => (hclause i).1)
  rw [← F.source_eq_iUnion_clauses] at hfin hbound
  refine ⟨hfin, hbound.trans ?_⟩
  calc
    _ ≤ ∑ _i : Fin F.clauses.length, max D 2 * (2 * max D 2 - 1) ^ (n + c) :=
      Finset.sum_le_sum fun i _ => (hclause i).2
    _ = F.clauses.length * (max D 2 * (2 * max D 2 - 1) ^ (n + c)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hr

def componentFormatBase (c D : ℕ) : ℕ :=
  ((c + 1) * max D 2) * (2 * max D 2 - 1) ^ (c + 1)

theorem componentFormatBase_pos (c D : ℕ) : 1 ≤ componentFormatBase c D := by
  have hE : 2 ≤ max D 2 := le_max_right _ _
  have hb : 1 ≤ 2 * max D 2 - 1 := by omega
  exact one_le_mul (one_le_mul (by omega) (by omega)) (one_le_pow₀ hb)

theorem componentFormatBase_bound {n c D : ℕ} (hn : 1 ≤ n) :
    (c + 1) * (max D 2 * (2 * max D 2 - 1) ^ (n + c)) ≤ componentFormatBase c D ^ n := by
  have hE : 2 ≤ max D 2 := le_max_right _ _
  have hb : 1 ≤ 2 * max D 2 - 1 := by omega
  have hK : 1 ≤ (c + 1) * max D 2 := one_le_mul (by omega) (by omega)
  have hKpow : (c + 1) * max D 2 ≤ ((c + 1) * max D 2) ^ n := by
    simpa using Nat.pow_le_pow_right hK hn
  have hexp : n + c ≤ (c + 1) * n := by nlinarith
  simpa only [componentFormatBase, mul_pow, ← pow_mul, mul_assoc] using
    Nat.mul_le_mul hKpow (Nat.pow_le_pow_right hb hexp)

theorem HasSemialgebraicFormat.finite_card_connectedComponents
    (hComponents : SemialgebraicComponentBoundTheorem)
    {n c D : ℕ} {S : Set (RealEuclidean n)} (hS : HasSemialgebraicFormat S c D)
    (hn : 1 ≤ n) : Finite (ConnectedComponents S) ∧
      Nat.card (ConnectedComponents S) ≤ componentFormatBase c D ^ n := by
  obtain ⟨F, rfl, hF⟩ := hS
  obtain ⟨G, hG, hr, hb, hD⟩ := hF.exists_bounded_counts
  rw [← hG]
  obtain ⟨hfin, hbound⟩ := finite_card_connectedComponents_bounded_dnf hComponents hn G hr hb hD
  exact ⟨hfin, hbound.trans (componentFormatBase_bound hn)⟩

theorem exists_uniform_component_base
    (hComponents : SemialgebraicComponentBoundTheorem) (c D : ℕ) :
    ∃ β : ℕ, 1 ≤ β ∧ ∀ n : ℕ, 1 ≤ n → ∀ S : Set (RealEuclidean n),
      HasSemialgebraicFormat S c D → Finite (ConnectedComponents S) ∧
        Nat.card (ConnectedComponents S) ≤ β ^ n :=
  ⟨componentFormatBase c D, componentFormatBase_pos c D,
    fun _ hn _ hS => hS.finite_card_connectedComponents hComponents hn⟩

theorem finite_card_connectedComponents_zero_dim (S : Set (RealEuclidean 0)) :
    Finite (ConnectedComponents S) ∧ Nat.card (ConnectedComponents S) ≤ 1 := by
  obtain ⟨hfin, hcard⟩ := finite_card_connectedComponents_of_finite (X := S) inferInstance
  refine ⟨hfin, hcard.le.trans ?_⟩
  simpa using Nat.card_le_card_of_injective (fun _ : S => ())
    (Function.injective_of_subsingleton _)

theorem HasSemialgebraicFormat.finite_card_connectedComponents_all_dimensions
    (hComponents : SemialgebraicComponentBoundTheorem)
    {n c D : ℕ} {S : Set (RealEuclidean n)} (hS : HasSemialgebraicFormat S c D) :
    Finite (ConnectedComponents S) ∧ Nat.card (ConnectedComponents S) ≤ componentFormatBase c D ^ n := by
  by_cases hn : n = 0
  · subst n
    simpa using finite_card_connectedComponents_zero_dim S
  · exact hS.finite_card_connectedComponents hComponents (by omega)

end NLQCLean
end
