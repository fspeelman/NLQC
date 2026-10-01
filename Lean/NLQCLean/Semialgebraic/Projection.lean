/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.External.SemialgebraicTextbook

/-!
# Coordinate elimination and polynomial images

Only the ordinary one-coordinate projection proposition is supplied.
Repeated projection, explicit polynomial graphs and image closure are proved.
The finite-description measurability interface has no external premise.
-/

section

namespace NLQCLean

theorem PolynomialSignAtom.measurableSet_holds {n : ℕ} (A : PolynomialSignAtom n) :
    MeasurableSet {x : RealEuclidean n | A.Holds x} := by
  have hc : Continuous (fun x : RealEuclidean n => MvPolynomial.eval (fun i => x i) A.polynomial) :=
    A.polynomial.continuous_eval.comp (by fun_prop)
  rcases A with ⟨p, s⟩
  cases s
  · exact (isOpen_lt hc continuous_const).measurableSet
  · exact (isClosed_eq hc continuous_const).measurableSet
  · exact (isOpen_lt continuous_const hc).measurableSet

theorem PolynomialSignDNF.measurableSet_source {n : ℕ} (F : PolynomialSignDNF n) :
    MeasurableSet F.source := by
  have heq : F.source = ⋃ i : Fin F.clauses.length,
      ⋂ j : Fin (F.clauses.get i).length, {x | ((F.clauses.get i).get j).Holds x} := by
    ext x
    simp only [source, clauseHolds, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter,
      List.exists_mem_iff_get, List.forall_mem_iff_get]
  rw [heq]
  exact MeasurableSet.iUnion (fun i => MeasurableSet.iInter (fun j =>
    ((F.clauses.get i).get j).measurableSet_holds))

theorem Semialgebraic.measurableSet {n : ℕ} {S : Set (RealEuclidean n)}
    (hS : Semialgebraic S) : MeasurableSet S := by
  obtain ⟨F, rfl⟩ := hS
  exact F.measurableSet_source

theorem Semialgebraic.polynomial_zero {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Semialgebraic {x : RealEuclidean n | MvPolynomial.eval (fun i => x i) p = 0} := by
  refine ⟨PolynomialSignDNF.atom ⟨p, .zero⟩, ?_⟩
  simp [PolynomialSignAtom.Holds, PolynomialSign.Holds]

theorem Semialgebraic.finset_iInter {n : ℕ} {ι : Type*} (s : Finset ι)
    (S : ι → Set (RealEuclidean n)) (hS : ∀ i ∈ s, Semialgebraic (S i)) :
    Semialgebraic (⋂ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Semialgebraic.univ (n := n))
  | @insert i s hi ih =>
    have h1 := hS i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
    convert h1.inter h2 using 1
    ext x
    simp

theorem Semialgebraic.iInter {n : ℕ} {ι : Type*} [Fintype ι]
    (S : ι → Set (RealEuclidean n)) (hS : ∀ i, Semialgebraic (S i)) :
    Semialgebraic (⋂ i, S i) := by
  simpa using Semialgebraic.finset_iInter Finset.univ S (fun i _ => hS i)

@[simp] theorem coordinateProjection_pair_left {n m : ℕ}
    (x : RealEuclidean n) (y : RealEuclidean m) :
    coordinateProjection (Fin.castAdd m) (euclideanPair x y) = x := by
  ext j
  simp

@[simp] theorem coordinateProjection_pair_right {n m : ℕ}
    (x : RealEuclidean n) (y : RealEuclidean m) :
    coordinateProjection (Fin.natAdd n) (euclideanPair x y) = y := by
  ext j
  simp

theorem Semialgebraic.first_projection (hProjection : SemialgebraicProjectionTheorem)
    {n m : ℕ} {S : Set (RealEuclidean (n + m))} (hS : Semialgebraic S) :
    Semialgebraic (coordinateProjection (Fin.castAdd m) '' S) := by
  induction m with
  | zero =>
    simpa only [show coordinateProjection (Fin.castAdd 0 : Fin n → Fin (n + 0)) = id from rfl,
      Set.image_id] using hS
  | succ m ih =>
    have hs := hProjection (n + m) S hS
    have h := ih hs
    convert h using 1
    rw [Set.image_image]
    rfl

theorem Semialgebraic.last_projection (hProjection : SemialgebraicProjectionTheorem)
    {n m : ℕ} {S : Set (RealEuclidean (n + m))} (hS : Semialgebraic S) :
    Semialgebraic (coordinateProjection (Fin.natAdd n) '' S) := by
  have hflip := hS.coordinate_equiv_image (finAddFlip : Fin (m + n) ≃ Fin (n + m))
  have h := hflip.first_projection hProjection
  convert h using 1
  rw [Set.image_image]
  congr 1
  funext x
  ext j
  simp

/-- The graph of a polynomial map restricted to a semialgebraic source is
given by source constraints and the output polynomial equations. -/
theorem Semialgebraic.polynomial_graph {n m : ℕ} {S : Set (RealEuclidean n)}
    (hS : Semialgebraic S) (q : Fin m → MvPolynomial (Fin n) ℝ) :
    SemialgebraicMapOn S (PolynomialSignDNF.polynomialMap q) := by
  have h := (hS.coordinate_preimage (Fin.castAdd m)).inter
    (Semialgebraic.iInter (fun j : Fin m => {z : RealEuclidean (n + m) |
      MvPolynomial.eval (fun k => z k)
        (MvPolynomial.rename (Fin.castAdd m) (q j) - MvPolynomial.X (Fin.natAdd n j)) = 0})
      (fun j => Semialgebraic.polynomial_zero _))
  unfold SemialgebraicMapOn
  convert h using 1
  ext z
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq,
    MvPolynomial.eval_sub, MvPolynomial.eval_rename, MvPolynomial.eval_X, sub_eq_zero]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨by simpa using hx, ?_⟩
    intro j
    simp [Function.comp_def, PolynomialSignDNF.polynomialMap]
  · rintro ⟨hz, hq⟩
    refine ⟨coordinateProjection (Fin.castAdd m) z, hz, ?_⟩
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simpa only [euclideanPair_right, PolynomialSignDNF.polynomialMap,
        coordinateProjection_apply, Function.comp_def] using hq j

theorem Semialgebraic.polynomial_image (hProjection : SemialgebraicProjectionTheorem)
    {n m : ℕ} {S : Set (RealEuclidean n)} (hS : Semialgebraic S)
    (q : Fin m → MvPolynomial (Fin n) ℝ) :
    Semialgebraic (PolynomialSignDNF.polynomialMap q '' S) := by
  have h := (hS.polynomial_graph q).last_projection hProjection
  simpa only [Set.image_image, Function.comp_def, coordinateProjection_pair_right] using h

end NLQCLean
end
