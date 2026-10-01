/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.ComponentBound
import NLQCLean.Semialgebraic.Fibers

/-!
# Lifted affine slices use one quadratic atom

Arbitrarily many affine equations on selected coordinates are
encoded by one sum of squares. Adding that atom doubles a positive format
budget, with zero-atom descriptions handled before the product estimate.
-/

section

open Set
open scoped BigOperators

namespace NLQCLean

namespace PolynomialSignDNF

def addAtom {n : ℕ} (F : PolynomialSignDNF n) (A : PolynomialSignAtom n) :
    PolynomialSignDNF n := ⟨F.clauses.map (fun L => L ++ [A])⟩

theorem source_addAtom {n : ℕ} (F : PolynomialSignDNF n) (A : PolynomialSignAtom n) :
    (F.addAtom A).source = F.source ∩ {x | A.Holds x} := by
  ext x
  simp only [source, addAtom, List.mem_map, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨L, hL, rfl⟩, hx⟩
    have h := (clauseHolds_append L [A] x).mp hx
    exact ⟨⟨L, hL, h.1⟩, by simpa [clauseHolds] using h.2⟩
  · rintro ⟨⟨L, hL, hx⟩, hA⟩
    exact ⟨L ++ [A], ⟨L, hL, rfl⟩,
      (clauseHolds_append L [A] x).mpr ⟨hx, by simpa [clauseHolds] using hA⟩⟩

theorem maxAtoms_addAtom_le {n : ℕ} (F : PolynomialSignDNF n) (A : PolynomialSignAtom n) :
    (F.addAtom A).maxAtoms ≤ F.maxAtoms + 1 := by
  change (((F.clauses.map (fun L => L ++ [A])).map List.length).foldr max 0) ≤ _
  rw [List.map_map]
  apply List.max_le_of_forall_le
  intro k hk
  obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hk
  simpa using Nat.add_le_add_right (F.length_le_maxAtoms hL) 1

theorem HasFormat.addAtom {n c D E : ℕ} {F : PolynomialSignDNF n}
    (hF : F.HasFormat c D) (hb : 1 ≤ F.maxAtoms) (A : PolynomialSignAtom n)
    (hA : A.polynomial.totalDegree ≤ E) : (F.addAtom A).HasFormat (2 * c) (max D E) := by
  constructor
  · have hmax := F.maxAtoms_addAtom_le A
    have hprod := hF.1
    have hlen : F.clauses.length ≤ F.clauses.length * F.maxAtoms := by nlinarith
    change (F.clauses.map _).length * (F.addAtom A).maxAtoms ≤ _
    rw [List.length_map]
    calc
      _ ≤ F.clauses.length * (F.maxAtoms + 1) := Nat.mul_le_mul_left _ hmax
      _ ≤ _ := by nlinarith
  · change ∀ L ∈ F.clauses.map (fun L => L ++ [A]),
      ∀ B ∈ L, B.polynomial.totalDegree ≤ max D E
    simp only [List.forall_mem_map]
    intro L hL B hB
    rcases List.mem_append.mp hB with hB | hB
    · exact (hF.2 L hL B hB).trans (le_max_left _ _)
    · have hBA := List.mem_singleton.mp hB
      subst B
      exact hA.trans (le_max_right _ _)

end PolynomialSignDNF

theorem HasSemialgebraicFormat.inter_polynomial_zero {n c D E : ℕ}
    {S : Set (RealEuclidean n)} (hS : HasSemialgebraicFormat S c D) (hc : 1 ≤ c)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ E) :
    HasSemialgebraicFormat (S ∩ {x | MvPolynomial.eval (fun i => x i) p = 0})
      (2 * c) (max D E) := by
  obtain ⟨F, rfl, hF⟩ := hS
  by_cases hb : F.maxAtoms = 0
  · by_cases he : F.clauses = []
    · have hs : F.source = ∅ := by simp [PolynomialSignDNF.source, he]
      rw [hs, empty_inter]
      refine ⟨PolynomialSignDNF.empty n, PolynomialSignDNF.source_empty, ?_⟩
      simp [PolynomialSignDNF.HasFormat, PolynomialSignDNF.empty, PolynomialSignDNF.maxAtoms]
    · rw [F.source_eq_univ_of_maxAtoms_eq_zero he hb, univ_inter]
      refine ⟨PolynomialSignDNF.atom ⟨p, .zero⟩, ?_, ?_⟩
      · simp [PolynomialSignAtom.Holds, PolynomialSign.Holds]
      · constructor
        · simp [PolynomialSignDNF.atom, PolynomialSignDNF.maxAtoms]
          omega
        · simpa [PolynomialSignDNF.atom] using hp.trans (le_max_right D E)
  · refine ⟨F.addAtom ⟨p, .zero⟩, ?_, hF.addAtom (by omega) _ hp⟩
    simpa [PolynomialSignAtom.Holds, PolynomialSign.Holds] using F.source_addAtom ⟨p, .zero⟩

noncomputable def affineEquationPolynomial {n a k : ℕ} (I : Fin a → Fin n)
    (M : Fin k → Fin a → ℝ) (b : Fin k → ℝ) (j : Fin k) : MvPolynomial (Fin n) ℝ :=
  (∑ i, MvPolynomial.C (M j i) * MvPolynomial.X (I i)) - MvPolynomial.C (b j)

theorem affineEquationPolynomial_degree_le {n a k : ℕ} (I : Fin a → Fin n)
    (M : Fin k → Fin a → ℝ) (b : Fin k → ℝ) (j : Fin k) :
    (affineEquationPolynomial I M b j).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_sub_C_le _ _).trans
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

noncomputable def affineSlicePolynomial {n a k : ℕ} (I : Fin a → Fin n)
    (M : Fin k → Fin a → ℝ) (b : Fin k → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ j, affineEquationPolynomial I M b j ^ 2

theorem affineSlicePolynomial_degree_le {n a k : ℕ} (I : Fin a → Fin n)
    (M : Fin k → Fin a → ℝ) (b : Fin k → ℝ) :
    (affineSlicePolynomial I M b).totalDegree ≤ 2 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_pow _ 2).trans
    (by have := affineEquationPolynomial_degree_le I M b j; omega)

def affineCoordinateSlice {n a k : ℕ} (I : Fin a → Fin n)
    (M : Fin k → Fin a → ℝ) (b : Fin k → ℝ) : Set (RealEuclidean n) :=
  {x | ∀ j, ∑ i, M j i * x (I i) = b j}

theorem affineCoordinateSlice_eq_zero {n a k : ℕ} (I : Fin a → Fin n)
    (M : Fin k → Fin a → ℝ) (b : Fin k → ℝ) :
    affineCoordinateSlice I M b =
      {x | MvPolynomial.eval (fun i => x i) (affineSlicePolynomial I M b) = 0} := by
  ext x
  simp only [affineCoordinateSlice, mem_ofPred_eq, affineSlicePolynomial, map_sum, map_pow]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)]
  simp [affineEquationPolynomial, sub_eq_zero]

theorem HasSemialgebraicFormat.inter_affineCoordinateSlice {n a k c D : ℕ}
    {S : Set (RealEuclidean n)} (hS : HasSemialgebraicFormat S c D) (hc : 1 ≤ c)
    (I : Fin a → Fin n) (M : Fin k → Fin a → ℝ) (b : Fin k → ℝ) :
    HasSemialgebraicFormat (S ∩ affineCoordinateSlice I M b) (2 * c) (max D 2) := by
  rw [affineCoordinateSlice_eq_zero]
  exact hS.inter_polynomial_zero hc _ (affineSlicePolynomial_degree_le I M b)

theorem HasSemialgebraicFormat.finite_card_connectedComponents_affineSlice
    (hComponents : SemialgebraicComponentBoundTheorem)
    {n a k c D : ℕ} {S : Set (RealEuclidean n)} (hS : HasSemialgebraicFormat S c D)
    (hc : 1 ≤ c) (I : Fin a → Fin n) (M : Fin k → Fin a → ℝ) (b : Fin k → ℝ) :
    Finite (ConnectedComponents ↥(S ∩ affineCoordinateSlice I M b)) ∧
      Nat.card (ConnectedComponents ↥(S ∩ affineCoordinateSlice I M b)) ≤
        componentFormatBase (2 * c) (max D 2) ^ n :=
  (hS.inter_affineCoordinateSlice hc I M b).finite_card_connectedComponents_all_dimensions hComponents

theorem HasSemialgebraicFormat.finite_card_connectedComponents_image_affineSlice
    (hComponents : SemialgebraicComponentBoundTheorem)
    {n a k m c D : ℕ} {S : Set (RealEuclidean n)} (hS : HasSemialgebraicFormat S c D)
    (hc : 1 ≤ c) (I : Fin a → Fin n) (M : Fin k → Fin a → ℝ) (b : Fin k → ℝ)
    {f : RealEuclidean n → RealEuclidean m} (hf : ContinuousOn f S) :
    Finite (ConnectedComponents (f '' (S ∩ affineCoordinateSlice I M b))) ∧
      Nat.card (ConnectedComponents (f '' (S ∩ affineCoordinateSlice I M b))) ≤
        componentFormatBase (2 * c) (max D 2) ^ n := by
  obtain ⟨hfin, hbound⟩ := hS.finite_card_connectedComponents_affineSlice hComponents hc I M b
  obtain ⟨hfin', hbound'⟩ := finite_card_connectedComponents_image (hf.mono inter_subset_left) hfin
  exact ⟨hfin', hbound'.trans hbound⟩

theorem coordinateProjection_image_inter_affineSlice {n a r k : ℕ}
    (S : Set (RealEuclidean n)) (J : Fin a → Fin n) (I : Fin r → Fin a)
    (M : Fin k → Fin r → ℝ) (b : Fin k → ℝ) :
    (coordinateProjection J '' S) ∩ affineCoordinateSlice I M b =
      coordinateProjection J '' (S ∩ affineCoordinateSlice (J ∘ I) M b) := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, hy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hy⟩

theorem HasSemialgebraicFormat.finite_card_connectedComponents_projected_affineSlice
    (hComponents : SemialgebraicComponentBoundTheorem)
    {n a r k c D : ℕ} {S : Set (RealEuclidean n)} (hS : HasSemialgebraicFormat S c D)
    (hc : 1 ≤ c) (J : Fin a → Fin n) (I : Fin r → Fin a)
    (M : Fin k → Fin r → ℝ) (b : Fin k → ℝ) :
    Finite (ConnectedComponents ↥((coordinateProjection J '' S) ∩ affineCoordinateSlice I M b)) ∧
      Nat.card (ConnectedComponents ↥((coordinateProjection J '' S) ∩ affineCoordinateSlice I M b)) ≤
        componentFormatBase (2 * c) (max D 2) ^ n := by
  rw [coordinateProjection_image_inter_affineSlice]
  exact hS.finite_card_connectedComponents_image_affineSlice hComponents hc (J ∘ I) M b
    (continuous_coordinateProjection J).continuousOn

theorem HasSemialgebraicFormat.card_projected_affineSlice_le
    (hComponents : SemialgebraicComponentBoundTheorem)
    {n a r k c D : ℕ} {S : Set (RealEuclidean n)} (hS : HasSemialgebraicFormat S c D)
    (hc : 1 ≤ c) (J : Fin a → Fin n) (I : Fin r → Fin a)
    (M : Fin k → Fin r → ℝ) (b : Fin k → ℝ)
    (hfinite : ((coordinateProjection J '' S) ∩ affineCoordinateSlice I M b).Finite) :
    Nat.card ↥((coordinateProjection J '' S) ∩ affineCoordinateSlice I M b) ≤
      componentFormatBase (2 * c) (max D 2) ^ n := by
  have hbound := (hS.finite_card_connectedComponents_projected_affineSlice hComponents hc J I M b).2
  rw [(finite_card_connectedComponents_of_finite hfinite.to_subtype).2] at hbound
  exact hbound

theorem coordinateFiber_eq_affineSlice {n m : ℕ} (I : Fin m → Fin n) (y : RealEuclidean m) :
    {x | coordinateProjection I x = y} =
      affineCoordinateSlice I (fun j i => if j = i then 1 else 0) (fun j => y j) := by
  ext x
  change coordinateProjection I x = y ↔ ∀ j, ∑ i, (if j = i then (1 : ℝ) else 0) * x (I i) = y j
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  constructor
  · intro h j
    exact congrArg (fun z : RealEuclidean m => z j) h
  · intro h
    ext j
    exact h j

theorem HasSemialgebraicFormat.card_projected_coordinateFiber_le
    (hComponents : SemialgebraicComponentBoundTheorem)
    {n a m c D : ℕ} {S : Set (RealEuclidean n)} (hS : HasSemialgebraicFormat S c D)
    (hc : 1 ≤ c) (J : Fin a → Fin n) (I : Fin m → Fin a) (y : RealEuclidean m)
    (hfinite : (semialgebraicMapFiber (coordinateProjection J '' S) (coordinateProjection I) y).Finite) :
    Nat.card (semialgebraicMapFiber (coordinateProjection J '' S) (coordinateProjection I) y) ≤
      componentFormatBase (2 * c) (max D 2) ^ n := by
  have heq : semialgebraicMapFiber (coordinateProjection J '' S) (coordinateProjection I) y =
      (coordinateProjection J '' S) ∩
        affineCoordinateSlice I (fun j i => if j = i then 1 else 0) (fun j => y j) := by
    rw [← coordinateFiber_eq_affineSlice]
    rfl
  rw [heq] at hfinite ⊢
  exact hS.card_projected_affineSlice_le hComponents hc J I _ _ hfinite

/-- The lifted ambient dimension remains the exponent after projection.
Only the qualitative fiber argument uses projection closure; the numerical
bound is obtained entirely before eliminating any lifted variable. -/
theorem HasSemialgebraicFormat.ae_card_projected_coordinateFiber_le
    (hComponents : SemialgebraicComponentBoundTheorem)
    (hProjection : SemialgebraicProjectionTheorem)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hFiber : SemialgebraicDimensionFiberTheorem)
    {n a m c D : ℕ} {S : Set (RealEuclidean n)} (hS : HasSemialgebraicFormat S c D)
    (hc : 1 ≤ c) (J : Fin a → Fin n) (I : Fin m → Fin a)
    (hd : coordinateInteriorDimension (coordinateProjection J '' S) ≤ m) :
    ∀ᵐ y, (semialgebraicMapFiber (coordinateProjection J '' S) (coordinateProjection I) y).Finite ∧
      Nat.card (semialgebraicMapFiber (coordinateProjection J '' S) (coordinateProjection I) y) ≤
        componentFormatBase (2 * c) (max D 2) ^ n := by
  have hC := (hS.semialgebraic.coordinate_graph J).image hProjection
  filter_upwards [ae_finite_coordinateFiber hStratification hFiber hC I hd] with y hy
  exact ⟨hy, hS.card_projected_coordinateFiber_le hComponents hc J I y hy⟩

end NLQCLean
end
