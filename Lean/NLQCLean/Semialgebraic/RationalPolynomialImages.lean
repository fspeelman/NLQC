/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.RationalImages

/-!
# Rational polynomial graphs and images

Finite Boolean operations, coordinate reorderings, polynomial graphs and
polynomial images preserve rational sign descriptions. Polynomial maps are
either supplied over `ℚ`, or supplied over `ℝ` with explicit coefficient-range
membership for each coordinate. All coordinate elimination uses the proved
rational projection theorem.
-/

namespace NLQCLean

/-- Every polynomial obtained by extending rational coefficients belongs
to the rational polynomial subring. -/
theorem rationalPolynomialSubring_map {σ : Type*} (p : MvPolynomial σ ℚ) :
    MvPolynomial.map (algebraMap ℚ ℝ) p ∈ rationalPolynomialSubring σ :=
  ⟨p, rfl⟩

/-- Coordinate variables have rational coefficients. -/
theorem rationalPolynomialSubring_X {σ : Type*} (i : σ) :
    (MvPolynomial.X i : MvPolynomial σ ℝ) ∈ rationalPolynomialSubring σ := by
  exact ⟨MvPolynomial.X i, by simp⟩

/-- Rational semialgebraicity of a map on a source means rational
semialgebraicity of its graph. No behavior off the source is required. -/
def RationalSemialgebraicMapOn {n m : ℕ} (S : Set (RealEuclidean n))
    (f : RealEuclidean n → RealEuclidean m) : Prop :=
  RationalSemialgebraic ((fun x => euclideanPair x (f x)) '' S)

namespace RationalSemialgebraic

theorem empty {n : ℕ} : RationalSemialgebraic (∅ : Set (RealEuclidean n)) := by
  simpa only [RationalSemialgebraic, Set.preimage_empty] using
    (RationalQE.SADef.empty (n := n))

theorem univ {n : ℕ} : RationalSemialgebraic (Set.univ : Set (RealEuclidean n)) := by
  simpa only [RationalSemialgebraic, Set.preimage_univ] using
    (RationalQE.SADef.univ (n := n))

theorem compl {n : ℕ} {S : Set (RealEuclidean n)} (hS : RationalSemialgebraic S) :
    RationalSemialgebraic Sᶜ := by
  simpa only [RationalSemialgebraic, Set.preimage_compl] using
    (RationalQE.SADef.compl hS)

theorem union {n : ℕ} {S T : Set (RealEuclidean n)}
    (hS : RationalSemialgebraic S) (hT : RationalSemialgebraic T) :
    RationalSemialgebraic (S ∪ T) := by
  simpa only [RationalSemialgebraic, Set.preimage_union] using
    (RationalQE.SADef.union hS hT)

theorem inter {n : ℕ} {S T : Set (RealEuclidean n)}
    (hS : RationalSemialgebraic S) (hT : RationalSemialgebraic T) :
    RationalSemialgebraic (S ∩ T) := by
  simpa only [RationalSemialgebraic, Set.preimage_inter] using
    (RationalQE.SADef.inter hS hT)

theorem diff {n : ℕ} {S T : Set (RealEuclidean n)}
    (hS : RationalSemialgebraic S) (hT : RationalSemialgebraic T) :
    RationalSemialgebraic (S \ T) :=
  hS.inter hT.compl

theorem finset_iInter {n : ℕ} {ι : Type*} (s : Finset ι)
    (S : ι → Set (RealEuclidean n)) (hS : ∀ i ∈ s, RationalSemialgebraic (S i)) :
    RationalSemialgebraic (⋂ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (RationalSemialgebraic.univ (n := n))
  | @insert i s hi ih =>
    have h1 := hS i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
    convert h1.inter h2 using 1
    ext x
    simp

theorem iInter {n : ℕ} {ι : Type*} [Fintype ι]
    (S : ι → Set (RealEuclidean n)) (hS : ∀ i, RationalSemialgebraic (S i)) :
    RationalSemialgebraic (⋂ i, S i) := by
  simpa using RationalSemialgebraic.finset_iInter Finset.univ S (fun i _ => hS i)

theorem finset_iUnion {n : ℕ} {ι : Type*} (s : Finset ι)
    (S : ι → Set (RealEuclidean n)) (hS : ∀ i ∈ s, RationalSemialgebraic (S i)) :
    RationalSemialgebraic (⋃ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (RationalSemialgebraic.empty (n := n))
  | @insert i s hi ih =>
    have h1 := hS i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
    convert h1.union h2 using 1
    ext x
    simp

theorem iUnion {n : ℕ} {ι : Type*} [Fintype ι]
    (S : ι → Set (RealEuclidean n)) (hS : ∀ i, RationalSemialgebraic (S i)) :
    RationalSemialgebraic (⋃ i, S i) := by
  simpa using RationalSemialgebraic.finset_iUnion Finset.univ S (fun i _ => hS i)

theorem polynomial_positive {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p ∈ rationalPolynomialSubring (Fin n)) :
    RationalSemialgebraic {x : RealEuclidean n |
      0 < MvPolynomial.eval (fun i => x i) p} := by
  exact RationalQE.SADef.pos p hp

theorem polynomial_negative {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p ∈ rationalPolynomialSubring (Fin n)) :
    RationalSemialgebraic {x : RealEuclidean n |
      MvPolynomial.eval (fun i => x i) p < 0} := by
  exact RationalQE.SADef.neg p hp

theorem polynomial_zero {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p ∈ rationalPolynomialSubring (Fin n)) :
    RationalSemialgebraic {x : RealEuclidean n |
      MvPolynomial.eval (fun i => x i) p = 0} := by
  exact RationalQE.SADef.zero p hp

/-- A zero set specified directly over the rationals. -/
theorem polynomial_zero_rat {n : ℕ} (p : MvPolynomial (Fin n) ℚ) :
    RationalSemialgebraic {x : RealEuclidean n |
      MvPolynomial.eval (fun i => x i) (MvPolynomial.map (algebraMap ℚ ℝ) p) = 0} :=
  polynomial_zero _ (rationalPolynomialSubring_map p)

/-- Image under an invertible coordinate reordering, using the inverse
coordinate pullback. This also covers reorderings between equal dimensions
presented by different natural-number expressions. -/
theorem coordinate_equiv_image {n k : ℕ} {S : Set (RealEuclidean k)}
    (hS : RationalSemialgebraic S) (e : Fin n ≃ Fin k) :
    RationalSemialgebraic (coordinateProjection e '' S) := by
  convert hS.coordinate_preimage e.symm using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [coordinateProjection, WithLp.toLp_ofLp, Function.comp_def] using hx
  · intro hy
    refine ⟨coordinateProjection e.symm y, hy, ?_⟩
    ext j
    simp

/-- Eliminate any finite leading coordinate block, after a rational
coordinate reordering. -/
theorem last_projection {n m : ℕ} {S : Set (RealEuclidean (n + m))}
    (hS : RationalSemialgebraic S) :
    RationalSemialgebraic (coordinateProjection (Fin.natAdd n) '' S) := by
  have hflip := hS.coordinate_equiv_image (finAddFlip : Fin (m + n) ≃ Fin (n + m))
  have h := hflip.first_projection
  convert h using 1
  rw [Set.image_image]
  congr 1
  funext x
  ext j
  simp

/-- Polynomial graph equations use only rational coefficients when the
source and all output polynomials have rational descriptions. -/
theorem polynomial_graph {n m : ℕ} {S : Set (RealEuclidean n)}
    (hS : RationalSemialgebraic S) (q : Fin m → MvPolynomial (Fin n) ℝ)
    (hq : ∀ j, q j ∈ rationalPolynomialSubring (Fin n)) :
    RationalSemialgebraicMapOn S (PolynomialSignDNF.polynomialMap q) := by
  have h := (hS.coordinate_preimage (Fin.castAdd m)).inter
    (RationalSemialgebraic.iInter (fun j : Fin m => {z : RealEuclidean (n + m) |
      MvPolynomial.eval (fun k => z k)
        (MvPolynomial.rename (Fin.castAdd m) (q j) - MvPolynomial.X (Fin.natAdd n j)) = 0})
      (fun j => RationalSemialgebraic.polynomial_zero _
        ((rationalPolynomialSubring _).sub_mem
          (rationalPolynomialSubring_rename (hq j) (Fin.castAdd m))
          (rationalPolynomialSubring_X (Fin.natAdd n j)))))
  unfold RationalSemialgebraicMapOn
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

/-- Images under polynomial maps preserve rational descriptions. No
projection assumption is an input. -/
theorem polynomial_image {n m : ℕ} {S : Set (RealEuclidean n)}
    (hS : RationalSemialgebraic S) (q : Fin m → MvPolynomial (Fin n) ℝ)
    (hq : ∀ j, q j ∈ rationalPolynomialSubring (Fin n)) :
    RationalSemialgebraic (PolynomialSignDNF.polynomialMap q '' S) := by
  have h := (hS.polynomial_graph q hq).last_projection
  simpa only [Set.image_image, Function.comp_def, coordinateProjection_pair_right] using h

/-- Polynomial graph closure with output polynomials given over `ℚ`. -/
theorem polynomial_graph_rat {n m : ℕ} {S : Set (RealEuclidean n)}
    (hS : RationalSemialgebraic S) (q : Fin m → MvPolynomial (Fin n) ℚ) :
    RationalSemialgebraicMapOn S (PolynomialSignDNF.polynomialMap
      (fun j => MvPolynomial.map (algebraMap ℚ ℝ) (q j))) :=
  hS.polynomial_graph _ (fun j => rationalPolynomialSubring_map (q j))

/-- Polynomial image closure with output polynomials given over `ℚ`. -/
theorem polynomial_image_rat {n m : ℕ} {S : Set (RealEuclidean n)}
    (hS : RationalSemialgebraic S) (q : Fin m → MvPolynomial (Fin n) ℚ) :
    RationalSemialgebraic (PolynomialSignDNF.polynomialMap
      (fun j => MvPolynomial.map (algebraMap ℚ ℝ) (q j)) '' S) :=
  hS.polynomial_image _ (fun j => rationalPolynomialSubring_map (q j))

end RationalSemialgebraic
end NLQCLean
