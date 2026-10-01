/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Vendor.Sundog.SignDiagrams
import NLQCLean.Semialgebraic.CoordinateMaps
import NLQCLean.External.SemialgebraicTextbook

/-!
# Finite sign descriptions and Sundog's semialgebraic sets

`Semialgebraic` asks for an explicit finite disjunction of finite conjunctions
of signed real polynomial atoms on `RealEuclidean n`. Sundog's `SADef n` is the
smallest family of subsets of `Fin n → ℝ` containing every strict positivity
set `{g | 0 < eval g f}` and closed under complement and binary union. Both use
arbitrary real coefficients, and neither restricts the dimension.

The two notions agree after transport along the Euclidean coordinate
isomorphism `WithLp.toLp 2 : (Fin n → ℝ) → RealEuclidean n`:

* a negative atom is Sundog's `neg`, a zero atom is `zero`, a positive atom is
  `pos`; this is valid for the zero polynomial as well;
* a clause is a finite intersection, with the empty clause giving `univ`;
* a description is a finite union, with the empty description giving `∅`;
* conversely, `SADef` is closed under the three generating operations inside
  `Semialgebraic`.

Selecting the first `n` of `n + 1` Euclidean coordinates corresponds exactly
to Sundog's existential elimination of the last coordinate through
`Fin.snoc`. Hence any proof of Sundog's projection statement proves the
unchanged `SemialgebraicProjectionTheorem`.
-/

section

namespace NLQCLean

open Sundog.TarskiQE

namespace PolynomialSignAtom

variable {n : ℕ}

/-- The coordinate set of one signed atom is quantifier-free semialgebraic in
Sundog's sense. The nonzero signs are strict inequalities, and the zero
polynomial is allowed. -/
theorem sadef_setOf_holds (A : PolynomialSignAtom n) :
    SADef n {g : Fin n → ℝ | A.Holds (WithLp.toLp 2 g)} := by
  rcases A with ⟨p, s⟩
  cases s
  · change SADef n {g : Fin n → ℝ | MvPolynomial.eval g p < 0}
    exact SADef.neg p
  · change SADef n {g : Fin n → ℝ | MvPolynomial.eval g p = 0}
    exact SADef.zero p
  · change SADef n {g : Fin n → ℝ | 0 < MvPolynomial.eval g p}
    exact SADef.pos p

end PolynomialSignAtom

namespace PolynomialSignDNF

variable {n : ℕ}

/-- A finite conjunction of atoms is a finite Sundog intersection; the empty
conjunction is the whole space. -/
theorem sadef_setOf_clauseHolds (L : List (PolynomialSignAtom n)) :
    SADef n {g : Fin n → ℝ | clauseHolds L (WithLp.toLp 2 g)} := by
  induction L with
  | nil =>
    have e : {g : Fin n → ℝ | clauseHolds [] (WithLp.toLp 2 g)} = Set.univ := by
      ext g
      simp
    rw [e]
    exact SADef.univ
  | cons A L ih =>
    have e : {g : Fin n → ℝ | clauseHolds (A :: L) (WithLp.toLp 2 g)} =
        {g : Fin n → ℝ | A.Holds (WithLp.toLp 2 g)} ∩
          {g : Fin n → ℝ | clauseHolds L (WithLp.toLp 2 g)} := by
      ext g
      simp
    rw [e]
    exact A.sadef_setOf_holds.inter ih

/-- The coordinate set of a finite sign description is a finite Sundog union;
the empty description is the empty set. -/
theorem sadef_toLp_preimage_source (F : PolynomialSignDNF n) :
    SADef n ((WithLp.toLp 2 : (Fin n → ℝ) → RealEuclidean n) ⁻¹' F.source) := by
  rcases F with ⟨Ls⟩
  induction Ls with
  | nil =>
    have e : (WithLp.toLp 2 : (Fin n → ℝ) → RealEuclidean n) ⁻¹'
        (PolynomialSignDNF.mk []).source = ∅ := by
      ext g
      simp [source]
    rw [e]
    exact SADef.empty
  | cons L Ls ih =>
    have e : (WithLp.toLp 2 : (Fin n → ℝ) → RealEuclidean n) ⁻¹'
        (PolynomialSignDNF.mk (L :: Ls)).source =
          {g : Fin n → ℝ | clauseHolds L (WithLp.toLp 2 g)} ∪
            (WithLp.toLp 2 : (Fin n → ℝ) → RealEuclidean n) ⁻¹'
              (PolynomialSignDNF.mk Ls).source := by
      ext g
      simp [source]
    rw [e]
    exact (sadef_setOf_clauseHolds L).union ih

end PolynomialSignDNF

namespace Semialgebraic

variable {n : ℕ}

/-- Every Sundog quantifier-free set, viewed in Euclidean coordinates, has a
finite sign description. -/
theorem ofLp_preimage_of_sadef {s : Set (Fin n → ℝ)} (hs : SADef n s) :
    Semialgebraic ((WithLp.ofLp : RealEuclidean n → (Fin n → ℝ)) ⁻¹' s) := by
  induction hs with
  | pos f =>
    refine ⟨PolynomialSignDNF.atom ⟨f, .positive⟩, ?_⟩
    ext x
    simp [PolynomialSignAtom.Holds, PolynomialSign.Holds]
  | compl _ ih =>
    rw [Set.preimage_compl]
    exact ih.compl
  | union _ _ ihs iht =>
    rw [Set.preimage_union]
    exact ihs.union iht

end Semialgebraic

/-- Finite polynomial sign descriptions on `RealEuclidean n` are exactly
Sundog's quantifier-free semialgebraic sets, transported along the coordinate
isomorphism. Coefficients are arbitrary reals and every dimension, including
zero, is covered. -/
theorem semialgebraic_iff_sadef {n : ℕ} (S : Set (RealEuclidean n)) :
    Semialgebraic S ↔ SADef n ((WithLp.toLp 2) ⁻¹' S) := by
  constructor
  · rintro ⟨F, rfl⟩
    exact PolynomialSignDNF.sadef_toLp_preimage_source F
  · intro h
    have e : (WithLp.ofLp : RealEuclidean n → (Fin n → ℝ)) ⁻¹'
        ((WithLp.toLp 2 : (Fin n → ℝ) → RealEuclidean n) ⁻¹' S) = S := by
      ext x
      simp
    rw [← e]
    exact Semialgebraic.ofLp_preimage_of_sadef h

/-- Projection onto the first `n` Euclidean coordinates is Sundog's
elimination of the last coordinate. `Fin.castAdd 1` selects the coordinates
`0, …, n - 1` of `Fin (n + 1)`, which are exactly the positions `Fin.castSucc`
filled by `g` in `Fin.snoc g y`; the eliminated value `y` sits at
`Fin.last n`. -/
theorem toLp_preimage_image_coordinateProjection_castAdd {n : ℕ}
    (A : Set (RealEuclidean (n + 1))) :
    (WithLp.toLp 2 : (Fin n → ℝ) → RealEuclidean n) ⁻¹'
        (coordinateProjection (Fin.castAdd 1) '' A) =
      {g : Fin n → ℝ | ∃ y : ℝ, Fin.snoc g y ∈
        (WithLp.toLp 2 : (Fin (n + 1) → ℝ) → RealEuclidean (n + 1)) ⁻¹' A} := by
  -- The selected indices are the `castSucc` positions of `Fin.snoc`.
  have hindex (j : Fin n) : (Fin.castAdd 1 j : Fin (n + 1)) = j.castSucc := rfl
  ext g
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, hxg⟩
    refine ⟨x (Fin.last n), ?_⟩
    have hsnoc : (Fin.snoc g (x (Fin.last n)) : Fin (n + 1) → ℝ) = WithLp.ofLp x := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]
      · rw [Fin.snoc_castSucc]
        have hj := congrArg (fun z : RealEuclidean n => z j) hxg
        rw [coordinateProjection_apply, hindex, PiLp.toLp_apply] at hj
        exact hj.symm
    rw [hsnoc, WithLp.toLp_ofLp]
    exact hx
  · rintro ⟨y, hy⟩
    refine ⟨_, hy, ?_⟩
    ext j
    rw [coordinateProjection_apply, hindex, PiLp.toLp_apply, PiLp.toLp_apply,
      Fin.snoc_castSucc]

/-- Sundog's elimination of one real variable, stated for every dimension,
implies the Euclidean coordinate-projection theorem. -/
theorem semialgebraicProjectionTheorem_of_sadef_projection
    (hproj : ∀ (n : ℕ) (A : Set (Fin (n + 1) → ℝ)), SADef (n + 1) A →
      SADef n {g : Fin n → ℝ | ∃ y : ℝ, Fin.snoc g y ∈ A}) :
    SemialgebraicProjectionTheorem := by
  intro n A hA
  rw [semialgebraic_iff_sadef, toLp_preimage_image_coordinateProjection_castAdd]
  exact hproj n _ ((semialgebraic_iff_sadef A).mp hA)

end NLQCLean
end
