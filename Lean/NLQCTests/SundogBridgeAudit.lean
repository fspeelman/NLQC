/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NLQCLean.Semialgebraic.SundogBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Audit of the bridge to Sundog's semialgebraic sets

The expanded statements of the bridge are displayed, followed by examples in
dimension zero, for the zero polynomial, for a nonlinear strict inequality,
and for the coordinate identity on sets whose projection is computed by hand.
The last example checks that Sundog's projection theorem, with its exact
implicit-argument signature, instantiates the reduction.
-/

section

open Sundog.TarskiQE

namespace NLQCLean.SundogBridgeAudit

#check @semialgebraic_iff_sadef
#check @toLp_preimage_image_coordinateProjection_castAdd
#check @semialgebraicProjectionTheorem_of_sadef_projection
#check @PolynomialSignAtom.sadef_setOf_holds
#check @PolynomialSignDNF.sadef_setOf_clauseHolds
#check @PolynomialSignDNF.sadef_toLp_preimage_source
#check @Semialgebraic.ofLp_preimage_of_sadef

/-! The three main statements, pinned in fully explicit form. -/

example : ∀ {n : ℕ} (S : Set (RealEuclidean n)),
    Semialgebraic S ↔ SADef n ((WithLp.toLp 2 : (Fin n → ℝ) → RealEuclidean n) ⁻¹' S) :=
  @semialgebraic_iff_sadef

example : ∀ {n : ℕ} (A : Set (RealEuclidean (n + 1))),
    (WithLp.toLp 2 : (Fin n → ℝ) → RealEuclidean n) ⁻¹'
        (coordinateProjection (Fin.castAdd 1) '' A) =
      {g : Fin n → ℝ | ∃ y : ℝ, Fin.snoc g y ∈
        (WithLp.toLp 2 : (Fin (n + 1) → ℝ) → RealEuclidean (n + 1)) ⁻¹' A} :=
  @toLp_preimage_image_coordinateProjection_castAdd

example : (∀ (n : ℕ) (A : Set (Fin (n + 1) → ℝ)), SADef (n + 1) A →
      SADef n {g : Fin n → ℝ | ∃ y : ℝ, Fin.snoc g y ∈ A}) →
    SemialgebraicProjectionTheorem :=
  @semialgebraicProjectionTheorem_of_sadef_projection

/-! ### Dimension zero -/

example : SADef 0 ((WithLp.toLp 2) ⁻¹' (Set.univ : Set (RealEuclidean 0))) :=
  (semialgebraic_iff_sadef _).mp Semialgebraic.univ

example : SADef 0 ((WithLp.toLp 2) ⁻¹' (∅ : Set (RealEuclidean 0))) :=
  (semialgebraic_iff_sadef _).mp Semialgebraic.empty

example : Semialgebraic (Set.univ : Set (RealEuclidean 0)) :=
  (semialgebraic_iff_sadef _).mpr (by simpa using (SADef.univ : SADef 0 Set.univ))

example : Semialgebraic (∅ : Set (RealEuclidean 0)) :=
  (semialgebraic_iff_sadef _).mpr (by simpa using (SADef.empty : SADef 0 ∅))

/-- Projecting a nonempty subset of the real line to `RealEuclidean 0` gives
the one-point space; `Fin.snoc` on `Fin 0` is exercised. -/
example :
    (WithLp.toLp 2 : (Fin 0 → ℝ) → RealEuclidean 0) ⁻¹'
        (coordinateProjection (Fin.castAdd 1) '' {x : RealEuclidean 1 | 0 < x 0}) =
      Set.univ := by
  rw [toLp_preimage_image_coordinateProjection_castAdd]
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  refine ⟨1, ?_⟩
  change (0 : ℝ) < (Fin.snoc g 1 : Fin 1 → ℝ) (Fin.last 0)
  rw [Fin.snoc_last]
  exact one_pos

/-- Projecting an empty subset of the real line to `RealEuclidean 0` gives the
empty set. -/
example :
    (WithLp.toLp 2 : (Fin 0 → ℝ) → RealEuclidean 0) ⁻¹'
        (coordinateProjection (Fin.castAdd 1) ''
          {x : RealEuclidean 1 | x 0 ^ 2 + 1 = 0}) = ∅ := by
  rw [toLp_preimage_image_coordinateProjection_castAdd]
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    not_exists]
  intro y hy
  change (Fin.snoc g y : Fin 1 → ℝ) (Fin.last 0) ^ 2 + 1 = 0 at hy
  rw [Fin.snoc_last] at hy
  nlinarith [sq_nonneg y]

/-! ### The zero polynomial -/

/-- A zero-sign atom of the zero polynomial holds everywhere, and its
coordinate set is Sundog-definable. -/
example : SADef 2 ((WithLp.toLp 2) ⁻¹'
    (PolynomialSignDNF.atom ⟨(0 : MvPolynomial (Fin 2) ℝ), .zero⟩).source) :=
  (semialgebraic_iff_sadef _).mp ⟨_, rfl⟩

example : (PolynomialSignDNF.atom ⟨(0 : MvPolynomial (Fin 2) ℝ), .zero⟩).source =
    Set.univ := by
  ext x
  simp [PolynomialSignAtom.Holds, PolynomialSign.Holds]

/-- Strict signs of the zero polynomial hold nowhere. -/
example : (PolynomialSignDNF.atom ⟨(0 : MvPolynomial (Fin 2) ℝ), .positive⟩).source = ∅ := by
  ext x
  simp [PolynomialSignAtom.Holds, PolynomialSign.Holds]

example : SADef 2 {g : Fin 2 → ℝ |
    PolynomialSignAtom.Holds ⟨(0 : MvPolynomial (Fin 2) ℝ), .negative⟩ (WithLp.toLp 2 g)} :=
  PolynomialSignAtom.sadef_setOf_holds _

/-! ### A nonlinear strict inequality -/

/-- The region above the parabola is semialgebraic, obtained from Sundog's
positive atom for `X 1 - X 0 ^ 2` through the reverse direction. -/
example : Semialgebraic {x : RealEuclidean 2 | x 0 ^ 2 < x 1} := by
  rw [semialgebraic_iff_sadef]
  have e : (WithLp.toLp 2 : (Fin 2 → ℝ) → RealEuclidean 2) ⁻¹'
      {x : RealEuclidean 2 | x 0 ^ 2 < x 1} =
        {g : Fin 2 → ℝ | 0 < MvPolynomial.eval g
          (MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 2) ℝ)} := by
    ext g
    simp
  rw [e]
  exact SADef.pos _

/-- The same set in the forward direction, from an explicit NLQC description. -/
example : SADef 2 ((WithLp.toLp 2) ⁻¹' {x : RealEuclidean 2 | x 0 ^ 2 < x 1}) := by
  refine (semialgebraic_iff_sadef _).mp
    ⟨PolynomialSignDNF.atom
      ⟨(MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 2) ℝ), .positive⟩, ?_⟩
  ext x
  simp [PolynomialSignAtom.Holds, PolynomialSign.Holds]

/-! ### The coordinate identity on a nonlinear set -/

/-- Eliminating the last coordinate of `{x | x 1 ^ 2 = x 0}` leaves the
nonnegative half-line in the first coordinate. Eliminating the first
coordinate instead would give the whole line, so this checks the indexing. -/
example :
    (WithLp.toLp 2 : (Fin 1 → ℝ) → RealEuclidean 1) ⁻¹'
        (coordinateProjection (Fin.castAdd 1) '' {x : RealEuclidean 2 | x 1 ^ 2 = x 0}) =
      {g : Fin 1 → ℝ | 0 ≤ g 0} := by
  rw [toLp_preimage_image_coordinateProjection_castAdd]
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  have hlast (y : ℝ) : (Fin.snoc g y : Fin 2 → ℝ) 1 = y := Fin.snoc_last (α := fun _ => ℝ) _ _
  have hfirst (y : ℝ) : (Fin.snoc g y : Fin 2 → ℝ) 0 = g 0 :=
    Fin.snoc_castSucc (α := fun _ => ℝ) (i := 0) _ _
  constructor
  · rintro ⟨y, hy⟩
    change (Fin.snoc g y : Fin 2 → ℝ) 1 ^ 2 = (Fin.snoc g y : Fin 2 → ℝ) 0 at hy
    rw [hlast, hfirst] at hy
    rw [← hy]
    exact sq_nonneg y
  · intro hg
    refine ⟨Real.sqrt (g 0), ?_⟩
    change (Fin.snoc g (Real.sqrt (g 0)) : Fin 2 → ℝ) 1 ^ 2 =
      (Fin.snoc g (Real.sqrt (g 0)) : Fin 2 → ℝ) 0
    rw [hlast, hfirst, Real.sq_sqrt hg]

/-! ### Instantiation by Sundog's projection theorem -/

/-- Sundog's `sadef_proj` has implicit dimension and set arguments. A
hypothesis of exactly that shape instantiates the reduction. -/
example
    (sadef_proj : ∀ {n : ℕ} {A : Set (Fin (n + 1) → ℝ)}, SADef (n + 1) A →
      SADef n {g : Fin n → ℝ | ∃ y : ℝ, Fin.snoc g y ∈ A}) :
    SemialgebraicProjectionTheorem :=
  semialgebraicProjectionTheorem_of_sadef_projection (fun _ _ hA => sadef_proj hA)

/-! ### Axioms -/

/--
info: 'NLQCLean.semialgebraic_iff_sadef' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms semialgebraic_iff_sadef

/--
info: 'NLQCLean.toLp_preimage_image_coordinateProjection_castAdd' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toLp_preimage_image_coordinateProjection_castAdd

/--
info: 'NLQCLean.semialgebraicProjectionTheorem_of_sadef_projection' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms semialgebraicProjectionTheorem_of_sadef_projection

end NLQCLean.SundogBridgeAudit
end
