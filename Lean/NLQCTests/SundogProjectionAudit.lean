/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Vendor.Sundog.SemialgebraicProjection

/-!
# Audit of the vendored Sundog projection theorem

The vendored `Sundog.TarskiQE.sadef_proj` eliminates the last coordinate of a set in
the Boolean closure `Sundog.TarskiQE.SADef` of strict polynomial inequalities with
arbitrary real coefficients. The checks below freeze its full type, the types of the
sign characterization and the one-variable sign-vector elimination it uses, and the
axioms of all three. The guarded messages fail the build if a type or axiom list
changes.
-/

namespace NLQCTests

/-- The projection theorem at the reference type, with all binders explicit. -/
example {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} (hA : Sundog.TarskiQE.SADef (n + 1) A) :
    Sundog.TarskiQE.SADef n {g : Fin n → ℝ | ∃ y : ℝ, Fin.snoc g y ∈ A} :=
  Sundog.TarskiQE.sadef_proj hA

/--
info: inductive Sundog.TarskiQE.SADef : (n : ℕ) → Set (Fin n → ℝ) → Prop
number of parameters: 1
constructors:
Sundog.TarskiQE.SADef.pos : ∀ {n : ℕ} (f : MvPolynomial (Fin n) ℝ),
  Sundog.TarskiQE.SADef n {g | 0 < (MvPolynomial.eval g) f}
Sundog.TarskiQE.SADef.compl : ∀ {n : ℕ} {s : Set (Fin n → ℝ)}, Sundog.TarskiQE.SADef n s → Sundog.TarskiQE.SADef n sᶜ
Sundog.TarskiQE.SADef.union : ∀ {n : ℕ} {s t : Set (Fin n → ℝ)},
  Sundog.TarskiQE.SADef n s → Sundog.TarskiQE.SADef n t → Sundog.TarskiQE.SADef n (s ∪ t)
-/
#guard_msgs in
#print Sundog.TarskiQE.SADef

/--
info: @Sundog.TarskiQE.sadef_proj : ∀ {n : ℕ} {A : Set (Fin (n + 1) → ℝ)},
  Sundog.TarskiQE.SADef (n + 1) A → Sundog.TarskiQE.SADef n {g | ∃ y, Fin.snoc g y ∈ A}
-/
#guard_msgs in
#check @Sundog.TarskiQE.sadef_proj

/--
info: @Sundog.TarskiQE.sadef_sign_char : ∀ {m : ℕ} {A : Set (Fin m → ℝ)},
  Sundog.TarskiQE.SADef m A →
    ∃ F sigs, ∀ (h : Fin m → ℝ), h ∈ A ↔ List.map (fun q => SignType.sign ((MvPolynomial.eval h) q)) F ∈ sigs
-/
#guard_msgs in
#check @Sundog.TarskiQE.sadef_sign_char

/--
info: @Sundog.TarskiQE.elim_signVector : ∀ {n : ℕ} (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) (σ : List SignType),
  Sundog.TarskiQE.SADef n {g | ∃ y, Sundog.TarskiQE.signVec F g y = σ}
-/
#guard_msgs in
#check @Sundog.TarskiQE.elim_signVector

/-- info: 'Sundog.TarskiQE.sadef_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.sadef_proj

/--
info: 'Sundog.TarskiQE.sadef_sign_char' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Sundog.TarskiQE.sadef_sign_char

/--
info: 'Sundog.TarskiQE.elim_signVector' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Sundog.TarskiQE.elim_signVector

end NLQCTests
