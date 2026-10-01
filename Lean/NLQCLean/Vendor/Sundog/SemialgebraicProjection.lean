/-
Derived from sundogcert (https://github.com/humiliati/sundogcert) at commit
c5c8d2b21cc118a2f1be1138b9800a991b57e084 (Sundogcert/SemialgebraicStructure.lean),
licensed under Apache-2.0 (see NLQCLean/Vendor/Sundog/LICENSE).
Modified for NLQCLean: extraction of two declarations, import paths and
Lean/Mathlib v4.33.1 compatibility; see NLQCLean/Vendor/Sundog/README.md.
-/
import NLQCLean.Vendor.Sundog.DiagramAssembly

/-!
# Projection of `SADef` sets

This module is an extract of the upstream file `Sundogcert/SemialgebraicStructure.lean`.
It contains only the sign characterization `sadef_sign_char` and the projection theorem
`sadef_proj`, unchanged apart from the recorded compatibility edits. The remainder of the
upstream file (substitution, the order atoms, and the o-minimal structure built on
`Sundogcert.OMinimalCellDecomp`) is not vendored.

From the upstream module documentation:

- **projection** — THE TS-2 PAYOFF: a `SADef` set is characterized by the sign vectors
  of a finite family (`sadef_sign_char`, by induction over the `allSignVecs`
  enumeration); the snoc-projection transports to the cons-based `finSuccEquiv` frame
  by the rotation `Fin.snoc Fin.succ 0`, and each sign-vector fiber is semialgebraic
  by `elim_signVector`.
-/

namespace Sundog.TarskiQE

open Polynomial Sundog.OMinimalOne

variable {n : ℕ}

/-! ### The sign characterization of SADef sets -/

/-- Every `SADef` set is a sign-vector condition on a finite family. -/
theorem sadef_sign_char {m : ℕ} {A : Set (Fin m → ℝ)} (hA : SADef m A) :
    ∃ (F : List (MvPolynomial (Fin m) ℝ)) (sigs : List (List SignType)),
      ∀ h : Fin m → ℝ,
        h ∈ A ↔ F.map (fun q => SignType.sign (MvPolynomial.eval h q)) ∈ sigs := by
  induction hA with
  | pos q =>
    refine ⟨[q], [[SignType.pos]], fun h => ?_⟩
    simp only [Set.mem_ofPred_eq, List.map_cons, List.map_nil, List.mem_singleton,
      List.cons.injEq, and_true]
    exact ⟨fun hp => sign_pos hp, fun hs => sign_eq_one_iff.mp hs⟩
  | compl hA ih =>
    obtain ⟨F, sigs, hch⟩ := ih
    refine ⟨F, (allSignVecs F.length).filter (fun τ => τ ∉ sigs), fun h => ?_⟩
    constructor
    · intro hc
      rw [List.mem_filter]
      refine ⟨mem_allSignVecs (by simp), ?_⟩
      simp only [decide_eq_true_eq]
      exact fun hmem => hc ((hch h).mpr hmem)
    · intro hmem hA'
      rw [List.mem_filter] at hmem
      have h2 := hmem.2
      simp only [decide_eq_true_eq] at h2
      exact h2 ((hch h).mp hA')
  | union hA hB ihA ihB =>
    obtain ⟨FA, sigsA, hchA⟩ := ihA
    obtain ⟨FB, sigsB, hchB⟩ := ihB
    refine ⟨FA ++ FB, (allSignVecs (FA ++ FB).length).filter
      (fun τ => τ.take FA.length ∈ sigsA ∨ τ.drop FA.length ∈ sigsB), fun h => ?_⟩
    have hsplit : (FA ++ FB).map (fun q => SignType.sign (MvPolynomial.eval h q))
        = (FA.map fun q => SignType.sign (MvPolynomial.eval h q))
          ++ (FB.map fun q => SignType.sign (MvPolynomial.eval h q)) := by
      rw [List.map_append]
    have htake : ((FA ++ FB).map
        (fun q => SignType.sign (MvPolynomial.eval h q))).take FA.length
        = FA.map fun q => SignType.sign (MvPolynomial.eval h q) := by
      rw [hsplit]
      exact List.take_left' (by rw [List.length_map])
    have hdrop : ((FA ++ FB).map
        (fun q => SignType.sign (MvPolynomial.eval h q))).drop FA.length
        = FB.map fun q => SignType.sign (MvPolynomial.eval h q) := by
      rw [hsplit]
      exact List.drop_left' (by rw [List.length_map])
    constructor
    · intro hmem
      rw [List.mem_filter]
      refine ⟨mem_allSignVecs (by simp), ?_⟩
      simp only [decide_eq_true_eq]
      rcases hmem with hA' | hB'
      · exact Or.inl (by rw [htake]; exact (hchA h).mp hA')
      · exact Or.inr (by rw [hdrop]; exact (hchB h).mp hB')
    · intro hmem
      rw [List.mem_filter] at hmem
      have h2 := hmem.2
      simp only [decide_eq_true_eq] at h2
      rcases h2 with hA' | hB'
      · exact Or.inl ((hchA h).mpr (by rw [htake] at hA'; exact hA'))
      · exact Or.inr ((hchB h).mpr (by rw [hdrop] at hB'; exact hB'))

/-! ### Projection: the TS-2 payoff -/

theorem sadef_proj {A : Set (Fin (n + 1) → ℝ)} (hA : SADef (n + 1) A) :
    SADef n {g : Fin n → ℝ | ∃ y : ℝ, Fin.snoc g y ∈ A} := by
  obtain ⟨F, sigs, hch⟩ := sadef_sign_char hA
  have hcomp : ∀ (g : Fin n → ℝ) (y : ℝ),
      (Fin.cons y g : Fin (n + 1) → ℝ) ∘ (Fin.snoc Fin.succ 0) = Fin.snoc g y := by
    intro g y
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j
      simp
  set F' : List (Polynomial (MvPolynomial (Fin n) ℝ)) := F.map fun q =>
    MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.rename (Fin.snoc Fin.succ 0) q)
    with hF'
  have hvec : ∀ (g : Fin n → ℝ) (y : ℝ),
      F.map (fun q => SignType.sign (MvPolynomial.eval (Fin.snoc g y) q))
        = signVec F' g y := by
    intro g y
    rw [signVec, hF', List.map_map]
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp_apply]
    rw [← spec_eval_cons, MvPolynomial.eval_rename, hcomp g y]
  have hset : {g : Fin n → ℝ | ∃ y : ℝ, Fin.snoc g y ∈ A}
      = ⋃ σ ∈ sigs, {g : Fin n → ℝ | ∃ y : ℝ, signVec F' g y = σ} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨y, hy⟩
      have hv := (hch (Fin.snoc g y)).mp hy
      rw [hvec g y] at hv
      exact ⟨_, hv, y, rfl⟩
    · rintro ⟨σ, hσ, y, hy⟩
      refine ⟨y, (hch (Fin.snoc g y)).mpr ?_⟩
      rw [hvec g y, hy]
      exact hσ
  rw [hset]
  exact SADef.list_biUnion fun σ _ => elim_signVector F' σ

end Sundog.TarskiQE
