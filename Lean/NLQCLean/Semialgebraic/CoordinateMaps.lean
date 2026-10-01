/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.Format

/-!
# Coordinate maps for concrete semialgebraic descriptions

Relabeling variables preserves
LRT format caps, including noninjective coordinate selections. Polynomial
substitution was proved in `Format`; no projection-closure theorem is used.
-/

section

namespace NLQCLean

/-- Select an ordered family of real Euclidean coordinates. Injectivity is
required by dimension definitions, but not by polynomial pullback. -/
noncomputable def coordinateProjection {n k : ℕ} (I : Fin k → Fin n)
    (x : RealEuclidean n) : RealEuclidean k :=
  WithLp.toLp 2 (fun j => x (I j))

@[simp] theorem coordinateProjection_apply {n k : ℕ} (I : Fin k → Fin n)
    (x : RealEuclidean n) (j : Fin k) : coordinateProjection I x j = x (I j) := rfl

@[fun_prop] theorem continuous_coordinateProjection {n k : ℕ} (I : Fin k → Fin n) :
    Continuous (coordinateProjection I) := by
  unfold coordinateProjection
  fun_prop

@[simp] theorem coordinateProjection_id {n : ℕ} :
    coordinateProjection (id : Fin n → Fin n) = id := by
  funext x
  rfl

@[simp] theorem coordinateProjection_comp {n k l : ℕ}
    (I : Fin k → Fin n) (J : Fin l → Fin k) :
    coordinateProjection J ∘ coordinateProjection I = coordinateProjection (I ∘ J) := rfl

namespace PolynomialSignDNF

variable {n k : ℕ}

/-- Rename polynomial variables by an arbitrary coordinate selection. -/
noncomputable def rename (F : PolynomialSignDNF k) (I : Fin k → Fin n) :
    PolynomialSignDNF n :=
  ⟨F.clauses.map fun L => L.map fun A => ⟨MvPolynomial.rename I A.polynomial, A.sign⟩⟩

@[simp] theorem source_rename (F : PolynomialSignDNF k) (I : Fin k → Fin n) :
    (F.rename I).source = coordinateProjection I ⁻¹' F.source := by
  ext x
  simp only [source, rename, List.mem_map, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨_, ⟨L, hL, rfl⟩, hx⟩
    refine ⟨L, hL, ?_⟩
    simpa only [clauseHolds, List.forall_mem_map, PolynomialSignAtom.Holds,
      MvPolynomial.eval_rename, Function.comp_def, coordinateProjection_apply] using hx
  · rintro ⟨L, hL, hx⟩
    refine ⟨_, ⟨L, hL, rfl⟩, ?_⟩
    simpa only [clauseHolds, List.forall_mem_map, PolynomialSignAtom.Holds,
      MvPolynomial.eval_rename, Function.comp_def, coordinateProjection_apply] using hx

@[simp] theorem length_rename (F : PolynomialSignDNF k) (I : Fin k → Fin n) :
    (F.rename I).clauses.length = F.clauses.length := by simp [rename]

@[simp] theorem maxAtoms_rename (F : PolynomialSignDNF k) (I : Fin k → Fin n) :
    (F.rename I).maxAtoms = F.maxAtoms := by
  simp [maxAtoms, rename, List.map_map, Function.comp_def]

theorem HasFormat.rename {F : PolynomialSignDNF k} {c D : ℕ}
    (h : F.HasFormat c D) (I : Fin k → Fin n) : (F.rename I).HasFormat c D := by
  refine ⟨by simpa using h.1, ?_⟩
  simp only [PolynomialSignDNF.rename, List.forall_mem_map]
  intro L hL A hA
  exact (MvPolynomial.totalDegree_rename_le I A.polynomial).trans (h.2 L hL A hA)

end PolynomialSignDNF

namespace Semialgebraic

variable {n k : ℕ} {S : Set (RealEuclidean k)}

theorem coordinate_preimage (hS : Semialgebraic S) (I : Fin k → Fin n) :
    Semialgebraic (coordinateProjection I ⁻¹' S) := by
  obtain ⟨F, rfl⟩ := hS
  exact ⟨F.rename I, F.source_rename I⟩

/-- Image under a coordinate permutation, by pulling back along its inverse.
This does not assert closure under a noninvertible projection. -/
theorem coordinate_equiv_image (hS : Semialgebraic S) (e : Fin n ≃ Fin k) :
    Semialgebraic (coordinateProjection e '' S) := by
  convert hS.coordinate_preimage e.symm using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [coordinateProjection, WithLp.toLp_ofLp, Function.comp_def] using hx
  · intro hy
    refine ⟨coordinateProjection e.symm y, hy, ?_⟩
    ext j
    simp

end Semialgebraic
end NLQCLean
end
