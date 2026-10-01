/-
Target geometry: local unitaries, double orbits, and PVM basis equivalence.
-/
import NLQCLean.LinearAlgebra.Bipartite
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Target geometry

The paper identifies targets up to local processing (snapshot §2.2-2.3):

* eq:unitary-orbit (L476-483): the double local-unitary orbit
  `𝒪_u(U) = {(L_A ⊗ L_B) U (S_A ⊗ S_B)}`;
* eq:basis-unitary (L501-506): an ordered rank-one PVM is represented by its
  basis unitary `M_Φ = Σ_i |φ_i⟩⟨i|`, i.e. simply by an element of the
  unitary group whose columns are the basis vectors;
* eq:basis-equivalence (L536-541): on basis unitaries the common-local-unitary
  equivalence is `M_Φ ↦ (L_A ⊗ L_B) M_Φ Δ` with `Δ` a diagonal (phase)
  unitary.

Targets are square matrices on the product index type and
tensor products of local operators are Kronecker products, so all three
notions are plain sets of matrices here.  Orbits are `Set`s, not quotients:
`thm:finite-orbit` speaks of finite unions of orbits, which needs only the
sets.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

variable {ιA ιB : Type*} [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]

section LocalUnitaries

variable (ιA ιB)

/-- Product local unitaries `L_A ⊗ L_B` on the joint space. -/
def localUnitaries : Set (Matrix (ιA × ιB) (ιA × ιB) ℂ) :=
  {W | ∃ LA ∈ Matrix.unitaryGroup ιA ℂ, ∃ LB ∈ Matrix.unitaryGroup ιB ℂ, W = LA ⊗ₖ LB}

/-- Diagonal phase unitaries `Δ ∈ 𝕋^D` acting on basis-vector phases. -/
def phaseUnitaries (n : Type*) [Fintype n] [DecidableEq n] : Set (Matrix n n ℂ) :=
  {Δ | ∃ φ : n → ℂ, (∀ i, ‖φ i‖ = 1) ∧ Δ = Matrix.diagonal φ}

variable {ιA ιB}

/-- A product local unitary is unitary. -/
theorem localUnitaries_subset_unitary :
    localUnitaries ιA ιB ⊆ (Matrix.unitaryGroup (ιA × ιB) ℂ : Set _) := by
  rintro W ⟨LA, hLA, LB, hLB, rfl⟩
  exact Matrix.kronecker_mem_unitary hLA hLB

/-- The identity is a product local unitary. -/
theorem one_mem_localUnitaries : (1 : Matrix (ιA × ιB) (ιA × ιB) ℂ) ∈ localUnitaries ιA ιB :=
  ⟨1, Submonoid.one_mem _, 1, Submonoid.one_mem _, (Matrix.one_kronecker_one).symm⟩

/-- A phase unitary is unitary. -/
theorem phaseUnitaries_subset_unitary {n : Type*} [Fintype n] [DecidableEq n] :
    phaseUnitaries n ⊆ (Matrix.unitaryGroup n ℂ : Set _) := by
  rintro Δ ⟨φ, hφ, rfl⟩
  rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff]
  ext i j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply]
  rcases eq_or_ne i j with rfl | hij
  · have h1 : φ i * (starRingEnd ℂ) (φ i) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hφ i]
      norm_num
    simp [h1]
  · simp [hij, Ne.symm hij]

/-- The identity is a phase unitary. -/
theorem one_mem_phaseUnitaries {n : Type*} [Fintype n] [DecidableEq n] :
    (1 : Matrix n n ℂ) ∈ phaseUnitaries n :=
  ⟨fun _ => 1, fun _ => norm_one, (Matrix.diagonal_one).symm⟩

end LocalUnitaries

section Orbits

variable (ιA ιB)

/-- **eq:unitary-orbit** (snapshot L476-483): the double local-unitary orbit
`𝒪_u(U)`. -/
def unitaryDoubleOrbit (U : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    Set (Matrix (ιA × ιB) (ιA × ιB) ℂ) :=
  {V | ∃ L ∈ localUnitaries ιA ιB, ∃ S ∈ localUnitaries ιA ιB, V = L * U * S}

/-- **eq:basis-equivalence** (snapshot L536-541): the common-local-unitary and
phase orbit of a basis unitary `M_Φ`. -/
def pvmBasisOrbit (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    Set (Matrix (ιA × ιB) (ιA × ιB) ℂ) :=
  {N | ∃ L ∈ localUnitaries ιA ιB, ∃ Δ ∈ phaseUnitaries (ιA × ιB), N = L * M * Δ}

variable {ιA ιB}

theorem self_mem_unitaryDoubleOrbit (U : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    U ∈ unitaryDoubleOrbit ιA ιB U :=
  ⟨1, one_mem_localUnitaries, 1, one_mem_localUnitaries, by simp⟩

theorem self_mem_pvmBasisOrbit (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    M ∈ pvmBasisOrbit ιA ιB M :=
  ⟨1, one_mem_localUnitaries, 1, one_mem_phaseUnitaries, by simp⟩

end Orbits

end NLQCLean
