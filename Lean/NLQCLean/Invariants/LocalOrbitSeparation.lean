import NLQCLean.Invariants.CompactSeparation
import NLQCLean.Geometry.UnitaryNormalEmbedding
import NLQCLean.Models.Targets
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Finitely many polynomial invariants separate local orbits

The double local-unitary action `V ↦ (A ⊗ B) V (C ⊗ D)†` and the measurement
action `N ↦ (A ⊗ B) N Δ` with a diagonal phase matrix `Δ` are continuous
linear actions of compact groups on the real coordinates of bipartite
matrices. Their orbits are exactly `unitaryDoubleOrbit` and `pvmBasisOrbit`.
Finitely many real polynomials in the real and imaginary matrix entries,
constant on each orbit, separate all orbits.
-/

noncomputable section

namespace NLQCLean

open Matrix MeasureTheory MvPolynomial
open scoped Matrix Kronecker

universe u v w

section LinearAction

variable {G : Type v} [Group G] [TopologicalSpace G]
variable {σ : Type u} [Fintype σ] [DecidableEq σ]
variable {E : Type w} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The coordinate matrices of a continuous linear action, in a fixed linear
coordinate system. -/
def MatrixRepresentation.ofLinearAction (c : E ≃ₗ[ℝ] (σ → ℝ))
    (act : G → E →ₗ[ℝ] E) (hc : Continuous c) (hact : ∀ v, Continuous fun g => act g v)
    (hone : ∀ v, act 1 v = v) (hmul : ∀ g h v, act (g * h) v = act g (act h v)) :
    MatrixRepresentation G σ where
  toMatrix g := LinearMap.toMatrix' (c.toLinearMap ∘ₗ act g ∘ₗ c.symm.toLinearMap)
  continuous_toMatrix := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [LinearMap.toMatrix'_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply]
    exact (continuous_apply i).comp (hc.comp (hact _))
  map_one := by
    have : c.toLinearMap ∘ₗ act 1 ∘ₗ c.symm.toLinearMap = LinearMap.id :=
      LinearMap.ext fun x => by simp [hone]
    rw [this, LinearMap.toMatrix'_id]
  map_mul g h := by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext fun x => by simp [hmul]

theorem MatrixRepresentation.ofLinearAction_mulVec (c : E ≃ₗ[ℝ] (σ → ℝ))
    (act : G → E →ₗ[ℝ] E) (hc : Continuous c) (hact : ∀ v, Continuous fun g => act g v)
    (hone : ∀ v, act 1 v = v) (hmul : ∀ g h v, act (g * h) v = act g (act h v))
    (g : G) (v : E) :
    (MatrixRepresentation.ofLinearAction c act hc hact hone hmul).toMatrix g *ᵥ c v =
      c (act g v) := by
  simp [MatrixRepresentation.ofLinearAction, LinearMap.toMatrix'_mulVec]

theorem MatrixRepresentation.mem_orbit_ofLinearAction (c : E ≃ₗ[ℝ] (σ → ℝ))
    (act : G → E →ₗ[ℝ] E) (hc : Continuous c) (hact : ∀ v, Continuous fun g => act g v)
    (hone : ∀ v, act 1 v = v) (hmul : ∀ g h v, act (g * h) v = act g (act h v))
    (u v : E) :
    c v ∈ (MatrixRepresentation.ofLinearAction c act hc hact hone hmul).orbit (c u) ↔
      ∃ g, act g u = v := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, c.injective ?_⟩
    rw [← hg]
    exact (MatrixRepresentation.ofLinearAction_mulVec c act hc hact hone hmul g u).symm
  · rintro ⟨g, rfl⟩
    exact ⟨g, MatrixRepresentation.ofLinearAction_mulVec c act hc hact hone hmul g u⟩

/-- **Finite separation for an abstract continuous linear action.** -/
theorem exists_finite_separating_of_linearAction [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] (c : E ≃ₗ[ℝ] (σ → ℝ))
    (act : G → E →ₗ[ℝ] E) (hc : Continuous c) (hact : ∀ v, Continuous fun g => act g v)
    (hone : ∀ v, act 1 v = v) (hmul : ∀ g h v, act (g * h) v = act g (act h v)) :
    ∃ s : Finset (MvPolynomial σ ℝ),
      (∀ p ∈ s, ∀ g u, eval (c (act g u)) p = eval (c u) p) ∧
      ∀ u v : E, (∀ p ∈ s, eval (c u) p = eval (c v) p) → ∃ g, act g u = v := by
  let ρ := MatrixRepresentation.ofLinearAction c act hc hact hone hmul
  let _ : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let μ : Measure G := Measure.haarMeasure K₀
  have : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  obtain ⟨s, hs, hsep⟩ := ρ.exists_finite_separating_invariants μ
  refine ⟨s, fun p hp g u => ?_, fun u v huv => ?_⟩
  · rw [← MatrixRepresentation.ofLinearAction_mulVec c act hc hact hone hmul]
    exact hs p hp g (c u)
  · exact (MatrixRepresentation.mem_orbit_ofLinearAction c act hc hact hone hmul u v).mp
      (hsep (c u) (c v) huv)

end LinearAction

section Coordinates

variable (m n : Type*)

/-- Real coordinates of a complex matrix: index `0` is the real part and
index `1` the imaginary part of each entry. -/
def matrixRealCoords : Matrix m n ℂ ≃ₗ[ℝ] ((m × n) × Fin 2 → ℝ) where
  toFun V v := if v.2 = 0 then (V v.1.1 v.1.2).re else (V v.1.1 v.1.2).im
  invFun x i j := ⟨x ((i, j), 0), x ((i, j), 1)⟩
  map_add' V W := by
    funext v
    by_cases h : v.2 = 0 <;> simp [h]
  map_smul' r V := by
    funext v
    by_cases h : v.2 = 0 <;> simp [h]
  left_inv V := by
    funext i j
    apply Complex.ext <;> simp
  right_inv x := by
    funext v
    rcases v with ⟨⟨i, j⟩, b⟩
    fin_cases b <;> simp

variable {m n}

@[simp] theorem matrixRealCoords_apply (V : Matrix m n ℂ) (v : (m × n) × Fin 2) :
    matrixRealCoords m n V v =
      if v.2 = 0 then (V v.1.1 v.1.2).re else (V v.1.1 v.1.2).im := rfl

theorem continuous_matrixRealCoords : Continuous (matrixRealCoords m n) := by
  refine continuous_pi fun v => ?_
  have hentry : Continuous fun V : Matrix m n ℂ => V v.1.1 v.1.2 :=
    (continuous_apply v.1.2).comp (continuous_apply v.1.1)
  change Continuous fun V : Matrix m n ℂ =>
    if v.2 = 0 then (V v.1.1 v.1.2).re else (V v.1.1 v.1.2).im
  split_ifs
  · exact Complex.continuous_re.comp hentry
  · exact Complex.continuous_im.comp hentry

/-- A real polynomial evaluated at the real and imaginary entries. -/
def matrixPolyEval (p : MvPolynomial ((m × n) × Fin 2) ℝ) (V : Matrix m n ℂ) : ℝ :=
  eval (matrixRealCoords m n V) p

end Coordinates

theorem continuous_kronecker_comp {X l m n p : Type*} [TopologicalSpace X]
    {f : X → Matrix l m ℂ} {g : X → Matrix n p ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => f x ⊗ₖ g x := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.kroneckerMap_apply]
  exact ((continuous_apply j.1).comp ((continuous_apply i.1).comp hf)).mul
    ((continuous_apply j.2).comp ((continuous_apply i.2).comp hg))

theorem conjTranspose_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup n ℂ :=
  Unitary.star_mem hU

section LocalDouble

variable (ιA ιB : Type*) [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]

/-- The compact group of four local unitaries. -/
abbrev LocalUnitaryQuad :=
  Matrix.unitaryGroup ιA ℂ × Matrix.unitaryGroup ιB ℂ ×
    Matrix.unitaryGroup ιA ℂ × Matrix.unitaryGroup ιB ℂ

variable {ιA ιB}

/-- `V ↦ (A ⊗ B) V (C ⊗ D)†`. -/
def localDoubleAct (g : LocalUnitaryQuad ιA ιB) :
    Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℝ] Matrix (ιA × ιB) (ιA × ιB) ℂ where
  toFun V := ((g.1 : Matrix ιA ιA ℂ) ⊗ₖ (g.2.1 : Matrix ιB ιB ℂ)) * V *
    ((g.2.2.1 : Matrix ιA ιA ℂ) ⊗ₖ (g.2.2.2 : Matrix ιB ιB ℂ))ᴴ
  map_add' V W := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r V := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl

theorem localDoubleAct_one (V : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    localDoubleAct 1 V = V := by
  simp [localDoubleAct]

theorem localDoubleAct_mul (g h : LocalUnitaryQuad ιA ιB) (V : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    localDoubleAct (g * h) V = localDoubleAct g (localDoubleAct h V) := by
  simp only [localDoubleAct, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_mul, Prod.snd_mul,
    Submonoid.coe_mul, Matrix.mul_kronecker_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem continuous_localDoubleAct (V : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    Continuous fun g : LocalUnitaryQuad ιA ιB => localDoubleAct g V := by
  have h1 : Continuous fun g : LocalUnitaryQuad ιA ιB => (g.1 : Matrix ιA ιA ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun g : LocalUnitaryQuad ιA ιB => (g.2.1 : Matrix ιB ιB ℂ) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have h3 : Continuous fun g : LocalUnitaryQuad ιA ιB => (g.2.2.1 : Matrix ιA ιA ℂ) :=
    continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp continuous_snd))
  have h4 : Continuous fun g : LocalUnitaryQuad ιA ιB => (g.2.2.2 : Matrix ιB ιB ℂ) :=
    continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
  exact ((continuous_kronecker_comp h1 h2).matrix_mul continuous_const).matrix_mul
    (continuous_kronecker_comp h3 h4).matrix_conjTranspose

theorem exists_localDoubleAct_iff (U V : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    (∃ g, localDoubleAct g U = V) ↔ V ∈ unitaryDoubleOrbit ιA ιB U := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨_, ⟨g.1, g.1.2, g.2.1, g.2.1.2, rfl⟩, _,
      ⟨(g.2.2.1 : Matrix ιA ιA ℂ)ᴴ, ?_, (g.2.2.2 : Matrix ιB ιB ℂ)ᴴ, ?_, ?_⟩, rfl⟩
    · exact conjTranspose_mem_unitaryGroup g.2.2.1.2
    · exact conjTranspose_mem_unitaryGroup g.2.2.2.2
    · exact Matrix.conjTranspose_kronecker _ _
  · rintro ⟨L, ⟨LA, hLA, LB, hLB, rfl⟩, S, ⟨SA, hSA, SB, hSB, rfl⟩, rfl⟩
    refine ⟨(⟨LA, hLA⟩, ⟨LB, hLB⟩, ⟨SAᴴ, conjTranspose_mem_unitaryGroup hSA⟩,
      ⟨SBᴴ, conjTranspose_mem_unitaryGroup hSB⟩), ?_⟩
    simp [localDoubleAct, Matrix.conjTranspose_kronecker]

/-- **Finitely many polynomial invariants separate double local-unitary orbits.**
The polynomials are real, in the real and imaginary parts of all entries, and
are constant on every orbit of every matrix. -/
theorem exists_finite_unitaryDoubleOrbit_separating :
    ∃ s : Finset (MvPolynomial (((ιA × ιB) × (ιA × ιB)) × Fin 2) ℝ),
      (∀ p ∈ s, ∀ U V : Matrix (ιA × ιB) (ιA × ιB) ℂ,
        V ∈ unitaryDoubleOrbit ιA ιB U → matrixPolyEval p V = matrixPolyEval p U) ∧
      ∀ U V : Matrix (ιA × ιB) (ιA × ιB) ℂ,
        (∀ p ∈ s, matrixPolyEval p U = matrixPolyEval p V) →
          V ∈ unitaryDoubleOrbit ιA ιB U := by
  obtain ⟨s, hs, hsep⟩ := exists_finite_separating_of_linearAction
    (G := LocalUnitaryQuad ιA ιB) (matrixRealCoords _ _) localDoubleAct
    continuous_matrixRealCoords continuous_localDoubleAct localDoubleAct_one localDoubleAct_mul
  refine ⟨s, fun p hp U V hV => ?_, fun U V hUV => ?_⟩
  · obtain ⟨g, rfl⟩ := (exists_localDoubleAct_iff U V).mpr hV
    exact hs p hp g U
  · exact (exists_localDoubleAct_iff U V).mp (hsep U V hUV)

end LocalDouble

/-- A unit complex number as an element of the circle group. -/
def circleOfNorm (z : ℂ) (h : ‖z‖ = 1) : Circle :=
  ⟨z, by simp [Submonoid.unitSphere, h]⟩

@[simp] theorem coe_circleOfNorm (z : ℂ) (h : ‖z‖ = 1) : (circleOfNorm z h : ℂ) = z := rfl

section Measurement

variable (ιA ιB : Type*) [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]

/-- Two local unitaries and one phase per basis label. -/
abbrev MeasurementGroup :=
  Matrix.unitaryGroup ιA ℂ × Matrix.unitaryGroup ιB ℂ × (ιA × ιB → Circle)

variable {ιA ιB}

/-- `N ↦ (A ⊗ B) N diag(φ)⁻¹`. -/
def measurementAct (g : MeasurementGroup ιA ιB) :
    Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℝ] Matrix (ιA × ιB) (ιA × ιB) ℂ where
  toFun N := ((g.1 : Matrix ιA ιA ℂ) ⊗ₖ (g.2.1 : Matrix ιB ιB ℂ)) * N *
    Matrix.diagonal (fun i => ((g.2.2 i)⁻¹ : Circle) : ιA × ιB → ℂ)
  map_add' V W := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r V := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl

theorem measurementAct_one (N : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    measurementAct 1 N = N := by
  simp [measurementAct]

theorem measurementAct_mul (g h : MeasurementGroup ιA ιB) (N : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    measurementAct (g * h) N = measurementAct g (measurementAct h N) := by
  simp only [measurementAct, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_mul, Prod.snd_mul,
    Submonoid.coe_mul, Matrix.mul_kronecker_mul, Matrix.mul_assoc, Pi.mul_apply, mul_inv,
    Circle.coe_mul, Matrix.diagonal_mul_diagonal]
  congr 4
  funext i
  ring

theorem continuous_measurementAct (N : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    Continuous fun g : MeasurementGroup ιA ιB => measurementAct g N := by
  have h1 : Continuous fun g : MeasurementGroup ιA ιB => (g.1 : Matrix ιA ιA ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun g : MeasurementGroup ιA ιB => (g.2.1 : Matrix ιB ιB ℂ) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have h3 : Continuous fun g : MeasurementGroup ιA ιB =>
      Matrix.diagonal (fun i => ((g.2.2 i)⁻¹ : Circle) : ιA × ιB → ℂ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij
      exact continuous_subtype_val.comp
        ((continuous_inv.comp (continuous_apply i)).comp (continuous_snd.comp continuous_snd))
    · exact continuous_const
  exact ((continuous_kronecker_comp h1 h2).matrix_mul continuous_const).matrix_mul h3

theorem exists_measurementAct_iff (M N : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    (∃ g, measurementAct g M = N) ↔ N ∈ pvmBasisOrbit ιA ιB M := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨_, ⟨g.1, g.1.2, g.2.1, g.2.1.2, rfl⟩, _,
      ⟨fun i => ((g.2.2 i)⁻¹ : Circle), fun i => Circle.norm_coe _, rfl⟩, rfl⟩
  · rintro ⟨L, ⟨LA, hLA, LB, hLB, rfl⟩, Δ, ⟨φ, hφ, rfl⟩, rfl⟩
    let ψ : ιA × ιB → Circle := fun i => (circleOfNorm (φ i) (hφ i))⁻¹
    refine ⟨(⟨LA, hLA⟩, ⟨LB, hLB⟩, ψ), ?_⟩
    simp only [measurementAct, LinearMap.coe_mk, AddHom.coe_mk]
    congr 2
    funext i
    change ((((circleOfNorm (φ i) (hφ i))⁻¹)⁻¹ : Circle) : ℂ) = φ i
    rw [inv_inv, coe_circleOfNorm]

/-- **Finitely many polynomial invariants separate measurement orbits.** -/
theorem exists_finite_pvmBasisOrbit_separating :
    ∃ s : Finset (MvPolynomial (((ιA × ιB) × (ιA × ιB)) × Fin 2) ℝ),
      (∀ p ∈ s, ∀ M N : Matrix (ιA × ιB) (ιA × ιB) ℂ,
        N ∈ pvmBasisOrbit ιA ιB M → matrixPolyEval p N = matrixPolyEval p M) ∧
      ∀ M N : Matrix (ιA × ιB) (ιA × ιB) ℂ,
        (∀ p ∈ s, matrixPolyEval p M = matrixPolyEval p N) →
          N ∈ pvmBasisOrbit ιA ιB M := by
  obtain ⟨s, hs, hsep⟩ := exists_finite_separating_of_linearAction
    (G := MeasurementGroup ιA ιB) (matrixRealCoords _ _) measurementAct
    continuous_matrixRealCoords continuous_measurementAct measurementAct_one measurementAct_mul
  refine ⟨s, fun p hp M N hN => ?_, fun M N hMN => ?_⟩
  · obtain ⟨g, rfl⟩ := (exists_measurementAct_iff M N).mpr hN
    exact hs p hp g M
  · exact (exists_measurementAct_iff M N).mp (hsep M N hMN)

end Measurement

end NLQCLean
