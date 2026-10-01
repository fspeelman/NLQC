import NLQCLean.LinearAlgebra.AdjointDimension
import NLQCLean.Geometry.LocalOrbit

/-!
# Real rank of local two-sided motion

The scalar kernel in each
local generator costs one dimension, and the common input/output scalar
costs one further dimension. No invertibility or unitarity of H is used.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker Matrix.Norms.Frobenius

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- The pure phase generator iI as a skew-Hermitian matrix. -/
noncomputable def phaseSkew (n : Type*) [Fintype n] [DecidableEq n] : skewHermitian n :=
  ⟨Complex.I • 1, by simp [mem_skewHermitian_iff]⟩

theorem phaseSkew_ne_zero (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n] :
    phaseSkew n ≠ 0 := by
  intro h
  let i : n := Classical.arbitrary n
  have he := congrArg (fun X : skewHermitian n => ((X : Matrix n n ℂ) i i).im) h
  simp [phaseSkew] at he

/-- The pair of local generators maps onto the local algebra. -/
noncomputable def localGeneratorMap :
    (skewHermitian a × skewHermitian b) →ₗ[ℝ] Matrix (a × b) (a × b) ℂ :=
  ((ampLeft a b).comp (skewHermitian a).subtype).coprod
    ((ampRight a b).comp (skewHermitian b).subtype)

theorem range_localGeneratorMap : LinearMap.range (localGeneratorMap (a := a) (b := b)) =
    localSkew a b := by
  simp [localGeneratorMap, LinearMap.range_coprod, LinearMap.range_comp, localSkew]

/-- The Alice/Bob scalar cancellation is a nonzero kernel direction. -/
theorem localGeneratorMap_phase_kernel :
    localGeneratorMap (a := a) (b := b) (phaseSkew a, -phaseSkew b) = 0 := by
  change (Complex.I • (1 : Matrix a a ℂ)) ⊗ₖ (1 : Matrix b b ℂ) +
    (1 : Matrix a a ℂ) ⊗ₖ (-(Complex.I • (1 : Matrix b b ℂ))) = 0
  ext ⟨i, j⟩ ⟨k, l⟩
  change (Complex.I * (1 : Matrix a a ℂ) i k) * (1 : Matrix b b ℂ) j l +
    (1 : Matrix a a ℂ) i k * (-(Complex.I * (1 : Matrix b b ℂ) j l)) = 0
  ring

/-- One scalar direction is redundant in the two local skew-Hermitian spaces. -/
theorem finrank_localSkew_le [Nonempty a] [Nonempty b] :
    Module.finrank ℝ (localSkew a b) ≤ Fintype.card a ^ 2 + Fintype.card b ^ 2 - 1 := by
  have hk : 1 ≤ Module.finrank ℝ (LinearMap.ker (localGeneratorMap (a := a) (b := b))) := by
    apply Submodule.one_le_finrank_iff.mpr
    intro hzero
    have hm := localGeneratorMap_phase_kernel (a := a) (b := b)
    change (phaseSkew a, -phaseSkew b) ∈ LinearMap.ker localGeneratorMap at hm
    rw [hzero, Submodule.mem_bot] at hm
    exact phaseSkew_ne_zero a (congrArg Prod.fst hm)
  have hd := (localGeneratorMap (a := a) (b := b)).finrank_range_add_finrank_ker
  rw [range_localGeneratorMap, Module.finrank_prod, finrank_skewHermitian,
    finrank_skewHermitian] at hd
  omega

/-- Local input/output generators acting on an arbitrary overlap matrix. -/
noncomputable def localMotionMap (H : Matrix (a × b) (a × b) ℂ) :
    (localSkew a b × localSkew a b) →ₗ[ℝ] Matrix (a × b) (a × b) ℂ :=
  ((mulRightCLM H).toLinearMap.comp (localSkew a b).subtype).coprod
    (-((mulLeftCLM H).toLinearMap.comp (localSkew a b).subtype))

theorem localMotionMap_apply (H : Matrix (a × b) (a × b) ℂ) (u v : localSkew a b) :
    localMotionMap H (u, v) = -(v : Matrix (a × b) (a × b) ℂ) * H + H * u := by
  simp [localMotionMap, add_comm]

theorem range_localMotionMap (H : Matrix (a × b) (a × b) ℂ) :
    LinearMap.range (localMotionMap H) = allowedTangent (localSkew a b) (localSkew a b) H := by
  ext Y
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    exact mem_allowedTangent_iff.mpr ⟨u, u.property, v, v.property,
      by simp [localMotionMap_apply]⟩
  · intro hY
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_allowedTangent_iff.mp hY
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), by simp [localMotionMap_apply]⟩

/-- The common phase on input and output acts trivially even at nonunitary H. -/
theorem localMotionMap_phase_kernel (H : Matrix (a × b) (a × b) ℂ) :
    let p : localSkew a b := ⟨Complex.I • 1, by
      simpa using (smul_I_one_mem_localSkew (ιA := a) (ιB := b) 1)⟩
    localMotionMap H (p, p) = 0 := by
  simp [localMotionMap_apply]

/-- The two local scalar cancellations and the common phase remove
three real directions from the four local skew-Hermitian spaces. -/
theorem finrank_allowedTangent_local_le [Nonempty a] [Nonempty b]
    (H : Matrix (a × b) (a × b) ℂ) :
    Module.finrank ℝ (allowedTangent (localSkew a b) (localSkew a b) H) ≤
      2 * (Fintype.card a ^ 2 + Fintype.card b ^ 2) - 3 := by
  let p : localSkew a b := ⟨Complex.I • 1, by
    simpa using (smul_I_one_mem_localSkew (ιA := a) (ιB := b) 1)⟩
  have hp : p ≠ 0 := by
    intro hz
    apply phaseSkew_ne_zero (a × b)
    apply Subtype.ext
    change Complex.I • (1 : Matrix (a × b) (a × b) ℂ) = 0
    exact congrArg (fun q : localSkew a b => (q : Matrix (a × b) (a × b) ℂ)) hz
  have hk : 1 ≤ Module.finrank ℝ (LinearMap.ker (localMotionMap H)) := by
    apply Submodule.one_le_finrank_iff.mpr
    intro hzero
    have hm : (p, p) ∈ LinearMap.ker (localMotionMap H) := localMotionMap_phase_kernel H
    rw [hzero, Submodule.mem_bot] at hm
    exact hp (congrArg Prod.fst hm)
  have hd := (localMotionMap H).finrank_range_add_finrank_ker
  rw [range_localMotionMap, Module.finrank_prod] at hd
  have hl := finrank_localSkew_le (a := a) (b := b)
  have hposA : 0 < Fintype.card a := Fintype.card_pos
  have hposB : 0 < Fintype.card b := Fintype.card_pos
  have hsum : 0 < Fintype.card a ^ 2 + Fintype.card b ^ 2 := by positivity
  omega

/-- Any real-linear local-motion term has rank at most 4d²-3. Its parameter
space is arbitrary, and H need not be unitary. -/
theorem finrank_range_le_of_local_motion {n V : Type*}
    [Fintype n] [DecidableEq n] [Nonempty n] [AddCommGroup V] [Module ℝ V]
    (H : Matrix (n × n) (n × n) ℂ) (T : V →ₗ[ℝ] Matrix (n × n) (n × n) ℂ)
    (hT : ∀ v, ∃ a ∈ localSkew n n, ∃ b ∈ localSkew n n, T v = -b * H + H * a) :
    Module.finrank ℝ (LinearMap.range T) ≤ 4 * Fintype.card n ^ 2 - 3 := by
  have hr : LinearMap.range T ≤ allowedTangent (localSkew n n) (localSkew n n) H := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, b, hb, heq⟩ := hT v
    exact mem_allowedTangent_iff.mpr ⟨a, ha, b, hb, by simpa using heq⟩
  have hd := (Submodule.finrank_mono hr).trans (finrank_allowedTangent_local_le H)
  simpa only [show 2 * (Fintype.card n ^ 2 + Fintype.card n ^ 2) =
    4 * Fintype.card n ^ 2 by omega] using hd

end NLQCLean
