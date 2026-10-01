import NLQCLean.Geometry.LocalMotionRank

/-!
# Real rank of PVM local and diagonal motion

A PVM overlap velocity has an input-local skew-Hermitian
generator and an output-diagonal skew-Hermitian generator.  Their common
scalar phase acts trivially on every overlap matrix, including nonunitary
ones.  This gives the rank bound `3 d^2 - 2` used by the transverse
differential estimate.
-/

namespace NLQCLean

open Matrix

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- Record the imaginary diagonal of a diagonal skew-Hermitian matrix. -/
def diagSkewImaginaryDiagonal (n : Type*) [Fintype n] [DecidableEq n] :
    diagSkew n →ₗ[ℝ] (n → ℝ) where
  toFun X := fun i => (X.1 i i).im
  map_add' X Y := by
    ext i
    simp
  map_smul' c X := by
    ext i
    simp [Complex.real_smul]

theorem diagSkewImaginaryDiagonal_injective
    (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (diagSkewImaginaryDiagonal n) := by
  intro X Y hXY
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst j
    have him := congrFun hXY i
    change (X.1 i i).im = (Y.1 i i).im at him
    have hXentry := congrArg (fun M : Matrix n n ℂ => M i i)
      (mem_diagSkew_iff.mp X.property).2
    have hYentry := congrArg (fun M : Matrix n n ℂ => M i i)
      (mem_diagSkew_iff.mp Y.property).2
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at hXentry hYentry
    have hXre := congrArg Complex.re hXentry
    have hYre := congrArg Complex.re hYentry
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hXre hYre
    apply Complex.ext
    · linarith
    · exact him
  · exact ((mem_diagSkew_iff.mp X.property).1 i j hij).trans
      ((mem_diagSkew_iff.mp Y.property).1 i j hij).symm

/-- A diagonal skew-Hermitian matrix has at most one real parameter per
diagonal entry. -/
theorem finrank_diagSkew_le (n : Type*) [Fintype n] [DecidableEq n] :
    Module.finrank ℝ (diagSkew n) ≤ Fintype.card n := by
  have h := (diagSkewImaginaryDiagonal n).finrank_le_finrank_of_injective
    (diagSkewImaginaryDiagonal_injective n)
  simpa only [Module.finrank_pi] using h

/-- Input-local and output-diagonal generators acting on an arbitrary
overlap matrix. -/
noncomputable def pvmMotionMap (H : Matrix (a × b) (a × b) ℂ) :
    (localSkew a b × diagSkew (a × b)) →ₗ[ℝ]
      Matrix (a × b) (a × b) ℂ :=
  ((mulRightCLM H).toLinearMap.comp (localSkew a b).subtype).coprod
    (-((mulLeftCLM H).toLinearMap.comp (diagSkew (a × b)).subtype))

theorem pvmMotionMap_apply (H : Matrix (a × b) (a × b) ℂ)
    (u : localSkew a b) (v : diagSkew (a × b)) :
    pvmMotionMap H (u, v) =
      -(v : Matrix (a × b) (a × b) ℂ) * H + H * u := by
  simp [pvmMotionMap, add_comm]

theorem range_pvmMotionMap (H : Matrix (a × b) (a × b) ℂ) :
    LinearMap.range (pvmMotionMap H) =
      allowedTangent (localSkew a b) (diagSkew (a × b)) H := by
  ext Y
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    exact mem_allowedTangent_iff.mpr ⟨u, u.property, v, v.property,
      by simp [pvmMotionMap_apply]⟩
  · intro hY
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_allowedTangent_iff.mp hY
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), by simp [pvmMotionMap_apply]⟩

/-- The common scalar phase belongs to the diagonal skew-Hermitian algebra. -/
theorem smul_I_one_mem_diagSkew (n : Type*) [Fintype n] [DecidableEq n]
    (r : ℝ) :
    (r • Complex.I) • (1 : Matrix n n ℂ) ∈ diagSkew n := by
  rw [mem_diagSkew_iff]
  constructor
  · intro i j hij
    simp [hij]
  · simp

/-- The common input/output phase acts trivially even when `H` is not
unitary or invertible. -/
theorem pvmMotionMap_phase_kernel (H : Matrix (a × b) (a × b) ℂ) :
    let p : localSkew a b := ⟨Complex.I • 1, by
      simpa using (smul_I_one_mem_localSkew (ιA := a) (ιB := b) 1)⟩
    let q : diagSkew (a × b) := ⟨Complex.I • 1, by
      simpa using (smul_I_one_mem_diagSkew (a × b) 1)⟩
    pvmMotionMap H (p, q) = 0 := by
  simp [pvmMotionMap_apply]

/-- The local-input and diagonal-output PVM motion space has dimension at
most `dim(local) + dim(diagonal) - 1`, with the final subtraction supplied
by their common scalar phase. -/
theorem finrank_allowedTangent_pvm_le [Nonempty a] [Nonempty b]
    (H : Matrix (a × b) (a × b) ℂ) :
    Module.finrank ℝ
        (allowedTangent (localSkew a b) (diagSkew (a × b)) H) ≤
      Fintype.card a ^ 2 + Fintype.card b ^ 2 + Fintype.card (a × b) - 2 := by
  let p : localSkew a b := ⟨Complex.I • 1, by
    simpa using (smul_I_one_mem_localSkew (ιA := a) (ιB := b) 1)⟩
  let q : diagSkew (a × b) := ⟨Complex.I • 1, by
    simpa using (smul_I_one_mem_diagSkew (a × b) 1)⟩
  have hp : p ≠ 0 := by
    intro hz
    apply phaseSkew_ne_zero (a × b)
    apply Subtype.ext
    change Complex.I • (1 : Matrix (a × b) (a × b) ℂ) = 0
    exact congrArg
      (fun u : localSkew a b => (u : Matrix (a × b) (a × b) ℂ)) hz
  have hk : 1 ≤ Module.finrank ℝ (LinearMap.ker (pvmMotionMap H)) := by
    apply Submodule.one_le_finrank_iff.mpr
    intro hzero
    have hm : (p, q) ∈ LinearMap.ker (pvmMotionMap H) :=
      pvmMotionMap_phase_kernel H
    rw [hzero, Submodule.mem_bot] at hm
    exact hp (congrArg Prod.fst hm)
  have hd := (pvmMotionMap H).finrank_range_add_finrank_ker
  rw [range_pvmMotionMap, Module.finrank_prod] at hd
  have hl := finrank_localSkew_le (a := a) (b := b)
  have hdiag := finrank_diagSkew_le (a × b)
  have hposA : 0 < Fintype.card a := Fintype.card_pos
  have hposB : 0 < Fintype.card b := Fintype.card_pos
  have hsqA : 0 < Fintype.card a ^ 2 := pow_pos hposA 2
  have hsqB : 0 < Fintype.card b ^ 2 := pow_pos hposB 2
  omega

/-- Any real-linear PVM motion term has rank at most `3 d^2 - 2`.  The
parameter space is arbitrary and `H` need not be unitary. -/
theorem finrank_range_le_of_pvm_motion {n V : Type*}
    [Fintype n] [DecidableEq n] [Nonempty n] [AddCommGroup V] [Module ℝ V]
    (H : Matrix (n × n) (n × n) ℂ)
    (T : V →ₗ[ℝ] Matrix (n × n) (n × n) ℂ)
    (hT : ∀ v, ∃ a ∈ localSkew n n, ∃ b ∈ diagSkew (n × n),
      T v = -b * H + H * a) :
    Module.finrank ℝ (LinearMap.range T) ≤ 3 * Fintype.card n ^ 2 - 2 := by
  have hr : LinearMap.range T ≤
      allowedTangent (localSkew n n) (diagSkew (n × n)) H := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, b, hb, heq⟩ := hT v
    exact mem_allowedTangent_iff.mpr ⟨a, ha, b, hb, by simpa using heq⟩
  have hd := (Submodule.finrank_mono hr).trans
    (finrank_allowedTangent_pvm_le H)
  have heq : Fintype.card n ^ 2 + Fintype.card n ^ 2 +
      Fintype.card (n × n) = 3 * Fintype.card n ^ 2 := by
    rw [Fintype.card_prod]
    ring
  simpa only [heq] using hd

end NLQCLean
