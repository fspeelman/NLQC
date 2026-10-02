/-
Local compression: the only calculation about the interior of a protocol.
-/
import NLQCLean.LinearAlgebra.Bipartite
import NLQCLean.LinearAlgebra.Isometry

/-!
# Local compression

This is `lem:shared-state-compression` of the snapshot (statement L586-622,
proof L624-637), described there as "the only calculation about the interior
of a protocol that we need".  Its three parts are proved separately, as the
statement matrix (row 1) requires; they are used together but are logically
independent.

* (i) `NLQCLean.compress_resource_ampLeft` — inserting a shared state turns
  an Alice-local generator into an amplified operator on the logical space:
  `J_η†(X_A ⊗ I)J_η = X̂_A ⊗ I` with
  `X̂_A = Tr_{R_A}[(I ⊗ η_A)X_A]` (eq:shared-compression, L594-602).
  The payoff for `prop:exact-velocity` is
  `NLQCLean.compress_resource_mem_localSkew`: anti-Hermitian local generators
  compress into `𝔤_{A:B}`.
* (ii) `NLQCLean.flag_compression_mem_diagonal` — compression through the
  duplicated outcome label is diagonal (eq:flag-isometry, L605-613).  This is
  the *only* source of the PVM case's diagonal output algebra.
* (iii) `NLQCLean.rangeProj_left_mul_eq` — a range contained in the decoder
  range is fixed by either single-laboratory decoder projection
  (eq:local-support-restriction, L616-620).

Index conventions.  `ιA, ιB` index the logical spaces `H_A, H_B` and
`ρA, ρB` the resource spaces `R_A, R_B`.  Registers are grouped **by
laboratory** (snapshot L454), so the ambient index of the protocol interior
is `(ιA × ρA) × (ιB × ρB)`.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

variable {ιA ιB ρA ρB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]

section SumRotate

/-- Move the innermost of three summations to the outside. -/
private theorem sum_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) :
    (∑ b, ∑ c, ∑ a, f a b c) = ∑ a, ∑ b, ∑ c, f a b c := by
  calc ∑ b, ∑ c, ∑ a, f a b c
      = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, f a b c := Finset.sum_comm

end SumRotate

section SharedState

/-- The shared-state insertion `J_η ψ = ψ ⊗ η`, with tensor factors regrouped
by laboratory (snapshot L449-454). -/
def insertResource (ιA ιB : Type*) [DecidableEq ιA] [DecidableEq ιB]
    (η : ρA × ρB → ℂ) :
    Matrix ((ιA × ρA) × (ιB × ρB)) (ιA × ιB) ℂ :=
  Matrix.of fun p q =>
    (if p.1.1 = q.1 then 1 else 0) * (if p.2.1 = q.2 then 1 else 0) * η (p.1.2, p.2.2)

/-- Alice's reduced resource operator `η_A = Tr_{R_B}|η⟩⟨η|`. -/
def resourceMarginal (η : ρA × ρB → ℂ) : Matrix ρA ρA ℂ :=
  Matrix.of fun r r' => ∑ s, η (r, s) * star (η (r', s))

/-- The compressed generator `X̂_A = Tr_{R_A}[(I_{H_A} ⊗ η_A)X_A]`. -/
def compressResource (η : ρA × ρB → ℂ) (X : Matrix (ιA × ρA) (ιA × ρA) ℂ) :
    Matrix ιA ιA ℂ :=
  Matrix.of fun a a' => ∑ r, ∑ r', resourceMarginal η r r' * X (a, r') (a', r)

omit [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB] [DecidableEq ρA] [DecidableEq ρB] in
@[simp] theorem insertResource_apply (η : ρA × ρB → ℂ)
    (p : (ιA × ρA) × (ιB × ρB)) (q : ιA × ιB) :
    insertResource ιA ιB η p q
      = (if p.1.1 = q.1 then 1 else 0) * (if p.2.1 = q.2 then 1 else 0)
          * η (p.1.2, p.2.2) := rfl

omit [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB] [DecidableEq ρA] [DecidableEq ρB] in
/-- The paper's form of the insertion (snapshot L449-454): `J_η ψ = ψ ⊗ η`
with tensor factors regrouped by laboratory. -/
theorem insertResource_apply_ite (η : ρA × ρB → ℂ)
    (p : (ιA × ρA) × (ιB × ρB)) (q : ιA × ιB) :
    insertResource ιA ιB η p q
      = if p.1.1 = q.1 ∧ p.2.1 = q.2 then η (p.1.2, p.2.2) else 0 := by
  rw [insertResource_apply]
  by_cases h1 : p.1.1 = q.1 <;> by_cases h2 : p.2.1 = q.2 <;> simp [h1, h2]

omit [DecidableEq ρA] [DecidableEq ρB] in
/-- `J_η` is an isometry when `η` is a unit vector (snapshot L449-454: `η` is
a unit vector of `R_A ⊗ R_B`).  This is what makes the global Stinespring
isometry of eq:global-isometry (L456-460) an isometry.

Instance of `NLQCLean.isIsometry_of_unit_columns`: the block label of a row
`p` is the pair of logical indices `(p.1.1, p.2.1)`, the within-block label is
the pair of resource indices `(p.1.2, p.2.2)`, and every column carries the
same unit vector `η`. -/
theorem isIsometry_insertResource (η : ρA × ρB → ℂ) (hη : IsUnitVector η) :
    IsIsometry (insertResource ιA ιB η) := by
  refine isIsometry_of_unit_columns (Equiv.prodProdProdComm ιA ρA ιB ρB) id
    Function.injective_id (fun _ => η) (fun _ => hη) ?_
  intro p q
  rw [insertResource_apply]
  by_cases h1 : p.1.1 = q.1 <;> by_cases h2 : p.2.1 = q.2 <;>
    simp [Equiv.prodProdProdComm_apply, Prod.ext_iff, h1, h2]

omit [Fintype ρA] [DecidableEq ρA] [DecidableEq ρB] in
@[simp] theorem resourceMarginal_apply (η : ρA × ρB → ℂ) (r r' : ρA) :
    resourceMarginal η r r' = ∑ s, η (r, s) * star (η (r', s)) := rfl

omit [Fintype ρA] [DecidableEq ρA] [DecidableEq ρB] in
/-- `η_A` is Hermitian. -/
theorem resourceMarginal_conjTranspose (η : ρA × ρB → ℂ) :
    (resourceMarginal η)ᴴ = resourceMarginal η := by
  ext r r'
  simp [Matrix.conjTranspose_apply, star_sum, mul_comm]

omit [DecidableEq ρA] [DecidableEq ρB] in
/-- Right multiplication by `J_η` collapses the two logical deltas, leaving a
sum over the resource indices only. -/
theorem mul_insertResource_apply (η : ρA × ρB → ℂ)
    (M : Matrix ((ιA × ρA) × (ιB × ρB)) ((ιA × ρA) × (ιB × ρB)) ℂ)
    (p : (ιA × ρA) × (ιB × ρB)) (q : ιA × ιB) :
    (M * insertResource ιA ιB η) p q
      = ∑ r, ∑ s, M p ((q.1, r), (q.2, s)) * η (r, s) := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, insertResource_apply]
  rw [Finset.sum_eq_single_of_mem q.1 (Finset.mem_univ _)
    (fun a _ ha => by simp [ha])]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single_of_mem q.2 (Finset.mem_univ _)
    (fun b _ hb => by simp [hb])]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp

omit [DecidableEq ρA] [DecidableEq ρB] in
/-- Left multiplication by `J_η†` collapses the two logical deltas. -/
theorem insertResource_conjTranspose_mul_apply (η : ρA × ρB → ℂ)
    (N : Matrix ((ιA × ρA) × (ιB × ρB)) (ιA × ιB) ℂ) (q : ιA × ιB) (q' : ιA × ιB) :
    ((insertResource ιA ιB η)ᴴ * N) q q'
      = ∑ r, ∑ s, star (η (r, s)) * N ((q.1, r), (q.2, s)) q' := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    insertResource_apply]
  rw [Finset.sum_eq_single_of_mem q.1 (Finset.mem_univ _)
    (fun a _ ha => by simp [ha])]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single_of_mem q.2 (Finset.mem_univ _)
    (fun b _ hb => by simp [hb])]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp

omit [DecidableEq ρA] in
/-- **eq:shared-compression** (snapshot L594-602).  Compression of an
Alice-local generator through the shared state is the amplification of the
compressed generator. -/
theorem compress_resource_ampLeft (η : ρA × ρB → ℂ)
    (X : Matrix (ιA × ρA) (ιA × ρA) ℂ) :
    (insertResource ιA ιB η)ᴴ
        * ampLeft (ιA × ρA) (ιB × ρB) X * insertResource ιA ιB η
      = ampLeft ιA ιB (compressResource η X) := by
  ext q q'
  rw [Matrix.mul_assoc, insertResource_conjTranspose_mul_apply]
  simp only [mul_insertResource_apply, ampLeft_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, compressResource, Matrix.of_apply, resourceMarginal_apply,
    Prod.mk.injEq]
  by_cases hb : q.2 = q'.2
  · simp only [hb, true_and, mul_ite, ite_mul, zero_mul, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_one]
    rw [show (∑ r, ∑ s, star (η (r, s)) * ∑ r', X (q.1, r) (q'.1, r') * η (r', s))
        = ∑ b, ∑ c, ∑ a, star (η (b, c)) * (X (q.1, b) (q'.1, a) * η (a, c)) from
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
        Finset.mul_sum _ _ _, sum_rotate]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  · simp [hb]


omit [Fintype ιA] [DecidableEq ιA] [DecidableEq ρA] [DecidableEq ρB] in
/-- Compression is `ℝ`-linear in the generator, in the form needed below. -/
theorem compressResource_neg (η : ρA × ρB → ℂ)
    (X : Matrix (ιA × ρA) (ιA × ρA) ℂ) :
    compressResource η (-X) = -compressResource (ιA := ιA) η X := by
  ext a a'
  simp [compressResource, ← Finset.sum_neg_distrib]

omit [Fintype ιA] [DecidableEq ιA] [DecidableEq ρA] [DecidableEq ρB] in
/-- Anti-Hermitian generators compress to anti-Hermitian ones
(snapshot L603-604). -/
theorem compressResource_conjTranspose (η : ρA × ρB → ℂ)
    (X : Matrix (ιA × ρA) (ιA × ρA) ℂ) :
    compressResource η Xᴴ = (compressResource η X)ᴴ := by
  ext a a'
  simp only [compressResource, Matrix.of_apply, Matrix.conjTranspose_apply, star_sum,
    star_mul, resourceMarginal_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun t _ => by rw [star_star, mul_comm]

omit [DecidableEq ρA] in
/-- **The payoff for `prop:exact-velocity`** (snapshot L840-847): an
anti-Hermitian Alice-local generator compresses into the local Lie algebra
`𝔤_{A:B}`. -/
theorem compress_resource_mem_localSkew (η : ρA × ρB → ℂ)
    {X : Matrix (ιA × ρA) (ιA × ρA) ℂ} (hX : Xᴴ = -X) :
    (insertResource ιA ιB η)ᴴ
        * ampLeft (ιA × ρA) (ιB × ρB) X * insertResource ιA ιB η
      ∈ localSkew ιA ιB := by
  rw [compress_resource_ampLeft]
  refine Submodule.mem_sup_left ⟨compressResource η X, ?_, rfl⟩
  show compressResource η X ∈ skewHermitian ιA
  rw [mem_skewHermitian_iff, ← compressResource_conjTranspose, hX,
    compressResource_neg]

/-- Bob's reduced resource operator `η_B = Tr_{R_A}|η⟩⟨η|`. -/
def resourceMarginalRight (η : ρA × ρB → ℂ) : Matrix ρB ρB ℂ :=
  Matrix.of fun s s' => ∑ r, η (r, s) * star (η (r, s'))

/-- Bob's compressed generator `Ŷ_B = Tr_{R_B}[(I_{H_B} ⊗ η_B)Y_B]`. -/
def compressResourceRight (η : ρA × ρB → ℂ) (Y : Matrix (ιB × ρB) (ιB × ρB) ℂ) :
    Matrix ιB ιB ℂ :=
  Matrix.of fun b b' => ∑ s, ∑ s', resourceMarginalRight η s s' * Y (b, s') (b', s)

omit [Fintype ρB] [DecidableEq ρA] [DecidableEq ρB] in
@[simp] theorem resourceMarginalRight_apply (η : ρA × ρB → ℂ) (s s' : ρB) :
    resourceMarginalRight η s s' = ∑ r, η (r, s) * star (η (r, s')) := rfl

omit [DecidableEq ρB] in
/-- **eq:shared-compression for Bob** (the "analogous formula holds for Bob"
clause of snapshot L603). -/
theorem compress_resource_ampRight (η : ρA × ρB → ℂ)
    (Y : Matrix (ιB × ρB) (ιB × ρB) ℂ) :
    (insertResource ιA ιB η)ᴴ
        * ampRight (ιA × ρA) (ιB × ρB) Y * insertResource ιA ιB η
      = ampRight ιA ιB (compressResourceRight η Y) := by
  ext q q'
  rw [Matrix.mul_assoc, insertResource_conjTranspose_mul_apply]
  simp only [mul_insertResource_apply, ampRight_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, compressResourceRight, Matrix.of_apply,
    resourceMarginalRight_apply, Prod.mk.injEq]
  by_cases ha : q.1 = q'.1
  · simp only [ha, true_and, ite_mul, zero_mul, one_mul]
    have collapse : ∀ (r : ρA) (s : ρB),
        (∑ r' : ρA, ∑ s' : ρB,
            (if r = r' then Y (q.2, s) (q'.2, s') * η (r', s') else 0))
          = ∑ s', Y (q.2, s) (q'.2, s') * η (r, s') := by
      intro r s
      rw [Finset.sum_comm]
      simp
    simp only [collapse]
    have hL : (∑ r, ∑ s, star (η (r, s)) * ∑ s', Y (q.2, s) (q'.2, s') * η (r, s'))
        = ∑ a, ∑ b, ∑ c, star (η (a, b)) * Y (q.2, b) (q'.2, c) * η (a, c) := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    have hR : (∑ s, ∑ s', (∑ r, η (r, s) * star (η (r, s'))) * Y (q.2, s') (q'.2, s))
        = ∑ a, ∑ b, ∑ c, star (η (a, b)) * Y (q.2, b) (q'.2, c) * η (a, c) := by
      rw [show (∑ s, ∑ s', (∑ r, η (r, s) * star (η (r, s'))) * Y (q.2, s') (q'.2, s))
          = ∑ b, ∑ c, ∑ a, star (η (a, c)) * Y (q.2, c) (q'.2, b) * η (a, b) from
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by ring]
      rw [sum_rotate]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    rw [hL, hR]
    simp
  · simp [ha]

omit [Fintype ιB] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB] in
/-- Bob's compression preserves anti-Hermitian generators. -/
theorem compressResourceRight_conjTranspose (η : ρA × ρB → ℂ)
    (Y : Matrix (ιB × ρB) (ιB × ρB) ℂ) :
    compressResourceRight η Yᴴ = (compressResourceRight η Y)ᴴ := by
  ext b b'
  simp only [compressResourceRight, Matrix.of_apply, Matrix.conjTranspose_apply,
    star_sum, star_mul, resourceMarginalRight_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun t _ => by rw [star_star, mul_comm]

omit [Fintype ιB] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB] in
theorem compressResourceRight_neg (η : ρA × ρB → ℂ)
    (Y : Matrix (ιB × ρB) (ιB × ρB) ℂ) :
    compressResourceRight η (-Y) = -compressResourceRight (ιB := ιB) η Y := by
  ext b b'
  simp [compressResourceRight, ← Finset.sum_neg_distrib]

omit [DecidableEq ρB] in
/-- Bob's payoff clause: an anti-Hermitian Bob-local generator also
compresses into `𝔤_{A:B}`. -/
theorem compress_resource_right_mem_localSkew (η : ρA × ρB → ℂ)
    {Y : Matrix (ιB × ρB) (ιB × ρB) ℂ} (hY : Yᴴ = -Y) :
    (insertResource ιA ιB η)ᴴ
        * ampRight (ιA × ρA) (ιB × ρB) Y * insertResource ιA ιB η
      ∈ localSkew ιA ιB := by
  rw [compress_resource_ampRight]
  refine Submodule.mem_sup_right ⟨compressResourceRight η Y, ?_, rfl⟩
  show compressResourceRight η Y ∈ skewHermitian ιB
  rw [mem_skewHermitian_iff, ← compressResourceRight_conjTranspose, hY,
    compressResourceRight_neg]

end SharedState

section FlagCompression

variable {δ εA εB : Type*} [Fintype δ] [Fintype εA] [Fintype εB]
variable [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]

/-- **eq:flag-isometry** (snapshot L605-611): `C_ω|i⟩ = |i⟩_{O_A}|i⟩_{O_B}|ω_i⟩`,
with the two coherent copies of the outcome label held by the two
laboratories. -/
def flagIsometry (ω : δ → εA × εB → ℂ) : Matrix ((δ × εA) × (δ × εB)) δ ℂ :=
  Matrix.of fun p i =>
    (if p.1.1 = i then 1 else 0) * (if p.2.1 = i then 1 else 0) * ω i (p.1.2, p.2.2)

omit [Fintype δ] [Fintype εA] [Fintype εB] [DecidableEq εA] [DecidableEq εB] in
@[simp] theorem flagIsometry_apply (ω : δ → εA × εB → ℂ)
    (p : (δ × εA) × (δ × εB)) (i : δ) :
    flagIsometry ω p i
      = (if p.1.1 = i then 1 else 0) * (if p.2.1 = i then 1 else 0)
          * ω i (p.1.2, p.2.2) := rfl

omit [Fintype δ] [Fintype εA] [Fintype εB] [DecidableEq εA] [DecidableEq εB] in
/-- `C_ω` is additive in the flag vectors.  The mirror of
`NLQCLean.insertResource_add`; together with `NLQCLean.flagIsometry_smul` it
makes `ω ↦ C_ω` a linear map, hence differentiable through
`NLQCLean.HasDerivAt.ofLinearMap`. -/
theorem flagIsometry_add (ω θ : δ → εA × εB → ℂ) :
    flagIsometry (ω + θ) = flagIsometry ω + flagIsometry θ := by
  ext p i
  simp only [Matrix.add_apply, flagIsometry_apply, Pi.add_apply]
  ring

omit [Fintype δ] [Fintype εA] [Fintype εB] [DecidableEq εA] [DecidableEq εB] in
/-- `C_ω` is homogeneous in the flag vectors. -/
theorem flagIsometry_smul (c : ℂ) (ω : δ → εA × εB → ℂ) :
    flagIsometry (c • ω) = c • flagIsometry ω := by
  ext p i
  simp only [Matrix.smul_apply, flagIsometry_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq εA] [DecidableEq εB] in
/-- `C_ω` is an isometry when every `ω_i` is a unit vector.  Unlike `J_η`, the
flag isometry carries no unit-norm side condition in its definition, so the
hypothesis is explicit.  `prop:exact-velocity` needs this to know that
`B = Dec† C_ω` is an isometry (snapshot L820-824).

Instance of `NLQCLean.isIsometry_of_unit_columns`: the block label of a row
`p` is the pair of *outcome labels* `(p.1.1, p.2.1)`, the columns sit on the
diagonal blocks `i ↦ (i, i)`, and the within-block label is the pair of
environments. -/
theorem isIsometry_flagIsometry (ω : δ → εA × εB → ℂ)
    (hω : ∀ i, IsUnitVector (ω i)) : IsIsometry (flagIsometry ω) := by
  refine isIsometry_of_unit_columns (Equiv.prodProdProdComm δ εA δ εB)
    (fun i => (i, i)) (fun a b h => congrArg Prod.fst h) ω hω ?_
  intro p i
  rw [flagIsometry_apply]
  by_cases h1 : p.1.1 = i <;> by_cases h2 : p.2.1 = i <;>
    simp [Equiv.prodProdProdComm_apply, Prod.ext_iff, h1, h2]

omit [DecidableEq εA] in
/-- **Part (ii)** (snapshot L612-614): compression of an Alice-local generator
through the flag isometry is **diagonal**.  This is the only source of the
diagonal output algebra `𝔱^D` in the PVM branch, and the proof is exactly the
paper's: the `(i,j)` entry carries the factor `⟨i|j⟩_{O_B}` from Bob's
untouched label copy. -/
theorem flag_compression_mem_diagonal (ω : δ → εA × εB → ℂ)
    (Z : Matrix (δ × εA) (δ × εA) ℂ) :
    (flagIsometry ω)ᴴ * ampLeft (δ × εA) (δ × εB) Z * flagIsometry ω
      ∈ diagonalSubmodule δ := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun p' _ => ?_
  rcases eq_or_ne p'.2.1 j with hj | hj
  · rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun p _ => ?_
    rcases eq_or_ne p.2 p'.2 with h2 | h2
    · have hne : ¬ (p.2.1 = i) := by
        rw [h2, hj]; exact fun h => hij h.symm
      simp [flagIsometry, hne]
    · simp [ampLeft_apply, Matrix.kroneckerMap_apply, h2]
  · simp [flagIsometry, hj]

omit [DecidableEq εB] in
/-- **Part (ii) with the parties interchanged** (snapshot L614): the same
compression through the flag isometry is diagonal for a Bob-local generator,
now because the `(i,j)` entry carries `⟨i|j⟩_{O_A}` from Alice's untouched
label copy. -/
theorem flag_compression_right_mem_diagonal (ω : δ → εA × εB → ℂ)
    (Z : Matrix (δ × εB) (δ × εB) ℂ) :
    (flagIsometry ω)ᴴ * ampRight (δ × εA) (δ × εB) Z * flagIsometry ω
      ∈ diagonalSubmodule δ := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun p' _ => ?_
  rcases eq_or_ne p'.1.1 j with hj | hj
  · rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun p _ => ?_
    rcases eq_or_ne p.1 p'.1 with h1 | h1
    · have hne : ¬ (p.1.1 = i) := by
        rw [h1, hj]; exact fun h => hij h.symm
      simp [flagIsometry, hne]
    · simp [ampRight_apply, Matrix.kroneckerMap_apply, h1]
  · simp [flagIsometry, hj]

end FlagCompression

section DecoderSupport

variable {κA κB ν : Type*} [Fintype κA] [Fintype κB] [Fintype ν]
variable [DecidableEq κA] [DecidableEq κB]

omit [Fintype κA] [Fintype κB] [DecidableEq κA] [DecidableEq κB] in
/-- The range projection of a product decoder factorizes. -/
theorem decoder_rangeProj {μA μB : Type*} [Fintype μA] [Fintype μB]
    (DA : Matrix κA μA ℂ) (DB : Matrix κB μB ℂ) :
    (DA ⊗ₖ DB) * (DA ⊗ₖ DB)ᴴ = (DA * DAᴴ) ⊗ₖ (DB * DBᴴ) := by
  rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul]

omit [Fintype ν] [DecidableEq κA] in
/-- **Part (iii)** (snapshot L616-620).  If the range of `G` lies in the range
of the product decoder, then either single-laboratory decoder projection
already fixes `G`; the unvaried laboratory's projection may be dropped. -/
theorem rangeProj_left_mul_eq {PA : Matrix κA κA ℂ} {PB : Matrix κB κB ℂ}
    {G : Matrix (κA × κB) ν ℂ} (hA : PA * PA = PA) (_hB : PB * PB = PB)
    (hG : (PA ⊗ₖ PB) * G = G) :
    (PA ⊗ₖ (1 : Matrix κB κB ℂ)) * G = G := by
  conv_lhs => rw [← hG]
  rw [← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, hA, Matrix.one_mul, hG]

omit [Fintype ν] [DecidableEq κB] in
theorem rangeProj_right_mul_eq {PA : Matrix κA κA ℂ} {PB : Matrix κB κB ℂ}
    {G : Matrix (κA × κB) ν ℂ} (_hA : PA * PA = PA) (hB : PB * PB = PB)
    (hG : (PA ⊗ₖ PB) * G = G) :
    ((1 : Matrix κA κA ℂ) ⊗ₖ PB) * G = G := by
  conv_lhs => rw [← hG]
  rw [← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, hB, Matrix.one_mul, hG]

end DecoderSupport


end NLQCLean
