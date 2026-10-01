/-
The Schmidt-transcript footprint `K = R m_A m_B` and the mixed-resource model.
-/
import NLQCLean.Models.OneRound
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The finite footprint and mixed resources

The footprint and mixed resources supplement the one-round architecture
in `NLQCLean.Models.OneRound`.

## The footprint (snapshot L545-554)

"Let the resource have Schmidt number at most `R`, and let the two complete
outgoing messages have dimensions at most `m_A, m_B`.  We call
`K = R m_A m_B` (**eq:K-footprint**) the *Schmidt--transcript footprint*.  A
protocol of footprint at most `K` may choose any factorization
`R m_A m_B ≤ K`."

That last sentence is why `NLQCLean.HasFootprint` is an *existential over
factorizations* and not an equation. Every bound in the paper is "at most",
so all four comparisons are `≤`.

### `R` is not a register dimension

`NLQCLean.schmidtRank` is the rank of the *reshaped coefficient matrix* of
the resource vector, which is the paper's `SR` across the `R_A : R_B` cut
(snapshot L1204, L1214).  It is emphatically **not** `Fintype.card ρA`: the
resource lives on `R_A ⊗ R_B` of arbitrary finite dimension and only its
Schmidt rank is charged.  That a Schmidt-rank-`R` resource may be *replaced*
by one supported on `ℂ^R ⊗ ℂ^R` is the conclusion of
`lem:reachable-compression` (L963-965 in the proof of
`thm:fixed-R-localization`), rather than a modelling convention.
The message registers `μA`, `μB`
are kept as abstract finite types with `Fintype.card μX ≤ m_X`, rather than
being defined as `Fin m_X`.

## Mixed resources (snapshot L465-472, L927-929)

"A mixed resource of Schmidt number at most `R` is a convex combination of
pure states of Schmidt rank at most `R`" (L465-467), and "a decomposition of
the resource gives a convex decomposition of the induced channel"
(L927-929).  `NLQCLean.MixedResource` and
`NLQCLean.MixedResource.mixedChannel` are exactly those two sentences.  The
encoders, the decoders and the exchange permutation are shared across the
components; only the resource vector varies, as in the paper.

The mixed channel is `Σ_k w_k channelOf(F(η_k))`, with the same local maps
in every component.
-/

namespace NLQCLean

open Matrix

section SchmidtRank

variable {ρA ρB : Type*} [Fintype ρA] [Fintype ρB]

/-- The reshaped coefficient matrix of a bipartite resource vector:
`η = Σ_{r,s} η(r,s) |r⟩|s⟩` becomes the matrix `C_{rs} = η(r,s)`. -/
def resourceMatrix (η : ρA × ρB → ℂ) : Matrix ρA ρB ℂ := Matrix.of fun r s => η (r, s)

omit [Fintype ρA] [Fintype ρB] in
@[simp] theorem resourceMatrix_apply (η : ρA × ρB → ℂ) (r : ρA) (s : ρB) :
    resourceMatrix η r s = η (r, s) := rfl

/-- The **Schmidt rank** of a pure bipartite resource across the `R_A : R_B`
cut (snapshot L1204, L1214: `SR`), as the rank of the reshaped coefficient
matrix.  This is the `R` of eq:K-footprint, and it is a property of the
vector, not of the register dimensions. -/
noncomputable def schmidtRank (η : ρA × ρB → ℂ) : ℕ := (resourceMatrix η).rank

theorem schmidtRank_le_card_left (η : ρA × ρB → ℂ) :
    schmidtRank η ≤ Fintype.card ρA :=
  Matrix.rank_le_card_height _

omit [Fintype ρA] in
theorem schmidtRank_le_card_right (η : ρA × ρB → ℂ) :
    schmidtRank η ≤ Fintype.card ρB :=
  Matrix.rank_le_card_width _

omit [Fintype ρA] [Fintype ρB] in
/-- Exchanging the two laboratories transposes the coefficient matrix. -/
theorem resourceMatrix_swap (η : ρA × ρB → ℂ) :
    resourceMatrix (fun p : ρB × ρA => η (p.2, p.1)) = (resourceMatrix η)ᵀ := rfl

/-- **Laboratory symmetry of the Schmidt rank.**  The `R` of eq:K-footprint
does not depend on which laboratory is called `A`.  This is what makes the
`A`/`B` symmetry of the later resource statements free. -/
theorem schmidtRank_swap (η : ρA × ρB → ℂ) :
    schmidtRank (fun p : ρB × ρA => η (p.2, p.1)) = schmidtRank η := by
  rw [schmidtRank, resourceMatrix_swap, Matrix.rank_transpose, schmidtRank]

end SchmidtRank

section Linearity

variable {ρA ρB ιA ιB : Type*} [DecidableEq ιA] [DecidableEq ιB]

/-- `J_η` is additive in the resource vector. -/
theorem insertResource_add (η θ : ρA × ρB → ℂ) :
    insertResource ιA ιB (η + θ)
      = insertResource ιA ιB η + insertResource ιA ιB θ := by
  ext p q
  simp only [Matrix.add_apply, insertResource_apply, Pi.add_apply]
  ring

/-- `J_η` is homogeneous in the resource vector. -/
theorem insertResource_smul (c : ℂ) (η : ρA × ρB → ℂ) :
    insertResource ιA ιB (c • η) = c • insertResource ιA ιB η := by
  ext p q
  simp only [Matrix.smul_apply, insertResource_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Linearity

section Footprint

variable {ρA ρB : Type*} [Fintype ρA] [Fintype ρB]

/-- **eq:K-footprint** (snapshot L545-554).  The pure resource `η` together
with the two outgoing message registers `M_A`, `M_B` has *Schmidt-transcript
footprint at most `K`* when some factorization `R m_A m_B ≤ K` dominates the
Schmidt rank of the resource and the two message dimensions.

The existential is the paper's "a protocol of footprint at most `K` may
choose any factorization `R m_A m_B ≤ K`" (L552-554), and all four
comparisons are `≤` because the paper says "at most" throughout (L546-548).

Note what is *not* said: nothing here constrains `Fintype.card ρA`, the
dimension of the resource register.  Only the Schmidt rank is charged.  The
private workspaces `K_A`, `K_B`, `E_A`, `E_B` are not charged either, per
L554-557. -/
def HasFootprint (K : ℕ) (η : ρA × ρB → ℂ) (μA μB : Type*)
    [Fintype μA] [Fintype μB] : Prop :=
  ∃ R mA mB : ℕ, R * mA * mB ≤ K ∧ schmidtRank η ≤ R ∧
    Fintype.card μA ≤ mA ∧ Fintype.card μB ≤ mB

variable {μA μB : Type*} [Fintype μA] [Fintype μB]

omit [Fintype ρA] in
/-- The existential over factorizations is equivalent to the single tight
inequality obtained by taking the smallest admissible `R`, `m_A`, `m_B`.
This gives a direct form of eq:K-footprint. -/
theorem hasFootprint_iff (K : ℕ) (η : ρA × ρB → ℂ) :
    HasFootprint K η μA μB
      ↔ schmidtRank η * Fintype.card μA * Fintype.card μB ≤ K := by
  constructor
  · rintro ⟨R, mA, mB, hK, hR, hA, hB⟩
    exact le_trans (Nat.mul_le_mul (Nat.mul_le_mul hR hA) hB) hK
  · intro h
    exact ⟨schmidtRank η, Fintype.card μA, Fintype.card μB, h, le_rfl, le_rfl, le_rfl⟩

omit [Fintype ρA] in
/-- A larger footprint budget is a weaker constraint. -/
theorem HasFootprint.mono {K K' : ℕ} {η : ρA × ρB → ℂ}
    (h : HasFootprint K η μA μB) (hKK' : K ≤ K') : HasFootprint K' η μA μB := by
  obtain ⟨R, mA, mB, hK, hR, hA, hB⟩ := h
  exact ⟨R, mA, mB, hK.trans hKK', hR, hA, hB⟩

/-- The footprint does not depend on which laboratory is called `A`
(snapshot L545-552 is symmetric in `A` and `B`).  Immediate from
`NLQCLean.schmidtRank_swap`. -/
theorem hasFootprint_swap (K : ℕ) (η : ρA × ρB → ℂ) :
    HasFootprint K (fun p : ρB × ρA => η (p.2, p.1)) μB μA
      ↔ HasFootprint K η μA μB := by
  have hcomm : schmidtRank η * Fintype.card μB * Fintype.card μA
      = schmidtRank η * Fintype.card μA * Fintype.card μB := by ring
  rw [hasFootprint_iff, hasFootprint_iff, schmidtRank_swap, hcomm]

end Footprint

section ProtocolFootprint

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

/-- A pure-resource protocol has footprint at most `K` when its resource and
its two message registers do (eq:K-footprint, snapshot L545-554). -/
def PureProtocol.HasFootprint
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB) (K : ℕ) : Prop :=
  NLQCLean.HasFootprint K P.resource μA μB

end ProtocolFootprint

section Mixed

/-- A **mixed resource** with `n` components (snapshot L465-467): "a convex
combination of pure states".  Only the resource is mixed; the architecture
around it is shared by all components, as in the paper's componentwise
reduction (L432-433, L925-931). -/
structure MixedResource (ρA ρB : Type*) [Fintype ρA] [Fintype ρB] (n : ℕ) where
  /-- The convex weights. -/
  weight : Fin n → ℝ
  /-- The weights are nonnegative. -/
  weight_nonneg : ∀ k, 0 ≤ weight k
  /-- The weights sum to one. -/
  weight_sum : ∑ k, weight k = 1
  /-- The pure components `η_k ∈ R_A ⊗ R_B`. -/
  component : Fin n → (ρA × ρB → ℂ)
  /-- Each component is a unit vector (snapshot L449). -/
  component_unit : ∀ k, IsUnitVector (component k)

namespace MixedResource

variable {ρA ρB : Type*} [Fintype ρA] [Fintype ρB]
variable {n : ℕ}

/-- **Schmidt number at most `R`** (snapshot L465-467): a convex combination
of pure states *each* of Schmidt rank at most `R`.  The quantifier is over
the components of the given decomposition, exactly as the paper's definition
reads; this is the quantity `thm:fixed-R-localization` (L951-959) fixes. -/
def schmidtNumberLE (m : MixedResource ρA ρB n) (R : ℕ) : Prop :=
  ∀ k, schmidtRank (m.component k) ≤ R

theorem schmidtNumberLE.mono {m : MixedResource ρA ρB n} {R R' : ℕ}
    (h : m.schmidtNumberLE R) (hRR' : R ≤ R') : m.schmidtNumberLE R' :=
  fun k => (h k).trans hRR'

variable {ιA ιB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype ιA'] [Fintype ιB']
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq ιA'] [DecidableEq ιB']
variable [DecidableEq εA] [DecidableEq εB]

/-- **The channel of a mixed resource** (snapshot L927-929): "a decomposition
of the resource gives a convex decomposition of the induced channel".  The
encoders, decoders and exchange permutation are shared; only `η` varies.

The mixed state `Σ_k w_k |η_k⟩⟨η_k|` induces the channel
`Σ_k w_k channelOf(F(η_k))`. -/
def mixedChannel (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix (ιA' × ιB') (ιA' × ιB') ℂ :=
  ∑ k, ((m.weight k : ℂ)) • operationalChannel (m.component k) VA VB DA DB

omit [Fintype ιA'] [Fintype ιB'] [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB] in
theorem mixedChannel_apply (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (ρ : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    m.mixedChannel VA VB DA DB ρ
      = ∑ k, ((m.weight k : ℂ)) • operationalChannel (m.component k) VA VB DA DB ρ := by
  rw [mixedChannel]
  simp

omit [Fintype ιA'] [Fintype ιB'] [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB] in
/-- A mixed resource with a single component is that pure component, and its
mixed channel is the ordinary operational channel. -/
theorem mixedChannel_single (m : MixedResource ρA ρB 1)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    m.mixedChannel VA VB DA DB
      = operationalChannel (m.component 0) VA VB DA DB := by
  have hw : (m.weight 0 : ℂ) = 1 := by
    have := m.weight_sum
    rw [Fin.sum_univ_one] at this
    rw [this, Complex.ofReal_one]
  rw [mixedChannel, Fin.sum_univ_one, hw, one_smul]

end MixedResource

end Mixed

end NLQCLean
