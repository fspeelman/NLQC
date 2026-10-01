/-
The allowed tangent space of the cross-Gram lemma.
-/
import NLQCLean.LinearAlgebra.Isometry
import Mathlib.Algebra.Star.Module
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Allowed tangent spaces

`lem:cross-gram-rigidity` bounds the Frobenius distance from `Ḣ` to the
*allowed tangent space* (snapshot eq:allowed-tangent, L691-695)

  `E_{𝔞,𝔟}(X) = {-b X + X a : a ∈ 𝔞, b ∈ 𝔟}`,

where `𝔞` and `𝔟` are real linear spaces of anti-Hermitian matrices.  Note
the sign and side convention: `a` acts on the right of `X` and `b` on the
left, with a minus sign.  Because `𝔟` is closed under negation, the set is
the sum of the two images `X · 𝔞` and `𝔟 · X`, which is how it is defined
here; `NLQCLean.mem_allowedTangent_iff` restates it in the paper's form.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Right translation `a ↦ X * a`. -/
noncomputable def mulRightCLM (X : Matrix κ ι 𝕜) : Matrix ι ι 𝕜 →L[ℝ] Matrix κ ι 𝕜 :=
  mulCLM X

/-- Left translation `b ↦ b * X`. -/
noncomputable def mulLeftCLM (X : Matrix κ ι 𝕜) : Matrix κ κ 𝕜 →L[ℝ] Matrix κ ι 𝕜 :=
  (mulCLM (𝕜 := 𝕜)).flip X

omit [DecidableEq ι] [DecidableEq κ] in
@[simp]
theorem mulRightCLM_apply (X : Matrix κ ι 𝕜) (a : Matrix ι ι 𝕜) :
    mulRightCLM X a = X * a := rfl

omit [DecidableEq ι] [DecidableEq κ] in
@[simp]
theorem mulLeftCLM_apply (X : Matrix κ ι 𝕜) (b : Matrix κ κ 𝕜) :
    mulLeftCLM X b = b * X := rfl

/-- The allowed tangent space `E_{𝔞,𝔟}(X)` of eq:allowed-tangent (L691-695). -/
noncomputable def allowedTangent (𝔞 : Submodule ℝ (Matrix ι ι 𝕜)) (𝔟 : Submodule ℝ (Matrix κ κ 𝕜))
    (X : Matrix κ ι 𝕜) : Submodule ℝ (Matrix κ ι 𝕜) :=
  𝔞.map (mulRightCLM X).toLinearMap ⊔ 𝔟.map (mulLeftCLM X).toLinearMap

omit [DecidableEq ι] [DecidableEq κ] in
/-- Membership in the paper's form: `Y = -b X + X a` with `a ∈ 𝔞`, `b ∈ 𝔟`. -/
theorem mem_allowedTangent_iff {𝔞 : Submodule ℝ (Matrix ι ι 𝕜)}
    {𝔟 : Submodule ℝ (Matrix κ κ 𝕜)} {X : Matrix κ ι 𝕜} {Y : Matrix κ ι 𝕜} :
    Y ∈ allowedTangent 𝔞 𝔟 X ↔ ∃ a ∈ 𝔞, ∃ b ∈ 𝔟, Y = -(b * X) + X * a := by
  constructor
  · intro hY
    rw [allowedTangent, Submodule.mem_sup] at hY
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hY
    obtain ⟨a, ha, rfl⟩ := hy₁
    obtain ⟨b, hb, rfl⟩ := hy₂
    exact ⟨a, ha, -b, Submodule.neg_mem _ hb, by simp [add_comm]⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [allowedTangent, Submodule.mem_sup]
    refine ⟨X * a, ⟨a, ha, rfl⟩, -(b * X), ⟨-b, Submodule.neg_mem _ hb, by simp⟩, ?_⟩
    rw [add_comm]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The membership witness used to discharge `dist_F(Ḣ, E) ≤ …`: the paper's
conclusion eq:cross-gram-orbit-distance (L722-727) follows from the velocity
identity by exhibiting one allowed tangent vector. -/
theorem infDist_le_of_mem {S : Submodule ℝ (Matrix κ ι 𝕜)} {Y y : Matrix κ ι 𝕜}
    {c : ℝ} (hy : y ∈ S) (h : ‖Y - y‖ ≤ c) :
    Metric.infDist Y (S : Set (Matrix κ ι 𝕜)) ≤ c :=
  le_trans (Metric.infDist_le_dist_of_mem hy) (by rwa [dist_eq_norm])

end NLQCLean
