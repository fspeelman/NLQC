import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# Singular-value bounds from a low-rank part and a small residual

Mathlib's singular values are zero-indexed.  Thus a map which is
the sum of a rank-at-most `t` map and a residual of norm at most `μ` has its
singular value at index `t` bounded by `μ`.
-/

namespace NLQCLean

open Module
open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

private theorem singularValues_mul_norm_le_of_mem_initialSpan
    (L : E →L[ℝ] F) {n t : ℕ} (hn : finrank ℝ E = n) (ht : t < n)
    {x : E}
    (hx : x ∈ Submodule.span ℝ (Set.range fun i : Fin (t + 1) ↦
      (L.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis hn)
        ⟨i, i.isLt.trans_le (Nat.succ_le_iff.mpr ht)⟩)) :
    L.toLinearMap.singularValues t * ‖x‖ ≤ ‖L x‖ := by
  let A : E →ₗ[ℝ] E := L.toLinearMap.adjoint ∘ₗ L.toLinearMap
  let hA := L.toLinearMap.isSymmetric_adjoint_comp_self
  let b : OrthonormalBasis (Fin n) ℝ E := hA.eigenvectorBasis hn
  let q : Fin (t + 1) → Fin n := fun i ↦
    ⟨i, i.isLt.trans_le (Nat.succ_le_iff.mpr ht)⟩
  have hcoeff (j : Fin n) (hj : t < j) : b.repr x j = 0 := by
    rw [b.repr_apply_apply]
    have hker : Submodule.span ℝ (Set.range fun i : Fin (t + 1) ↦ b (q i)) ≤
        LinearMap.ker (innerSL ℝ (b j)).toLinearMap := by
      rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      change inner ℝ (b j) (b (q i)) = 0
      exact b.inner_eq_zero (by
        intro hji
        have := congrArg Fin.val hji
        dsimp only [q] at this
        omega)
    exact hker (by simpa only [b, q] using hx)
  have hinner : ‖L x‖ ^ 2 =
      ∑ i : Fin n, hA.eigenvalues hn i * (b.repr x i) ^ 2 := by
    calc
      ‖L x‖ ^ 2 = inner ℝ (A x) x := by
        dsimp only [A]
        rw [ContinuousLinearMap.adjoint_toLinearMap]
        simpa using ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left L x
      _ = ∑ i : Fin n, inner ℝ (A x) (b i) * inner ℝ (b i) x :=
        (b.sum_inner_mul_inner (A x) x).symm
      _ = ∑ i : Fin n, hA.eigenvalues hn i * (b.repr x i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [b]
        rw [hA x (b i), hA.apply_eigenvectorBasis hn]
        simp only [inner_smul_right]
        have hre : inner ℝ x ((hA.eigenvectorBasis hn) i) =
            (hA.eigenvectorBasis hn).repr x i := by
          rw [real_inner_comm]
          exact ((hA.eigenvectorBasis hn).repr_apply_apply x i).symm
        have hre' : inner ℝ ((hA.eigenvectorBasis hn) i) x =
            (hA.eigenvectorBasis hn).repr x i :=
          ((hA.eigenvectorBasis hn).repr_apply_apply x i).symm
        rw [hre, hre']
        simp only [RCLike.ofReal_real_eq_id, id_eq]
        ring
  have hsum : hA.eigenvalues hn ⟨t, ht⟩ * ∑ i : Fin n, (b.repr x i) ^ 2 ≤
      ∑ i : Fin n, hA.eigenvalues hn i * (b.repr x i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i ≤ ⟨t, ht⟩
    · exact mul_le_mul_of_nonneg_right (hA.eigenvalues_antitone hn hi) (sq_nonneg _)
    · have hitFin : (⟨t, ht⟩ : Fin n) < i := lt_of_not_ge hi
      have hit : t < i := hitFin
      simp [hcoeff i hit]
  have hnorm : ∑ i : Fin n, (b.repr x i) ^ 2 = ‖x‖ ^ 2 := by
    rw [← EuclideanSpace.real_norm_sq_eq (b.repr x)]
    exact congrArg (fun z : ℝ ↦ z ^ 2) (b.repr.norm_map x)
  rw [← L.toLinearMap.sq_singularValues_of_lt hn ht, hnorm] at hsum
  apply (sq_le_sq₀
    (mul_nonneg (L.toLinearMap.singularValues_nonneg t) (norm_nonneg x))
    (norm_nonneg (L x))).mp
  simpa only [mul_pow] using hsum.trans_eq hinner.symm

/-- The leading singular value is bounded by the operator norm. -/
theorem singularValues_zero_le_norm (L : E →L[ℝ] F) :
    L.toLinearMap.singularValues 0 ≤ ‖L‖ := by
  by_cases hE : finrank ℝ E = 0
  · rw [L.toLinearMap.singularValues_of_finrank_le (by simp [hE])]
    exact L.opNorm_nonneg
  have h0 : 0 < finrank ℝ E := Nat.pos_of_ne_zero hE
  let hA := L.toLinearMap.isSymmetric_adjoint_comp_self
  let b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E := hA.eigenvectorBasis rfl
  let x : E := b ⟨0, h0⟩
  have hxnorm : ‖x‖ = 1 := b.norm_eq_one ⟨0, h0⟩
  have hlower : L.toLinearMap.singularValues 0 ≤ ‖L x‖ := by
    have hxspan : x ∈ Submodule.span ℝ
        (Set.range fun i : Fin (0 + 1) ↦ b ⟨i, i.isLt.trans_le h0⟩) := by
      apply Submodule.subset_span
      exact ⟨⟨0, by omega⟩, rfl⟩
    simpa only [hxnorm, mul_one, b, x] using
      singularValues_mul_norm_le_of_mem_initialSpan L rfl h0 hxspan
  have happly : ‖L x‖ ≤ ‖L‖ := by simpa only [hxnorm, mul_one] using L.le_opNorm x
  exact hlower.trans happly

/-- A rank-at-most `t` summand can affect only the first `t` zero-indexed
singular values; the next singular value is controlled by the residual. -/
theorem singularValues_le_of_eq_add_of_finrank_range_le
    (L T R : E →L[ℝ] F) {t : ℕ} { μ : ℝ }
    (hL : L = T + R)
    (ht : finrank ℝ T.toLinearMap.range ≤ t)
    (hR : ‖R‖ ≤ μ) (hμ : 0 ≤ μ) :
    L.toLinearMap.singularValues t ≤ μ := by
  by_cases hdim : finrank ℝ E ≤ t
  · rw [L.toLinearMap.singularValues_of_finrank_le hdim]
    exact hμ
  have hit : t < finrank ℝ E := Nat.lt_of_not_ge hdim
  let hA := L.toLinearMap.isSymmetric_adjoint_comp_self
  let b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E := hA.eigenvectorBasis rfl
  let q : Fin (t + 1) → Fin (finrank ℝ E) := fun i ↦
    ⟨i, i.isLt.trans_le (Nat.succ_le_iff.mpr hit)⟩
  let V : Submodule ℝ E := Submodule.span ℝ (Set.range fun i : Fin (t + 1) ↦ b (q i))
  have hq : Function.Injective q := by
    intro i j hij
    apply Fin.ext
    have hv : (q i).val = (q j).val :=
      congrArg (fun k : Fin (finrank ℝ E) ↦ k.val) hij
    simpa only [q] using hv
  have hlin : LinearIndependent ℝ (fun i : Fin (t + 1) ↦ b (q i)) := by
    have horth : Orthonormal ℝ (fun i : Fin (t + 1) ↦ b (q i)) := by
      constructor
      · intro i
        exact b.norm_eq_one (q i)
      · intro i j hij
        exact b.inner_eq_zero (fun h => hij (hq h))
    exact horth.linearIndependent
  have hdimV : finrank ℝ V = t + 1 := by
    simpa only [V, Fintype.card_fin] using finrank_span_eq_card hlin
  let f : V →ₗ[ℝ] T.toLinearMap.range :=
    T.toLinearMap.rangeRestrict.domRestrict V
  have htarget : finrank ℝ T.toLinearMap.range < finrank ℝ V := by omega
  have hk : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt htarget
  obtain ⟨x, hxker, hx0⟩ := (LinearMap.ker f).ne_bot_iff.mp hk
  have hxE0 : (x : E) ≠ 0 := by
    intro hx
    apply hx0
    exact Subtype.ext hx
  have hTx : T x = 0 := by
    have hfx : f x = 0 := LinearMap.mem_ker.mp hxker
    simpa [f] using congrArg Subtype.val hfx
  have hxspan : (x : E) ∈ Submodule.span ℝ
      (Set.range fun i : Fin (t + 1) ↦ b (q i)) := x.property
  have hlower : L.toLinearMap.singularValues t * ‖(x : E)‖ ≤ ‖L x‖ := by
    simpa only [b, q] using
      singularValues_mul_norm_le_of_mem_initialSpan L rfl hit hxspan
  have hLx : L x = R x := by simp [hL, hTx]
  have hupper : ‖L x‖ ≤ μ * ‖(x : E)‖ := by
    rw [hLx]
    exact (R.le_opNorm x).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hxnorm : 0 < ‖(x : E)‖ := norm_pos_iff.mpr hxE0
  by_contra htail
  have hstrict : μ < L.toLinearMap.singularValues t := lt_of_not_ge htail
  have hs := mul_lt_mul_of_pos_right hstrict hxnorm
  exact (not_lt_of_ge hupper) (hs.trans_le hlower)

end NLQCLean
