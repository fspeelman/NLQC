import NLQCLean.LinearAlgebra.CrossedSinglet
import NLQCLean.Approx.SharpFreezing
import NLQCLean.Models.ForwardReindex
import NLQCLean.Models.SwapNeighborhood
import NLQCLean.Rigidity.FlaggedSupports

/-!
# Near SWAP, both complete charged messages are large

For every pure one-round protocol on arbitrary finite
registers, every target `U ∈ S_d`, and score at least `1 − e` with `0 ≤ e ≤ 1/16`,

  `d² ≤ 2 (dim M_A)²` and `d² ≤ 2 (dim M_B)²`.

Upper bound: the crossed amplitude (Alice's reference with Bob's output, and the mirror
pair) is at most `m² d` in squared norm (`sum_normSq_crossedAmplitude_le`), using only the
isometries. Lower bound: the existing untruncated Choi projection puts the global
isometry within `d(1/4 + √(2e))` of a frozen SWAP, whose crossed amplitude is maximal; a
Cauchy–Schwarz projection argument gives at least `d³/2`. No trace-distance contract and
no bound on the preshared resource support is used.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

section Reorder7

variable {α₁ α₂ α₃ α₄ α₅ α₆ α₇ : Type*} [Fintype α₁] [Fintype α₂] [Fintype α₃] [Fintype α₄]
  [Fintype α₅] [Fintype α₆] [Fintype α₇]

theorem sum_seven_perm_alice (f : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → α₇ → ℂ) :
    ∑ r, ∑ kA, ∑ mB, ∑ kB, ∑ a, ∑ pa, ∑ pb, f r kA mB kB a pa pb =
      ∑ a, ∑ kA, ∑ mB, ∑ r, ∑ pa, ∑ kB, ∑ pb, f r kA mB kB a pa pb := by
  have h1 : ∑ r, ∑ kA, ∑ mB, ∑ kB, ∑ a, ∑ pa, ∑ pb, f r kA mB kB a pa pb =
      ∑ t : α₁ × α₂ × α₃ × α₄ × α₅ × α₆ × α₇,
        f t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  have h2 : ∑ a, ∑ kA, ∑ mB, ∑ r, ∑ pa, ∑ kB, ∑ pb, f r kA mB kB a pa pb =
      ∑ t : α₅ × α₂ × α₃ × α₁ × α₆ × α₄ × α₇,
        f t.2.2.2.1 t.2.1 t.2.2.1 t.2.2.2.2.2.1 t.1 t.2.2.2.2.1 t.2.2.2.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  rw [h1, h2]
  exact Fintype.sum_equiv
    ⟨fun t => (t.2.2.2.2.1, t.2.1, t.2.2.1, t.1, t.2.2.2.2.2.1, t.2.2.2.1, t.2.2.2.2.2.2),
      fun t => (t.2.2.2.1, t.2.1, t.2.2.1, t.2.2.2.2.2.1, t.1, t.2.2.2.2.1, t.2.2.2.2.2.2),
      fun _ => rfl, fun _ => rfl⟩ _ _ (fun _ => rfl)

theorem sum_seven_perm_bob (f : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → α₇ → ℂ) :
    ∑ r, ∑ kA, ∑ mB, ∑ kB, ∑ mA, ∑ pa, ∑ pb, f r kA mB kB mA pa pb =
      ∑ mB, ∑ kB, ∑ mA, ∑ r, ∑ pb, ∑ kA, ∑ pa, f r kA mB kB mA pa pb := by
  have h1 : ∑ r, ∑ kA, ∑ mB, ∑ kB, ∑ mA, ∑ pa, ∑ pb, f r kA mB kB mA pa pb =
      ∑ t : α₁ × α₂ × α₃ × α₄ × α₅ × α₆ × α₇,
        f t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  have h2 : ∑ mB, ∑ kB, ∑ mA, ∑ r, ∑ pb, ∑ kA, ∑ pa, f r kA mB kB mA pa pb =
      ∑ t : α₃ × α₄ × α₅ × α₁ × α₇ × α₂ × α₆,
        f t.2.2.2.1 t.2.2.2.2.2.1 t.1 t.2.1 t.2.2.1 t.2.2.2.2.2.2 t.2.2.2.2.1 := by
    simp only [Fintype.sum_prod_type]
  rw [h1, h2]
  exact Fintype.sum_equiv
    ⟨fun t => (t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.1, t.2.2.2.2.2.2, t.2.1, t.2.2.2.2.2.1),
      fun t => (t.2.2.2.1, t.2.2.2.2.2.1, t.1, t.2.1, t.2.2.1, t.2.2.2.2.2.2, t.2.2.2.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ (fun _ => rfl)

end Reorder7

section Formula

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

omit [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB] [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB] in
omit [DecidableEq ρA] [DecidableEq ρB] in
theorem encodedCore_apply (η : ρA × ρB → ℂ) (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ) (α : κA × μA) (β : κB × μB) (i : ιA) (j : ιB) :
    ((VA ⊗ₖ VB) * insertResource ιA ιB η) (α, β) (i, j) =
      ∑ pa, ∑ pb, VA α (i, pa) * VB β (j, pb) * η (pa, pb) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun pa _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun pb _ => ?_
      rw [Matrix.kronecker_apply, insertResource_apply_ite, if_pos ⟨rfl, rfl⟩]
    · intro b _ hb
      refine Finset.sum_eq_zero fun pb _ => ?_
      rw [insertResource_apply_ite, if_neg (fun h => hb h.2), mul_zero]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun pa _ => Finset.sum_eq_zero fun s _ => ?_
    rw [insertResource_apply_ite, if_neg (fun h => hb h.1), mul_zero]
  · simp

omit [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB] [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB] in
omit [DecidableEq ρA] [DecidableEq ρB] in
theorem globalIsometry_apply_expanded (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (xA : ιA' × εA) (xB : ιB' × εB) (i : ιA) (j : ιB) :
    globalIsometry η VA VB DA DB (xA, xB) (i, j) =
      ∑ p : (κA × μB) × (κB × μA), DA xA p.1 * DB xB p.2 *
        ∑ pa, ∑ pb, VA (p.1.1, p.2.2) (i, pa) * VB (p.2.1, p.1.2) (j, pb) * η (pa, pb) := by
  rw [globalIsometry_eq, Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  rintro ⟨p1, p2⟩ -
  rw [Matrix.kronecker_apply, Matrix.mul_apply,
    Finset.sum_eq_single (exchangeEquiv κA μA κB μB (p1, p2))]
  · rw [exchangeMatrix_apply, if_pos rfl, one_mul, exchangeEquiv_apply, encodedCore_apply]
  · intro q _ hq
    rw [exchangeMatrix_apply, if_neg (fun h => hq h.symm), zero_mul]
  · simp

end Formula

section CrossedVectors

variable {d : ℕ} {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]

/-- Alice's reference paired with Bob's logical output. -/
def crossedAliceVector (G : Matrix ((Fin d × E) × (Fin d × F)) (Fin d × Fin d) ℂ) :
    Fin d × ((Fin d × E) × F) → ℂ :=
  fun z => ∑ r, G (z.2.1, (r, z.2.2)) (r, z.1)

/-- Bob's reference paired with Alice's logical output. -/
def crossedBobVector (G : Matrix ((Fin d × E) × (Fin d × F)) (Fin d × Fin d) ℂ) :
    Fin d × ((Fin d × F) × E) → ℂ :=
  fun z => ∑ r, G ((r, z.2.2), z.2.1) (z.1, r)

/-- SWAP with a frozen environment vector. -/
noncomputable def frozenSwap (d : ℕ) (g : E × F → ℂ) :
    Matrix ((Fin d × E) × (Fin d × F)) (Fin d × Fin d) ℂ :=
  insertResource (Fin d) (Fin d) g * swapUnitary (Fin d)

omit [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F] in
theorem frozenSwap_apply (g : E × F → ℂ) (p : (Fin d × E) × (Fin d × F))
    (q : Fin d × Fin d) :
    frozenSwap d g p q = if p.2.1 = q.1 ∧ p.1.1 = q.2 then g (p.1.2, p.2.2) else 0 := by
  rw [frozenSwap, Matrix.mul_apply, Finset.sum_eq_single (p.1.1, p.2.1)]
  · rw [insertResource_apply_ite, if_pos ⟨rfl, rfl⟩]
    simp [swapUnitary, Matrix.one_apply, Prod.ext_iff, mul_ite]
  · intro c _ hc
    have h : ¬ (p.1.1 = c.1 ∧ p.2.1 = c.2) := fun h => hc (Prod.ext h.1.symm h.2.symm)
    rw [insertResource_apply_ite, if_neg h, zero_mul]
  · simp

omit [DecidableEq E] [DecidableEq F] in
theorem isIsometry_frozenSwap {g : E × F → ℂ} (hg : IsUnitVector g) :
    IsIsometry (frozenSwap d g) :=
  (isIsometry_insertResource g hg).mul (isIsometry_swapUnitary (Fin d))

omit [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F] in
theorem crossedAliceVector_frozenSwap (g : E × F → ℂ) (z : Fin d × ((Fin d × E) × F)) :
    crossedAliceVector (frozenSwap d g) z =
      (d : ℂ) * (if z.2.1.1 = z.1 then g (z.2.1.2, z.2.2) else 0) := by
  by_cases h : z.2.1.1 = z.1 <;> simp [crossedAliceVector, frozenSwap_apply, h]

theorem norm_sq_of_isIsometry {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n]
    {G : Matrix m n ℂ} (hG : IsIsometry G) : ‖G‖ ^ 2 = (Fintype.card n : ℝ) := by
  have h := frobInner_self_of_isometry hG
  rw [frobInner_self_eq_norm_sq] at h
  exact_mod_cast h

omit [DecidableEq E] [DecidableEq F] in
theorem sum_normSq_crossedAliceVector_frozenSwap {g : E × F → ℂ} (hg : IsUnitVector g) :
    ∑ z, Complex.normSq (crossedAliceVector (frozenSwap d g) z) = (d : ℝ) ^ 3 := by
  have hg' : ∑ e, Complex.normSq (g e) = 1 := hg
  have hd2 : Complex.normSq (d : ℂ) = (d : ℝ) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_natCast]
  have hrb : ∀ rb : Fin d, ∑ w : (Fin d × E) × F,
      Complex.normSq (if w.1.1 = rb then g (w.1.2, w.2) else 0) = 1 := by
    intro rb
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_eq_single rb]
    · show ∑ ea, ∑ y, Complex.normSq (if rb = rb then g (ea, y) else 0) = 1
      simp only [if_true]
      rw [← hg', Fintype.sum_prod_type]
    · intro b _ hb
      simp [hb]
    · simp
  simp only [crossedAliceVector_frozenSwap, Complex.normSq_mul, hd2, ← Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  rw [(Finset.sum_congr rfl fun rb _ => hrb rb).trans (by simp : ∑ _rb : Fin d, (1 : ℝ) = d)]
  ring

omit [DecidableEq E] [DecidableEq F] in
/-- The crossed projection of any `G` onto a frozen SWAP is `d` times their overlap. -/
theorem crossedAlice_inner_frozenSwap (G : Matrix ((Fin d × E) × (Fin d × F)) (Fin d × Fin d) ℂ)
    (g : E × F → ℂ) :
    ∑ z, star (crossedAliceVector (frozenSwap d g) z) * crossedAliceVector G z =
      (d : ℂ) * frobInner (frozenSwap d g) G := by
  have hL : ∑ z, star (crossedAliceVector (frozenSwap d g) z) * crossedAliceVector G z =
      (d : ℂ) * ∑ w : (Fin d × E) × F, ∑ r,
        star (g (w.1.2, w.2)) * G (w.1, (r, w.2)) (r, w.1.1) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_eq_single w.1.1]
    · rw [crossedAliceVector_frozenSwap, if_pos rfl]
      dsimp only [crossedAliceVector]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [star_mul', Complex.star_def, map_natCast]
      ring
    · intro b _ hb
      simp [crossedAliceVector_frozenSwap, Ne.symm hb]
    · simp
  have hk : ∀ k : (Fin d × E) × (Fin d × F),
      ∑ i, star (frozenSwap d g k i) * G k i = star (g (k.1.2, k.2.2)) * G k (k.2.1, k.1.1) := by
    intro k
    rw [Finset.sum_eq_single (k.2.1, k.1.1)]
    · simp [frozenSwap_apply]
    · intro i _ hi
      have h : ¬ (k.2.1 = i.1 ∧ k.1.1 = i.2) := fun h => hi (Prod.ext h.1.symm h.2.symm)
      rw [frozenSwap_apply, if_neg h, star_zero, zero_mul]
    · simp
  have hR : frobInner (frozenSwap d g) G = ∑ w : (Fin d × E) × F, ∑ r,
      star (g (w.1.2, w.2)) * G (w.1, (r, w.2)) (r, w.1.1) := by
    rw [frobInner]
    simp only [hk]
    rw [Fintype.sum_prod_type]
    conv_rhs => rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hL, hR]

/-- Lower bound: a global isometry close to a frozen SWAP has a large crossed amplitude. -/
theorem crossedAlice_lower (hd : 0 < d)
    {G : Matrix ((Fin d × E) × (Fin d × F)) (Fin d × Fin d) ℂ} (hG : IsIsometry G)
    {g : E × F → ℂ} (hg : IsUnitVector g) {t : ℝ} (_ht : 0 ≤ t) (ht2 : t ^ 2 ≤ 2)
    (hclose : ‖G - frozenSwap d g‖ ≤ t * d) :
    (d : ℝ) ^ 3 * (1 - t ^ 2 / 2) ^ 2 ≤ ∑ z, Complex.normSq (crossedAliceVector G z) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcard : (Fintype.card (Fin d × Fin d) : ℝ) = (d : ℝ) ^ 2 := by
    simp [Fintype.card_prod, Fintype.card_fin, sq]
  have hGn : ‖G‖ ^ 2 = (d : ℝ) ^ 2 := (norm_sq_of_isIsometry hG).trans hcard
  have hVn : ‖frozenSwap d g‖ ^ 2 = (d : ℝ) ^ 2 :=
    (norm_sq_of_isIsometry (isIsometry_frozenSwap hg)).trans hcard
  have hre : (d : ℝ) ^ 2 * (1 - t ^ 2 / 2) ≤ (frobInner (frozenSwap d g) G).re := by
    have h := frobNorm_sub_sq G (frozenSwap d g)
    have hc : ‖G - frozenSwap d g‖ ^ 2 ≤ (t * d) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hclose 2
    nlinarith
  set S := ∑ z, Complex.normSq (crossedAliceVector G z) with hS
  have hA := crossedAlice_inner_frozenSwap G g
  have hV3 := sum_normSq_crossedAliceVector_frozenSwap (d := d) hg
  have hCS : ‖∑ z, star (crossedAliceVector (frozenSwap d g) z) * crossedAliceVector G z‖ ^ 2 ≤
      (d : ℝ) ^ 3 * S := by
    have h1 : ‖∑ z, star (crossedAliceVector (frozenSwap d g) z) * crossedAliceVector G z‖ ≤
        ∑ z, ‖crossedAliceVector (frozenSwap d g) z‖ * ‖crossedAliceVector G z‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun z _ => by
        rw [norm_mul, norm_star]))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun z => ‖crossedAliceVector (frozenSwap d g) z‖) (fun z => ‖crossedAliceVector G z‖)
    simp only [Complex.normSq_eq_norm_sq] at hV3 hS
    calc _ ≤ (∑ z, ‖crossedAliceVector (frozenSwap d g) z‖ * ‖crossedAliceVector G z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ = _ := by rw [hV3, hS]
  have hlow : (d : ℝ) ^ 3 * (1 - t ^ 2 / 2) ≤
      ‖∑ z, star (crossedAliceVector (frozenSwap d g) z) * crossedAliceVector G z‖ := by
    rw [hA, norm_mul, Complex.norm_natCast]
    have h := Complex.re_le_norm (frobInner (frozenSwap d g) G)
    have hd0 : (0 : ℝ) ≤ d := hdR.le
    nlinarith
  have hpos : 0 ≤ (d : ℝ) ^ 3 * (1 - t ^ 2 / 2) := by
    have : 0 ≤ 1 - t ^ 2 / 2 := by linarith
    positivity
  have hsq := (pow_le_pow_left₀ hpos hlow 2).trans hCS
  have hd3 : (0 : ℝ) < (d : ℝ) ^ 3 := by positivity
  refine le_of_mul_le_mul_left ?_ hd3
  calc (d : ℝ) ^ 3 * ((d : ℝ) ^ 3 * (1 - t ^ 2 / 2) ^ 2) = ((d : ℝ) ^ 3 * (1 - t ^ 2 / 2)) ^ 2 := by
        ring
    _ ≤ _ := hsq

omit [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F] in
/-- Exchanging the parties turns the Bob crossed pair into the Alice crossed pair. -/
theorem crossedBobVector_eq (G : Matrix ((Fin d × E) × (Fin d × F)) (Fin d × Fin d) ℂ)
    (z : Fin d × ((Fin d × F) × E)) :
    crossedBobVector G z =
      crossedAliceVector (G.submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _)) z := rfl

omit [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F] in
theorem frozenSwap_submatrix_prodComm (g : E × F → ℂ) :
    (frozenSwap d g).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) =
      frozenSwap d (fun p : F × E => g (p.2, p.1)) := by
  ext p q
  simp only [Matrix.submatrix_apply, frozenSwap_apply, Equiv.prodComm_apply, Prod.fst_swap,
    Prod.snd_swap, and_comm]

theorem crossedBob_lower (hd : 0 < d)
    {G : Matrix ((Fin d × E) × (Fin d × F)) (Fin d × Fin d) ℂ} (hG : IsIsometry G)
    {g : E × F → ℂ} (hg : IsUnitVector g) {t : ℝ} (ht : 0 ≤ t) (ht2 : t ^ 2 ≤ 2)
    (hclose : ‖G - frozenSwap d g‖ ≤ t * d) :
    (d : ℝ) ^ 3 * (1 - t ^ 2 / 2) ^ 2 ≤ ∑ z, Complex.normSq (crossedBobVector G z) := by
  have hg' : IsUnitVector (fun p : F × E => g (p.2, p.1)) :=
    (Fintype.sum_equiv (Equiv.prodComm F E) _ _ (fun _ => rfl)).trans hg
  have hG' := hG.submatrix_equiv (Equiv.prodComm (Fin d × F) (Fin d × E))
    (Equiv.prodComm (Fin d) (Fin d))
  have hclose' : ‖G.submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) -
      frozenSwap d (fun p : F × E => g (p.2, p.1))‖ ≤ t * d := by
    have hsub : G.submatrix (Equiv.prodComm (Fin d × F) (Fin d × E)) (Equiv.prodComm (Fin d) (Fin d)) -
        (frozenSwap d g).submatrix (Equiv.prodComm (Fin d × F) (Fin d × E))
          (Equiv.prodComm (Fin d) (Fin d)) =
        (G - frozenSwap d g).submatrix (Equiv.prodComm (Fin d × F) (Fin d × E))
          (Equiv.prodComm (Fin d) (Fin d)) := by
      ext p q
      simp
    rw [← frozenSwap_submatrix_prodComm, hsub, norm_submatrix_equiv]
    exact hclose
  simpa only [crossedBobVector_eq] using crossedAlice_lower hd hG' hg' ht ht2 hclose'

end CrossedVectors

section Protocol

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

theorem PureProtocol.crossedAliceVector_globalIsometry
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    (z : Fin d × ((Fin d × εA) × εB)) :
    crossedAliceVector P.globalIsometry z =
      crossedAmplitude P.decA P.decB P.encA P.encB P.resource z.1 z.2.1 z.2.2 := by
  obtain ⟨rb, x, y⟩ := z
  simp only [crossedAliceVector, PureProtocol.globalIsometry, globalIsometry_apply_expanded,
    Fintype.sum_prod_type, Finset.mul_sum]
  rw [sum_seven_perm_alice]
  simp only [crossedAmplitude, crossedXi, crossedChi, crossedPhi, Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem PureProtocol.crossedBobVector_globalIsometry
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    (z : Fin d × ((Fin d × εB) × εA)) :
    crossedBobVector P.globalIsometry z =
      crossedAmplitude P.decB P.decA P.encB P.encA (fun p : ρB × ρA => P.resource (p.2, p.1))
        z.1 z.2.1 z.2.2 := by
  obtain ⟨ra, x, y⟩ := z
  simp only [crossedBobVector, PureProtocol.globalIsometry, globalIsometry_apply_expanded,
    Fintype.sum_prod_type, Finset.mul_sum]
  rw [sum_seven_perm_bob]
  simp only [crossedAmplitude, crossedXi, crossedChi, crossedPhi, Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem PureProtocol.sum_normSq_crossedAlice_le
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB) :
    ∑ z, Complex.normSq (crossedAliceVector P.globalIsometry z) ≤
      (Fintype.card μA : ℝ) ^ 2 * d := by
  have h := sum_normSq_crossedAmplitude_le P.decA_isometry P.decB_isometry P.encA_isometry
    P.encB_isometry P.resource_unit
  simp only [Fintype.card_fin] at h
  calc ∑ z, Complex.normSq (crossedAliceVector P.globalIsometry z)
      = ∑ rb, ∑ x, ∑ y, Complex.normSq
          (crossedAmplitude P.decA P.decB P.encA P.encB P.resource rb x y) := by
        simp only [Fintype.sum_prod_type, P.crossedAliceVector_globalIsometry]
    _ ≤ _ := h

theorem PureProtocol.sum_normSq_crossedBob_le
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB) :
    ∑ z, Complex.normSq (crossedBobVector P.globalIsometry z) ≤
      (Fintype.card μB : ℝ) ^ 2 * d := by
  have hη : IsUnitVector (fun p : ρB × ρA => P.resource (p.2, p.1)) :=
    (Fintype.sum_equiv (Equiv.prodComm ρB ρA) _ _ (fun _ => rfl)).trans P.resource_unit
  have h := sum_normSq_crossedAmplitude_le P.decB_isometry P.decA_isometry P.encB_isometry
    P.encA_isometry hη
  simp only [Fintype.card_fin] at h
  calc ∑ z, Complex.normSq (crossedBobVector P.globalIsometry z)
      = ∑ ra, ∑ x, ∑ y, Complex.normSq (crossedAmplitude P.decB P.decA P.encB P.encA
          (fun p : ρB × ρA => P.resource (p.2, p.1)) ra x y) := by
        simp only [Fintype.sum_prod_type, P.crossedBobVector_globalIsometry]
    _ ≤ _ := h

/-- Near-SWAP message floors: near SWAP, both complete charged messages satisfy `d² ≤ 2 m²`, for every pure
protocol on arbitrary finite registers and score error `0 ≤ e ≤ 1/16`. -/
theorem PureProtocol.sq_le_two_mul_message_sq_of_mem_swapNeighborhood
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB) (hd : 0 < d)
    {U : Matrix.unitaryGroup (Fin d × Fin d) ℂ} (hU : U ∈ swapNeighborhood d) {e : ℝ}
    (he : e ≤ 1 / 16)
    (hscore : 1 - e ≤ scoreU (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) P.operationalChannel) :
    (d : ℝ) ^ 2 ≤ 2 * (Fintype.card μA : ℝ) ^ 2 ∧ (d : ℝ) ^ 2 ≤ 2 * (Fintype.card μB : ℝ) ^ 2 := by
  have : NeZero d := ⟨hd.ne'⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨g, hg, -, hclose⟩ := P.exists_rank_bounded_approx_frozen
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (Matrix.mem_unitaryGroup_iff'.mp U.2)
    ((hasFootprint_iff _ P.resource).mpr le_rfl) (by linarith) hscore
  have hsqrt : Real.sqrt (Fintype.card (Fin d × Fin d) : ℝ) = d := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact Real.sqrt_mul_self hdR.le
  rw [hsqrt, div_le_iff₀ hdR] at hclose
  have h2 : ‖insertResource (Fin d) (Fin d) g * (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
      frozenSwap d g‖ ≤ (d : ℝ) / 4 := by
    rw [frozenSwap, ← Matrix.mul_sub, (isIsometry_insertResource g hg).frobNorm_mul_eq]
    exact (mem_swapNeighborhood_iff hd U).mp hU
  have hs : Real.sqrt (2 * e) ≤ 3 / 8 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hclose' : ‖P.globalIsometry - frozenSwap d g‖ ≤ 5 / 8 * d := by
    calc ‖P.globalIsometry - frozenSwap d g‖ =
        ‖(P.globalIsometry - insertResource (Fin d) (Fin d) g *
            (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) +
          (insertResource (Fin d) (Fin d) g * (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
            frozenSwap d g)‖ := by rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ Real.sqrt (2 * e) * d + d / 4 := add_le_add hclose h2
      _ ≤ 5 / 8 * d := by nlinarith
  have hA := (crossedAlice_lower hd P.isIsometry_globalIsometry hg (t := 5 / 8) (by norm_num)
    (by norm_num) hclose').trans P.sum_normSq_crossedAlice_le
  have hB := (crossedBob_lower hd P.isIsometry_globalIsometry hg (t := 5 / 8) (by norm_num)
    (by norm_num) hclose').trans P.sum_normSq_crossedBob_le
  norm_num at hA hB
  constructor
  · nlinarith
  · nlinarith

/-- Near-SWAP message floors consequences: the charged footprint is at least `d²/2`, and the resource rank
satisfies `r · d²/2 ≤ K`, i.e. `r ≤ 2K/d²`. -/
theorem PureProtocol.footprint_bounds_of_mem_swapNeighborhood
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB) (hd : 0 < d)
    {U : Matrix.unitaryGroup (Fin d × Fin d) ℂ} (hU : U ∈ swapNeighborhood d) {e : ℝ}
    (he : e ≤ 1 / 16)
    (hscore : 1 - e ≤ scoreU (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) P.operationalChannel)
    {K : ℕ} (hK : P.HasFootprint K) :
    (d : ℝ) ^ 2 / 2 ≤ K ∧ (schmidtRank P.resource : ℝ) * ((d : ℝ) ^ 2 / 2) ≤ K := by
  obtain ⟨hA, hB⟩ := P.sq_le_two_mul_message_sq_of_mem_swapNeighborhood hd hU he hscore
  have hfoot : ((schmidtRank P.resource * Fintype.card μA * Fintype.card μB : ℕ) : ℝ) ≤ K := by
    exact_mod_cast (hasFootprint_iff K P.resource).mp hK
  push_cast at hfoot
  have hr : (1 : ℝ) ≤ schmidtRank P.resource := by
    exact_mod_cast P.resource_unit.schmidtRank_pos
  have hprod : ((d : ℝ) ^ 2 / 2) ^ 2 ≤ ((Fintype.card μA : ℝ) * Fintype.card μB) ^ 2 := by
    nlinarith [mul_le_mul hA hB (by positivity) (by positivity)]
  have hm : (d : ℝ) ^ 2 / 2 ≤ (Fintype.card μA : ℝ) * Fintype.card μB :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 2 ≠ 0)).mp hprod
  have hr0 : (0 : ℝ) ≤ schmidtRank P.resource := by positivity
  have hrK : (schmidtRank P.resource : ℝ) * ((d : ℝ) ^ 2 / 2) ≤ K := by
    calc (schmidtRank P.resource : ℝ) * ((d : ℝ) ^ 2 / 2)
        ≤ (schmidtRank P.resource : ℝ) * ((Fintype.card μA : ℝ) * Fintype.card μB) :=
          mul_le_mul_of_nonneg_left hm hr0
      _ ≤ K := by rw [← mul_assoc]; exact hfoot
  refine ⟨?_, hrK⟩
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 / 2 := by positivity
  nlinarith

end Protocol

end NLQCLean
