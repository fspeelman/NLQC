import NLQCLean.LinearAlgebra.SchmidtOverlap
import Mathlib.Algebra.Order.Chebyshev

/-!
# The crossed-pair amplitude is bounded by the message dimension

For a one-round architecture written in
coordinates, the amplitude of Alice's reference paired with Bob's output channel obeys

  `∑ |crossed|² ≤ (dim M_A)² · dim J`,

where `M_A` is Alice's complete message and `J` Bob's input. This is the finite-sum
form of `ρ_{XM} ≤ m (ρ_X ⊗ I)` followed by Bob's decoder: one Cauchy–Schwarz step over
the message index, and four isometry identities. No PSD order, partial trace or
causality axiom is used, and no dimension of any preshared support appears.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

section Generic

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- An isometry preserves the squared norm of a coefficient vector. -/
theorem IsIsometry.sum_normSq_mulVec {V : Matrix m n ℂ} (hV : IsIsometry V) (u : n → ℂ) :
    ∑ i, Complex.normSq (∑ j, V i j * u j) = ∑ j, Complex.normSq (u j) := by
  have hent : ∀ k j, ∑ i, star (V i k) * V i j = if k = j then 1 else 0 := by
    intro k j
    have h := congrFun (congrFun hV k) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  have key : ∀ i, (∑ j, V i j * u j) * starRingEnd ℂ (∑ k, V i k * u k) =
      ∑ j, ∑ k, (u j * starRingEnd ℂ (u k)) * (star (V i k) * V i j) := by
    intro i
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, Complex.star_def]
    ring
  apply Complex.ofReal_injective
  calc ((∑ i, Complex.normSq (∑ j, V i j * u j) : ℝ) : ℂ)
      = ∑ i, (∑ j, V i j * u j) * starRingEnd ℂ (∑ k, V i k * u k) := by
        push_cast
        simp only [Complex.mul_conj]
    _ = ∑ i, ∑ j, ∑ k, (u j * starRingEnd ℂ (u k)) * (star (V i k) * V i j) :=
        Finset.sum_congr rfl fun i _ => key i
    _ = ∑ j, ∑ k, ∑ i, (u j * starRingEnd ℂ (u k)) * (star (V i k) * V i j) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)
    _ = ∑ j, ∑ k, (u j * starRingEnd ℂ (u k)) * ∑ i, star (V i k) * V i j := by
        simp only [Finset.mul_sum]
    _ = ∑ j, u j * starRingEnd ℂ (u j) := by
        simp only [hent, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
    _ = ((∑ j, Complex.normSq (u j) : ℝ) : ℂ) := by
        push_cast
        simp only [Complex.mul_conj]

omit [Fintype m] [Fintype n] [DecidableEq n] in
/-- Cauchy–Schwarz over a finite index. -/
theorem normSq_sum_le_card_mul {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    Complex.normSq (∑ a, z a) ≤ Fintype.card ι * ∑ a, Complex.normSq (z a) := by
  have h1 : ‖∑ a, z a‖ ≤ ∑ a, ‖z a‖ := norm_sum_le _ _
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun a => ‖z a‖)
  simp only [Complex.normSq_eq_norm_sq, Finset.card_univ] at h2 ⊢
  calc ‖∑ a, z a‖ ^ 2 ≤ (∑ a, ‖z a‖) ^ 2 := by gcongr
    _ ≤ _ := h2

end Generic

section Reorder

variable {α β γ δ ε ζ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  [Fintype ε] [Fintype ζ]

theorem sum_reorder_crossed_first (g : α → β → γ → δ → ℝ) :
    ∑ rb, ∑ x, ∑ y, ∑ a, g a rb x y = ∑ a, ∑ rb, ∑ y, ∑ x, g a rb x y := by
  calc ∑ rb, ∑ x, ∑ y, ∑ a, g a rb x y = ∑ rb, ∑ x, ∑ a, ∑ y, g a rb x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ rb, ∑ a, ∑ x, ∑ y, g a rb x y := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ rb, ∑ x, ∑ y, g a rb x y := Finset.sum_comm
    _ = ∑ a, ∑ rb, ∑ y, ∑ x, g a rb x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_reorder_crossed_second (G : α → β → γ → δ → ε → ζ → ℝ) :
    ∑ a, ∑ rb, ∑ y, ∑ mB, ∑ q : ε × ζ, G a rb y mB q.1 q.2 =
      ∑ rb, ∑ mB, ∑ pa, ∑ a, ∑ i : ε × γ, G a rb i.2 mB i.1 pa := by
  simp only [Fintype.sum_prod_type]
  calc ∑ a, ∑ rb, ∑ y, ∑ mB, ∑ r, ∑ pa, G a rb y mB r pa
      = ∑ rb, ∑ a, ∑ y, ∑ mB, ∑ r, ∑ pa, G a rb y mB r pa := Finset.sum_comm
    _ = ∑ rb, ∑ a, ∑ mB, ∑ y, ∑ r, ∑ pa, G a rb y mB r pa :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ rb, ∑ mB, ∑ a, ∑ y, ∑ r, ∑ pa, G a rb y mB r pa :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ rb, ∑ mB, ∑ a, ∑ y, ∑ pa, ∑ r, G a rb y mB r pa :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ rb, ∑ mB, ∑ a, ∑ pa, ∑ y, ∑ r, G a rb y mB r pa :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ rb, ∑ mB, ∑ pa, ∑ a, ∑ y, ∑ r, G a rb y mB r pa :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ rb, ∑ mB, ∑ pa, ∑ a, ∑ r, ∑ y, G a rb y mB r pa :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_reorder_crossed_third (g : α → β → γ → δ → ℝ) :
    ∑ rb, ∑ mB, ∑ pa, ∑ kB, g kB mB rb pa = ∑ rb, ∑ pa, ∑ k : α × β, g k.1 k.2 rb pa := by
  simp only [Fintype.sum_prod_type]
  calc ∑ rb, ∑ mB, ∑ pa, ∑ kB, g kB mB rb pa = ∑ rb, ∑ pa, ∑ mB, ∑ kB, g kB mB rb pa :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ rb, ∑ pa, ∑ kB, ∑ mB, g kB mB rb pa :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

end Reorder

section CrossedAmplitude

variable {X Y KA KB MA MB PA PB ι J : Type*}
  [Fintype X] [Fintype Y] [Fintype KA] [Fintype KB] [Fintype MA] [Fintype MB]
  [Fintype PA] [Fintype PB] [Fintype ι] [Fintype J]
  [DecidableEq KA] [DecidableEq KB] [DecidableEq MA] [DecidableEq MB]
  [DecidableEq PA] [DecidableEq PB] [DecidableEq ι] [DecidableEq J]

/-- Bob's encoded coefficient, before any message is received. -/
def crossedPhi (VB : Matrix (KB × MB) (J × PB) ℂ) (η : PA × PB → ℂ)
    (k : KB × MB) (rb : J) (pa : PA) : ℂ :=
  ∑ pb, VB k (rb, pb) * η (pa, pb)

/-- Bob's decoder applied with Alice's message index fixed. -/
def crossedChi (DB : Matrix (ι × Y) (KB × MA) ℂ) (VB : Matrix (KB × MB) (J × PB) ℂ)
    (η : PA × PB → ℂ) (a : MA) (rb : J) (y : Y) (mB : MB) (q : ι × PA) : ℂ :=
  ∑ kB, DB (q.1, y) (kB, a) * crossedPhi VB η (kB, mB) rb q.2

/-- Alice's encoder inserted, with an arbitrary Alice output row `α`. -/
def crossedXi (DB : Matrix (ι × Y) (KB × MA) ℂ) (VA : Matrix (KA × MA) (ι × PA) ℂ)
    (VB : Matrix (KB × MB) (J × PB) ℂ) (η : PA × PB → ℂ)
    (a : MA) (rb : J) (y : Y) (α : KA × MA) (mB : MB) : ℂ :=
  ∑ q, VA α q * crossedChi DB VB η a rb y mB q

/-- The crossed amplitude: Alice's reference index equals Bob's output index `r`. -/
def crossedAmplitude (DA : Matrix X (KA × MB) ℂ) (DB : Matrix (ι × Y) (KB × MA) ℂ)
    (VA : Matrix (KA × MA) (ι × PA) ℂ) (VB : Matrix (KB × MB) (J × PB) ℂ)
    (η : PA × PB → ℂ) (rb : J) (x : X) (y : Y) : ℂ :=
  ∑ a, ∑ p : KA × MB, DA x p * crossedXi DB VA VB η a rb y (p.1, a) p.2

/-- in coordinates: the crossed amplitude has squared norm at most `m_A² · dim J`. -/
theorem sum_normSq_crossedAmplitude_le {DA : Matrix X (KA × MB) ℂ}
    {DB : Matrix (ι × Y) (KB × MA) ℂ} {VA : Matrix (KA × MA) (ι × PA) ℂ}
    {VB : Matrix (KB × MB) (J × PB) ℂ} {η : PA × PB → ℂ}
    (hDA : IsIsometry DA) (hDB : IsIsometry DB) (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hη : IsUnitVector η) :
    ∑ rb, ∑ x, ∑ y, Complex.normSq (crossedAmplitude DA DB VA VB η rb x y) ≤
      (Fintype.card MA : ℝ) ^ 2 * Fintype.card J := by
  set m : ℝ := (Fintype.card MA : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  -- DA isometry, for fixed a, rb, y
  have h2 (a : MA) (rb : J) (y : Y) :
      ∑ x, Complex.normSq (∑ p : KA × MB, DA x p * crossedXi DB VA VB η a rb y (p.1, a) p.2) =
        ∑ p : KA × MB, Complex.normSq (crossedXi DB VA VB η a rb y (p.1, a) p.2) :=
    hDA.sum_normSq_mulVec _
  -- select Alice's row with message a, then VA isometry
  have h3 (a : MA) (rb : J) (y : Y) :
      ∑ p : KA × MB, Complex.normSq (crossedXi DB VA VB η a rb y (p.1, a) p.2) ≤
        ∑ mB, ∑ q : ι × PA, Complex.normSq (crossedChi DB VB η a rb y mB q) := by
    calc ∑ p : KA × MB, Complex.normSq (crossedXi DB VA VB η a rb y (p.1, a) p.2)
        = ∑ mB, ∑ kA, Complex.normSq (crossedXi DB VA VB η a rb y (kA, a) mB) := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
      _ ≤ ∑ mB, ∑ α' : KA × MA, Complex.normSq (crossedXi DB VA VB η a rb y α' mB) := by
          refine Finset.sum_le_sum fun mB _ => ?_
          rw [Fintype.sum_prod_type]
          exact Finset.sum_le_sum fun kA _ => Finset.single_le_sum
            (f := fun b => Complex.normSq (crossedXi DB VA VB η a rb y (kA, b) mB))
            (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ a)
      _ = _ := Finset.sum_congr rfl fun mB _ => hVA.sum_normSq_mulVec _
  -- DB isometry, for fixed rb, mB, pa and Alice message a
  have h4 (rb : J) (mB : MB) (pa : PA) (a : MA) :
      ∑ i : ι × Y, Complex.normSq (crossedChi DB VB η a rb i.2 mB (i.1, pa)) =
        ∑ kB, Complex.normSq (crossedPhi VB η (kB, mB) rb pa) := by
    let u : KB × MA → ℂ := fun j => if j.2 = a then crossedPhi VB η (j.1, mB) rb pa else 0
    calc ∑ i : ι × Y, Complex.normSq (crossedChi DB VB η a rb i.2 mB (i.1, pa))
        = ∑ i : ι × Y, Complex.normSq (∑ j, DB i j * u j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          rw [crossedChi, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun kB _ => ?_
          simp [u]
      _ = ∑ j, Complex.normSq (u j) := hDB.sum_normSq_mulVec u
      _ = _ := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun kB _ => ?_
          rw [Finset.sum_eq_single a]
          · simp [u]
          · intro b _ hb
            simp [u, hb]
          · simp
  -- VB isometry, for fixed rb, pa
  have h5 (rb : J) (pa : PA) :
      ∑ k : KB × MB, Complex.normSq (crossedPhi VB η k rb pa) =
        ∑ pb, Complex.normSq (η (pa, pb)) := by
    let u : J × PB → ℂ := fun j => if j.1 = rb then η (pa, j.2) else 0
    calc ∑ k : KB × MB, Complex.normSq (crossedPhi VB η k rb pa)
        = ∑ k : KB × MB, Complex.normSq (∑ j, VB k j * u j) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          congr 1
          rw [crossedPhi, Fintype.sum_prod_type, Finset.sum_eq_single rb]
          · simp [u]
          · intro b _ hb
            simp [u, hb]
          · simp
      _ = ∑ j, Complex.normSq (u j) := hVB.sum_normSq_mulVec u
      _ = _ := by
          rw [Fintype.sum_prod_type, Finset.sum_eq_single rb]
          · simp [u]
          · intro b _ hb
            simp [u, hb]
          · simp
  have hη' : ∑ pa, ∑ pb, Complex.normSq (η (pa, pb)) = 1 := by
    have h : ∑ e, Complex.normSq (η e) = 1 := hη
    rw [← h, Fintype.sum_prod_type]
  calc ∑ rb, ∑ x, ∑ y, Complex.normSq (crossedAmplitude DA DB VA VB η rb x y)
      ≤ ∑ rb, ∑ x, ∑ y, ∑ a, m * Complex.normSq
          (∑ p : KA × MB, DA x p * crossedXi DB VA VB η a rb y (p.1, a) p.2) := by
        refine Finset.sum_le_sum fun rb _ => Finset.sum_le_sum fun x _ =>
          Finset.sum_le_sum fun y _ => ?_
        rw [← Finset.mul_sum]
        exact normSq_sum_le_card_mul _
    _ = ∑ a, ∑ rb, ∑ y, ∑ x, m * Complex.normSq
          (∑ p : KA × MB, DA x p * crossedXi DB VA VB η a rb y (p.1, a) p.2) :=
        sum_reorder_crossed_first _
    _ = m * ∑ a, ∑ rb, ∑ y, ∑ p : KA × MB,
          Complex.normSq (crossedXi DB VA VB η a rb y (p.1, a) p.2) := by
        simp only [← Finset.mul_sum, h2]
    _ ≤ m * ∑ a, ∑ rb, ∑ y, ∑ mB, ∑ q : ι × PA,
          Complex.normSq (crossedChi DB VB η a rb y mB q) := by
        gcongr with a _ rb _ y _
        exact h3 a rb y
    _ = m * ∑ rb, ∑ mB, ∑ pa, ∑ a, ∑ i : ι × Y,
          Complex.normSq (crossedChi DB VB η a rb i.2 mB (i.1, pa)) := by
        congr 1
        exact sum_reorder_crossed_second
          (fun a rb y mB r pa => Complex.normSq (crossedChi DB VB η a rb y mB (r, pa)))
    _ = m * ∑ rb, ∑ mB, ∑ pa, m * ∑ kB, Complex.normSq (crossedPhi VB η (kB, mB) rb pa) := by
        simp only [h4, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm]
    _ = m * m * ∑ rb, ∑ pa, ∑ k : KB × MB, Complex.normSq (crossedPhi VB η k rb pa) := by
        simp only [← Finset.mul_sum]
        rw [mul_assoc]
        congr 2
        exact sum_reorder_crossed_third
          (fun kB mB rb pa => Complex.normSq (crossedPhi VB η (kB, mB) rb pa))
    _ = m ^ 2 * Fintype.card J := by
        simp only [h5, hη', Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        try ring

end CrossedAmplitude

end NLQCLean
