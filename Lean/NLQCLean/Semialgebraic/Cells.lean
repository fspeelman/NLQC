import NLQCLean.Semialgebraic.CylindricalRoots
import NLQCLean.Semialgebraic.SAPaths

/-!
# Cylindrical cells over a base

For a parametric family `F` and a set `D` of parameters, `cell F D j` is the
set of points `(g, y)` with `g ∈ D` and `y` in slot `j` at `g`: the graph of a
root for odd `j`, the band between two consecutive roots (or below the first,
above the last, or the whole line when there are none) for even `j`. If `F` is
derivative-closed, the number of roots is constant on `D` and `D` is
semialgebraically path connected, so is each cell: base paths lift through the
continuous root functions.
-/

noncomputable section

namespace NLQCLean

open Set Sundog.TarskiQE

variable {n : ℕ}

/-- The cell of slot `j` over `D`. -/
def cell (F : List (ParamPoly n)) (D : Set (Fin n → ℝ)) (j : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {h | Fin.init h ∈ D ∧ h ∈ slotSet F j}

theorem saOn_cell {F : List (ParamPoly n)} {D : Set (Fin n → ℝ)} (hD : SAOn D) (j : ℕ) :
    SAOn (cell F D j) :=
  (hD.comap Fin.castSucc).inter (saOn_slotSet F j)

theorem snoc_mem_cell {F : List (ParamPoly n)} {D : Set (Fin n → ℝ)} {j : ℕ} {g : Fin n → ℝ}
    {y : ℝ} : (Fin.snoc g y : Fin (n + 1) → ℝ) ∈ cell F D j ↔ g ∈ D ∧ slotIndex F g y = j := by
  simp [cell, slotSet]

theorem slotIndex_odd_iff {F : List (ParamPoly n)} {g : Fin n → ℝ} {i : ℕ}
    (hi : i < (rootSet F g).ncard) (y : ℝ) : slotIndex F g y = 2 * i + 1 ↔ y = rootFn F g i := by
  rw [slotIndex_eq_iff, rootFn, eq_nthElem_iff (rootSet_finite F g) hi]
  constructor
  · rintro ⟨hc, hr⟩
    exact ⟨hr.mpr (by omega), by omega⟩
  · rintro ⟨hy, hc⟩
    exact ⟨by omega, iff_of_true hy (by omega)⟩

theorem slotIndex_even_iff {F : List (ParamPoly n)} {g : Fin n → ℝ} {i : ℕ}
    (hi : i ≤ (rootSet F g).ncard) (y : ℝ) :
    slotIndex F g y = 2 * i ↔ (0 < i → rootFn F g (i - 1) < y) ∧
      (i < (rootSet F g).ncard → y < rootFn F g i) := by
  have hT := rootSet_finite F g
  rw [slotIndex_eq_iff]
  have h2 : 2 * i / 2 = i := by omega
  have h3 : ¬ (2 * i % 2 = 1) := by omega
  rw [h2]
  simp only [h3, iff_false]
  rw [countBelow_eq_iff hT hi]
  unfold rootFn
  constructor
  · rintro ⟨⟨h1, h2⟩, hr⟩
    refine ⟨h1, fun hik => lt_of_le_of_ne (h2 hik) fun e => hr ?_⟩
    rw [e]
    exact (nthElem_spec hT hik).1
  · rintro ⟨h1, h2⟩
    have hc : countBelow (rootSet F g) y = i :=
      (countBelow_eq_iff hT hi).mpr ⟨h1, fun h => (h2 h).le⟩
    refine ⟨⟨h1, fun hik => (h2 hik).le⟩, fun hr => ?_⟩
    rcases lt_or_eq_of_le hi with hik | hik
    · exact absurd ((mem_iff_eq_nthElem hT hik hc).mp hr) (h2 hik).ne
    · exact not_mem_of_countBelow_eq_ncard hT (hik ▸ hc) hr

theorem slotIndex_le (F : List (ParamPoly n)) (g : Fin n → ℝ) (y : ℝ) :
    slotIndex F g y ≤ 2 * (rootSet F g).ncard := by
  classical
  have hT := rootSet_finite F g
  unfold slotIndex
  split_ifs with hr
  · have := countBelow_lt_ncard hT hr
    omega
  · have := countBelow_le_ncard hT y
    omega

/-! ### Lifting paths -/

theorem IsSAPath.snoc_of {γ : ℝ → Fin n → ℝ} {Y : ℝ → ℝ} (hγ : IsSAPath γ)
    (hY : ContinuousOn Y (Icc 0 1)) {R : Set (Option (Fin (n + 1)) → ℝ)} (hR : SAOn R)
    (hRY : ∀ x : Option (Fin (n + 1)) → ℝ, x none ∈ Icc (0 : ℝ) 1 →
      (fun i => x (some i.castSucc)) = γ (x none) → (x ∈ R ↔ x (some (Fin.last n)) = Y (x none))) :
    IsSAPath fun t => (Fin.snoc (γ t) (Y t) : Fin (n + 1) → ℝ) :=
  IsSAPath.snoc hγ.continuousOn hY (((saOn_basePathGraph hγ).inter hR).congr fun x => by
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨ht, hb⟩, hx⟩
      exact ⟨ht, hb, (hRY x ht (funext hb)).mp hx⟩
    · rintro ⟨ht, hb, hx⟩
      exact ⟨⟨ht, hb⟩, (hRY x ht (funext hb)).mpr hx⟩)

/-- The base path lifts into slot `j` from height `y₁` to height `y₂`. -/
def LiftsTo (F : List (ParamPoly n)) (γ : ℝ → Fin n → ℝ) (j : ℕ) (y₁ y₂ : ℝ) : Prop :=
  ∃ Y : ℝ → ℝ, IsSAPath (fun t => (Fin.snoc (γ t) (Y t) : Fin (n + 1) → ℝ)) ∧ Y 0 = y₁ ∧
    Y 1 = y₂ ∧ ∀ t ∈ Icc (0 : ℝ) 1, slotIndex F (γ t) (Y t) = j

theorem mem_Ioo_convex {a b s₁ s₂ t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (h₁ : s₁ ∈ Ioo a b)
    (h₂ : s₂ ∈ Ioo a b) : (1 - t) * s₁ + t * s₂ ∈ Ioo a b := by
  obtain ⟨ht0, ht1⟩ := ht
  constructor
  · rcases le_or_gt t (1 / 2) with h | h
    · nlinarith [mul_nonneg ht0 (sub_nonneg.mpr h₂.1.le), h₁.1]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h₁.1.le), h₂.1]
  · rcases le_or_gt t (1 / 2) with h | h
    · nlinarith [mul_nonneg ht0 (sub_nonneg.mpr h₂.2.le), h₁.2]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h₁.2.le), h₂.2]

theorem continuousOn_convex (s₁ s₂ : ℝ) : Continuous fun t : ℝ => (1 - t) * s₁ + t * s₂ := by
  fun_prop

/-- The coordinate change `(t, g, y) ↦ (g, y + c(t))`. -/
def shiftLast (c : MvPolynomial (Option (Fin (n + 1))) ℝ) :
    Fin (n + 1) → MvPolynomial (Option (Fin (n + 1))) ℝ :=
  Fin.lastCases (MvPolynomial.X (some (Fin.last n)) + c) fun l => MvPolynomial.X (some l.castSucc)

theorem slot_shift_iff (F : List (ParamPoly n)) (c : MvPolynomial (Option (Fin (n + 1))) ℝ) (j : ℕ)
    (x : Option (Fin (n + 1)) → ℝ) :
    (fun l => MvPolynomial.eval x (shiftLast c l)) ∈ slotSet F j ↔
      slotIndex F (fun l => x (some l.castSucc))
        (x (some (Fin.last n)) + MvPolynomial.eval x c) = j := by
  change slotIndex F (fun l : Fin n => MvPolynomial.eval x (shiftLast c l.castSucc))
    (MvPolynomial.eval x (shiftLast c (Fin.last n))) = j ↔ _
  simp [shiftLast]

section Lifts

variable {F : List (ParamPoly n)} (hF : DerivClosed F) {D : Set (Fin n → ℝ)} {k : ℕ}
  (hk : ∀ g ∈ D, (rootSet F g).ncard = k) {γ : ℝ → Fin n → ℝ} (hγ : IsSAPath γ)
  (hmaps : MapsTo γ (Icc 0 1) D)

include hF hk hγ hmaps

theorem continuousOn_rootFn_comp {i : ℕ} (hi : i < k) :
    ContinuousOn (fun t => rootFn F (γ t) i) (Icc 0 1) :=
  (continuousOn_rootFn hF hk hi).comp hγ.continuousOn hmaps

theorem lift_odd {i : ℕ} {y₁ y₂ : ℝ} (hy₁ : slotIndex F (γ 0) y₁ = 2 * i + 1)
    (hy₂ : slotIndex F (γ 1) y₂ = 2 * i + 1) : LiftsTo F γ (2 * i + 1) y₁ y₂ := by
  have h0 : γ 0 ∈ D := hmaps ⟨le_refl 0, zero_le_one⟩
  have h1 : γ 1 ∈ D := hmaps ⟨zero_le_one, le_refl 1⟩
  have hi : i < k := by
    have := slotIndex_le F (γ 0) y₁
    rw [hk _ h0] at this
    omega
  have hik : ∀ t ∈ Icc (0 : ℝ) 1, i < (rootSet F (γ t)).ncard := fun t ht => (hk _ (hmaps ht)).symm ▸ hi
  refine ⟨fun t => rootFn F (γ t) i, ?_, ?_, ?_, fun t ht => ?_⟩
  · refine hγ.snoc_of (continuousOn_rootFn_comp hF hk hγ hmaps hi)
      ((saOn_slotSet F (2 * i + 1)).comap some) fun x ht hb => ?_
    change slotIndex F (fun l => x (some l.castSucc)) (x (some (Fin.last n))) = 2 * i + 1 ↔ _
    rw [hb]
    exact slotIndex_odd_iff (hik _ ht) _
  · exact ((slotIndex_odd_iff (hik 0 ⟨le_refl 0, zero_le_one⟩) y₁).mp hy₁).symm
  · exact ((slotIndex_odd_iff (hik 1 ⟨zero_le_one, le_refl 1⟩) y₂).mp hy₂).symm
  · exact (slotIndex_odd_iff (hik t ht) _).mpr rfl

omit hF in
theorem lift_full (hk0 : k = 0) {y₁ y₂ : ℝ} : LiftsTo F γ 0 y₁ y₂ := by
  have hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, slotIndex F (γ t) y = 0 := by
    intro t ht y
    have h := slotIndex_even_iff (F := F) (g := γ t) (i := 0) (Nat.zero_le _) y
    rw [Nat.mul_zero] at h
    refine h.mpr ⟨fun h => absurd h (lt_irrefl 0), fun h => ?_⟩
    rw [hk _ (hmaps ht), hk0] at h
    exact absurd h (lt_irrefl 0)
  refine ⟨fun t => (1 - t) * y₁ + t * y₂, ?_, by simp, by simp, fun t ht => hzero t ht _⟩
  refine hγ.snoc_of (continuousOn_convex y₁ y₂).continuousOn
    (SAOn.eq (MvPolynomial.X (some (Fin.last n)))
      ((1 - MvPolynomial.X none) * MvPolynomial.C y₁ + MvPolynomial.X none * MvPolynomial.C y₂))
    fun x _ _ => ?_
  simp

theorem lift_below (hk0 : 0 < k) {y₁ y₂ : ℝ} (hy₁ : slotIndex F (γ 0) y₁ = 2 * 0)
    (hy₂ : slotIndex F (γ 1) y₂ = 2 * 0) : LiftsTo F γ 0 y₁ y₂ := by
  have hk' : ∀ t ∈ Icc (0 : ℝ) 1, (rootSet F (γ t)).ncard = k := fun t ht => hk _ (hmaps ht)
  have hle : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (rootSet F (γ t)).ncard := fun _ _ => Nat.zero_le _
  have hcar : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, slotIndex F (γ t) y = 2 * 0 ↔ y < rootFn F (γ t) 0 := by
    intro t ht y
    rw [slotIndex_even_iff (hle t ht)]
    simp [hk' t ht, hk0]
  have ht0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have ht1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  set u₁ := rootFn F (γ 0) 0 - y₁
  set u₂ := rootFn F (γ 1) 0 - y₂
  have hu₁ : 0 < u₁ := sub_pos.mpr ((hcar 0 ht0 y₁).mp hy₁)
  have hu₂ : 0 < u₂ := sub_pos.mpr ((hcar 1 ht1 y₂).mp hy₂)
  have hu : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (1 - t) * u₁ + t * u₂ := fun t ht =>
    (mem_Ioo_convex (b := u₁ + u₂ + 1) ht ⟨hu₁, by linarith⟩ ⟨hu₂, by linarith⟩).1
  let c : MvPolynomial (Option (Fin (n + 1))) ℝ :=
    (1 - MvPolynomial.X none) * MvPolynomial.C u₁ + MvPolynomial.X none * MvPolynomial.C u₂
  refine ⟨fun t => rootFn F (γ t) 0 - ((1 - t) * u₁ + t * u₂), ?_, ?_, ?_, fun t ht => ?_⟩
  · refine hγ.snoc_of ((continuousOn_rootFn_comp hF hk hγ hmaps hk0).sub
      (continuousOn_convex u₁ u₂).continuousOn)
      ((saOn_slotSet F 1).preimage (shiftLast c)) fun x ht hb => ?_
    change (fun l => MvPolynomial.eval x (shiftLast c l)) ∈ slotSet F 1 ↔ _
    rw [slot_shift_iff, hb]
    have := slotIndex_odd_iff (F := F) (g := γ (x none)) (i := 0)
      ((hk' _ ht).symm ▸ hk0) (x (some (Fin.last n)) + MvPolynomial.eval x c)
    rw [Nat.mul_zero, zero_add] at this
    rw [this]
    simp only [c, map_add, map_mul, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, map_one]
    constructor <;> intro h <;> linarith
  · simp [u₁]
  · simp [u₂]
  · rw [hcar t ht]
    linarith [hu t ht]

theorem lift_above {i : ℕ} (hi0 : 0 < i) (hik : i = k) {y₁ y₂ : ℝ}
    (hy₁ : slotIndex F (γ 0) y₁ = 2 * i) (hy₂ : slotIndex F (γ 1) y₂ = 2 * i) :
    LiftsTo F γ (2 * i) y₁ y₂ := by
  subst hik
  have hk' : ∀ t ∈ Icc (0 : ℝ) 1, (rootSet F (γ t)).ncard = i := fun t ht => hk _ (hmaps ht)
  have hcar : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y,
      slotIndex F (γ t) y = 2 * i ↔ rootFn F (γ t) (i - 1) < y := by
    intro t ht y
    rw [slotIndex_even_iff (hk' t ht).ge]
    simp [hk' t ht, hi0]
  have ht0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have ht1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  set u₁ := y₁ - rootFn F (γ 0) (i - 1)
  set u₂ := y₂ - rootFn F (γ 1) (i - 1)
  have hu₁ : 0 < u₁ := sub_pos.mpr ((hcar 0 ht0 y₁).mp hy₁)
  have hu₂ : 0 < u₂ := sub_pos.mpr ((hcar 1 ht1 y₂).mp hy₂)
  have hu : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (1 - t) * u₁ + t * u₂ := fun t ht =>
    (mem_Ioo_convex (b := u₁ + u₂ + 1) ht ⟨hu₁, by linarith⟩ ⟨hu₂, by linarith⟩).1
  let c : MvPolynomial (Option (Fin (n + 1))) ℝ :=
    -((1 - MvPolynomial.X none) * MvPolynomial.C u₁ + MvPolynomial.X none * MvPolynomial.C u₂)
  have hlt : i - 1 < i := by omega
  refine ⟨fun t => rootFn F (γ t) (i - 1) + ((1 - t) * u₁ + t * u₂), ?_, ?_, ?_,
    fun t ht => ?_⟩
  · refine hγ.snoc_of ((continuousOn_rootFn_comp hF hk hγ hmaps hlt).add
      (continuousOn_convex u₁ u₂).continuousOn)
      ((saOn_slotSet F (2 * (i - 1) + 1)).preimage (shiftLast c)) fun x ht hb => ?_
    change (fun l => MvPolynomial.eval x (shiftLast c l)) ∈ slotSet F (2 * (i - 1) + 1) ↔ _
    rw [slot_shift_iff, hb, slotIndex_odd_iff ((hk' _ ht).symm ▸ hlt)]
    simp only [c, map_neg, map_add, map_mul, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
      map_one]
    constructor <;> intro h <;> linarith
  · simp [u₁]
  · simp [u₂]
  · rw [hcar t ht]
    linarith [hu t ht]

end Lifts

/-- The two root coordinates of the bounded band construction. -/
def bandE₁ (n : ℕ) : Fin (n + 1) → Option (Option (Option (Fin (n + 1)))) :=
  Fin.lastCases none fun l => some (some (some l.castSucc))

def bandE₂ (n : ℕ) : Fin (n + 1) → Option (Option (Option (Fin (n + 1)))) :=
  Fin.lastCases (some none) fun l => some (some (some l.castSucc))

theorem comp_bandE₁_mem (F : List (ParamPoly n)) (j : ℕ)
    (w : Option (Option (Option (Fin (n + 1)))) → ℝ) :
    w ∘ bandE₁ n ∈ slotSet F j ↔
      slotIndex F (fun l => w (some (some (some l.castSucc)))) (w none) = j := by
  change slotIndex F (fun l : Fin n => w (bandE₁ n l.castSucc)) (w (bandE₁ n (Fin.last n))) = j ↔ _
  simp [bandE₁]

theorem comp_bandE₂_mem (F : List (ParamPoly n)) (j : ℕ)
    (w : Option (Option (Option (Fin (n + 1)))) → ℝ) :
    w ∘ bandE₂ n ∈ slotSet F j ↔
      slotIndex F (fun l => w (some (some (some l.castSucc)))) (w (some none)) = j := by
  change slotIndex F (fun l : Fin n => w (bandE₂ n l.castSucc)) (w (bandE₂ n (Fin.last n))) = j ↔ _
  simp [bandE₂]

section Between

variable {F : List (ParamPoly n)} (hF : DerivClosed F) {D : Set (Fin n → ℝ)} {k : ℕ}
  (hk : ∀ g ∈ D, (rootSet F g).ncard = k) {γ : ℝ → Fin n → ℝ} (hγ : IsSAPath γ)
  (hmaps : MapsTo γ (Icc 0 1) D)

include hF hk hγ hmaps

theorem lift_between {i : ℕ} (hi0 : 0 < i) (hik : i < k) {y₁ y₂ : ℝ}
    (hy₁ : slotIndex F (γ 0) y₁ = 2 * i) (hy₂ : slotIndex F (γ 1) y₂ = 2 * i) :
    LiftsTo F γ (2 * i) y₁ y₂ := by
  have hk' : ∀ t ∈ Icc (0 : ℝ) 1, (rootSet F (γ t)).ncard = k := fun t ht => hk _ (hmaps ht)
  have hlt : i - 1 < i := by omega
  let L : ℝ → ℝ := fun t => rootFn F (γ t) (i - 1)
  let U : ℝ → ℝ := fun t => rootFn F (γ t) i
  have hLU : ∀ t ∈ Icc (0 : ℝ) 1, L t < U t := fun t ht =>
    nthElem_lt_nthElem (rootSet_finite F _) hlt ((hk' t ht).symm ▸ hik)
  have hcar : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, slotIndex F (γ t) y = 2 * i ↔ L t < y ∧ y < U t := by
    intro t ht y
    rw [slotIndex_even_iff ((hk' t ht).symm ▸ hik.le)]
    simp [hk' t ht, hi0, hik, L, U]
  have ht0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have ht1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  obtain ⟨h1L, h1U⟩ := (hcar 0 ht0 y₁).mp hy₁
  obtain ⟨h2L, h2U⟩ := (hcar 1 ht1 y₂).mp hy₂
  have hd₁ : 0 < U 0 - L 0 := sub_pos.mpr (hLU 0 ht0)
  have hd₂ : 0 < U 1 - L 1 := sub_pos.mpr (hLU 1 ht1)
  set s₁ := (y₁ - L 0) / (U 0 - L 0)
  set s₂ := (y₂ - L 1) / (U 1 - L 1)
  have hs₁ : s₁ ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (by linarith) hd₁
    · rw [div_lt_one hd₁]
      linarith
  have hs₂ : s₂ ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (by linarith) hd₂
    · rw [div_lt_one hd₂]
      linarith
  let S : ℝ → ℝ := fun t => (1 - t) * s₁ + t * s₂
  have hS : ∀ t ∈ Icc (0 : ℝ) 1, S t ∈ Ioo (0 : ℝ) 1 := fun t ht => mem_Ioo_convex ht hs₁ hs₂
  -- the semialgebraic description of the lifted graph
  let tc : Option (Option (Option (Fin (n + 1)))) := some (some none)
  let yc : Option (Option (Option (Fin (n + 1)))) := some (some (some (Fin.last n)))
  let Sp : MvPolynomial (Option (Option (Option (Fin (n + 1))))) ℝ :=
    (1 - MvPolynomial.X tc) * MvPolynomial.C s₁ + MvPolynomial.X tc * MvPolynomial.C s₂
  have hA : SAOn ({w | w ∘ bandE₁ n ∈ slotSet F (2 * (i - 1) + 1)} ∩
      {w | w ∘ bandE₂ n ∈ slotSet F (2 * i + 1)} ∩
      {w : Option (Option (Option (Fin (n + 1)))) → ℝ | MvPolynomial.eval w (MvPolynomial.X yc) =
        MvPolynomial.eval w ((1 - Sp) * MvPolynomial.X none + Sp * MvPolynomial.X (some none))}) :=
    (((saOn_slotSet F _).comap (bandE₁ n)).inter ((saOn_slotSet F _).comap (bandE₂ n))).inter
      (SAOn.eq _ _)
  have hR := SAOn.exists_option (SAOn.exists_option hA)
  refine ⟨fun t => (1 - S t) * L t + S t * U t, ?_, ?_, ?_, fun t ht => ?_⟩
  · have hLc : ContinuousOn L (Icc 0 1) := continuousOn_rootFn_comp hF hk hγ hmaps (hlt.trans hik)
    have hUc : ContinuousOn U (Icc 0 1) := continuousOn_rootFn_comp hF hk hγ hmaps hik
    have hSc : ContinuousOn S (Icc 0 1) := (continuousOn_convex s₁ s₂).continuousOn
    refine hγ.snoc_of (((continuousOn_const.sub hSc).mul hLc).add (hSc.mul hUc)) hR
      fun x ht hb => ?_
    simp only [mem_ofPred_eq, mem_inter_iff, comp_bandE₁_mem, comp_bandE₂_mem]
    simp only [Option.elim, hb, Sp, tc, yc, map_add, map_mul, map_sub, map_one,
      MvPolynomial.eval_X, MvPolynomial.eval_C]
    have hik' : i < (rootSet F (γ (x none))).ncard := (hk' _ ht).symm ▸ hik
    constructor
    · rintro ⟨b, a, ⟨ha, hb'⟩, hy⟩
      rw [slotIndex_odd_iff (hlt.trans hik') a] at ha
      rw [slotIndex_odd_iff hik' b] at hb'
      rw [hy, ha, hb']
    · intro hy
      refine ⟨U (x none), L (x none), ⟨(slotIndex_odd_iff (hlt.trans hik') _).mpr rfl,
        (slotIndex_odd_iff hik' _).mpr rfl⟩, ?_⟩
      rw [hy]
  · simp only [S, sub_zero, one_mul, zero_mul, add_zero, s₁]
    field_simp
    ring
  · simp only [S, sub_self, zero_mul, one_mul, zero_add, s₂]
    field_simp
    ring
  · rw [hcar t ht]
    obtain ⟨hS0, hS1⟩ := hS t ht
    have := hLU t ht
    constructor <;> nlinarith

end Between

/-- **Cells are semialgebraically path connected.** -/
theorem SAPathConnected.cell {F : List (ParamPoly n)} (hF : DerivClosed F) {D : Set (Fin n → ℝ)}
    (hD : SAPathConnected D) {k : ℕ} (hk : ∀ g ∈ D, (rootSet F g).ncard = k) (j : ℕ) :
    SAPathConnected (cell F D j) := by
  intro h₁ hh₁ h₂ hh₂
  obtain ⟨hg₁, hs₁⟩ := hh₁
  obtain ⟨hg₂, hs₂⟩ := hh₂
  obtain ⟨γ, hγ, hγ0, hγ1, hmaps⟩ := hD _ hg₁ _ hg₂
  have hy₁ : slotIndex F (γ 0) (h₁ (Fin.last n)) = j := hγ0 ▸ hs₁
  have hy₂ : slotIndex F (γ 1) (h₂ (Fin.last n)) = j := hγ1 ▸ hs₂
  have hlift : LiftsTo F γ j (h₁ (Fin.last n)) (h₂ (Fin.last n)) := by
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · have hik : i ≤ k := by
        have := slotIndex_le F (γ 0) (h₁ (Fin.last n))
        rw [hk _ (hmaps ⟨le_refl 0, zero_le_one⟩), hy₁] at this
        omega
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [Nat.mul_zero]
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · exact lift_full hk hγ hmaps hk0
        · exact lift_below hF hk hγ hmaps hk0 hy₁ hy₂
      · rcases lt_or_eq_of_le hik with hlt | heq
        · exact lift_between hF hk hγ hmaps hi0 hlt hy₁ hy₂
        · exact lift_above hF hk hγ hmaps hi0 heq hy₁ hy₂
    · exact lift_odd hF hk hγ hmaps hy₁ hy₂
  obtain ⟨Y, hY, hY0, hY1, hYslot⟩ := hlift
  refine ⟨_, hY, ?_, ?_, fun t ht => snoc_mem_cell.mpr ⟨hmaps ht, hYslot t ht⟩⟩
  · simp only [hγ0, hY0]
    exact Fin.snoc_init_self h₁
  · simp only [hγ1, hY1]
    exact Fin.snoc_init_self h₂

end NLQCLean
