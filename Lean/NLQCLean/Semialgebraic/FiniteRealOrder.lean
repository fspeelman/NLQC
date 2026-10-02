import Mathlib.Data.Set.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Preorder.Finite

/-!
# Ordering a finite set of reals

For a finite `T ⊆ ℝ`, `countBelow T y` is the number of elements of `T` below
`y`, and `nthElem T i` is the element with exactly `i` elements below it.
-/

noncomputable section

namespace NLQCLean

/-- Number of elements of `T` strictly below `y`. -/
def countBelow (T : Set ℝ) (y : ℝ) : ℕ := {z | z ∈ T ∧ z < y}.ncard

variable {T : Set ℝ}

theorem countBelow_mono (hT : T.Finite) {y y' : ℝ} (h : y ≤ y') :
    countBelow T y ≤ countBelow T y' :=
  Set.ncard_le_ncard (fun _ hz => ⟨hz.1, hz.2.trans_le h⟩) (hT.subset fun _ hz => hz.1)

theorem countBelow_lt (hT : T.Finite) {y y' : ℝ} (hy : y ∈ T) (h : y < y') :
    countBelow T y < countBelow T y' := by
  refine Set.ncard_lt_ncard ⟨fun z hz => ⟨hz.1, hz.2.trans h⟩, fun hsub => ?_⟩
    (hT.subset fun z hz => hz.1)
  exact lt_irrefl y (hsub ⟨hy, h⟩).2

theorem countBelow_le_ncard (hT : T.Finite) (y : ℝ) : countBelow T y ≤ T.ncard :=
  Set.ncard_le_ncard (fun _ hz => hz.1) hT

theorem countBelow_lt_ncard (hT : T.Finite) {y : ℝ} (hy : y ∈ T) : countBelow T y < T.ncard := by
  refine Set.ncard_lt_ncard ⟨fun _ hz => hz.1, fun hsub => ?_⟩ hT
  exact lt_irrefl y (hsub hy).2

theorem succ_le_countBelow_iff (hT : T.Finite) {i : ℕ} {y : ℝ} :
    i + 1 ≤ countBelow T y ↔ ∃ z ∈ T, z < y ∧ i ≤ countBelow T z := by
  constructor
  · intro h
    have hfin : {z | z ∈ T ∧ z < y}.Finite := hT.subset fun z hz => hz.1
    have hne : {z | z ∈ T ∧ z < y}.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      unfold countBelow at h
      rw [hne, Set.ncard_empty] at h
      omega
    obtain ⟨z, hz, hmax⟩ := hfin.exists_maximal hne
    refine ⟨z, hz.1, hz.2, ?_⟩
    have heq : {w | w ∈ T ∧ w < y} = insert z {w | w ∈ T ∧ w < z} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
      constructor
      · rintro ⟨hw, hwy⟩
        rcases lt_trichotomy w z with hwz | rfl | hzw
        · exact Or.inr ⟨hw, hwz⟩
        · exact Or.inl rfl
        · exact absurd (hmax ⟨hw, hwy⟩ hzw.le) (not_le.mpr hzw)
      · rintro (rfl | ⟨hw, hwz⟩)
        · exact hz
        · exact ⟨hw, hwz.trans hz.2⟩
    have hc : countBelow T y = countBelow T z + 1 := by
      unfold countBelow
      rw [heq, Set.ncard_insert_of_notMem (fun h => lt_irrefl z h.2)
        (hT.subset fun w hw => hw.1)]
    omega
  · rintro ⟨z, hz, hzy, hi⟩
    have := countBelow_lt hT hz hzy
    omega

theorem le_ncard_iff_exists_countBelow (hT : T.Finite) {k : ℕ} :
    k ≤ T.ncard ↔ ∃ y, k ≤ countBelow T y := by
  constructor
  · intro hk
    obtain ⟨M, hM⟩ := hT.bddAbove
    refine ⟨M + 1, ?_⟩
    have : {z | z ∈ T ∧ z < M + 1} = T := by
      ext z
      exact ⟨fun h => h.1, fun h => ⟨h, (hM h).trans_lt (lt_add_one M)⟩⟩
    unfold countBelow
    rw [this]
    exact hk
  · rintro ⟨y, hy⟩
    exact hy.trans (countBelow_le_ncard hT y)

theorem exists_countBelow_eq (hT : T.Finite) {i : ℕ} (hi : i < T.ncard) :
    ∃ y ∈ T, countBelow T y = i := by
  have hne : {z | z ∈ T ∧ i ≤ countBelow T z}.Nonempty := by
    obtain ⟨y, hy⟩ := (le_ncard_iff_exists_countBelow hT).mp (Nat.succ_le_of_lt hi)
    obtain ⟨z, hz, -, hzi⟩ := (succ_le_countBelow_iff hT).mp hy
    exact ⟨z, hz, hzi⟩
  obtain ⟨z, hz, hmin⟩ := (hT.subset fun w hw => hw.1).exists_minimal hne
  refine ⟨z, hz.1, le_antisymm ?_ hz.2⟩
  by_contra hlt
  obtain ⟨w, hw, hwz, hwi⟩ := (succ_le_countBelow_iff hT).mp (Nat.succ_le_of_lt (not_le.mp hlt))
  exact absurd (hmin ⟨hw, hwi⟩ hwz.le) (not_le.mpr hwz)

theorem eq_of_countBelow_eq (hT : T.Finite) {y y' : ℝ} (hy : y ∈ T) (hy' : y' ∈ T)
    (h : countBelow T y = countBelow T y') : y = y' := by
  rcases lt_trichotomy y y' with hlt | heq | hgt
  · exact absurd h (countBelow_lt hT hy hlt).ne
  · exact heq
  · exact absurd h (countBelow_lt hT hy' hgt).ne'

open Classical in
/-- The element of `T` with exactly `i` elements below it (junk `0` if none). -/
def nthElem (T : Set ℝ) (i : ℕ) : ℝ :=
  if h : ∃ y ∈ T, countBelow T y = i then h.choose else 0

theorem nthElem_spec (hT : T.Finite) {i : ℕ} (hi : i < T.ncard) :
    nthElem T i ∈ T ∧ countBelow T (nthElem T i) = i := by
  have h := exists_countBelow_eq hT hi
  unfold nthElem
  rw [dite_eq_left h]
  exact h.choose_spec

theorem eq_nthElem (hT : T.Finite) {y : ℝ} (hy : y ∈ T) : y = nthElem T (countBelow T y) := by
  have hs := nthElem_spec hT (countBelow_lt_ncard hT hy)
  exact eq_of_countBelow_eq hT hy hs.1 hs.2.symm

theorem eq_nthElem_iff (hT : T.Finite) {y : ℝ} {i : ℕ} (hi : i < T.ncard) :
    y = nthElem T i ↔ y ∈ T ∧ countBelow T y = i := by
  constructor
  · rintro rfl
    exact nthElem_spec hT hi
  · rintro ⟨hy, rfl⟩
    exact eq_nthElem hT hy

theorem nthElem_lt_nthElem (hT : T.Finite) {i j : ℕ} (hij : i < j) (hj : j < T.ncard) :
    nthElem T i < nthElem T j := by
  have hi := nthElem_spec hT (hij.trans hj)
  have hj' := nthElem_spec hT hj
  by_contra hle
  have := countBelow_mono hT (not_lt.mp hle)
  omega

theorem succ_le_countBelow_iff_nthElem_lt (hT : T.Finite) {i : ℕ} (hi : i < T.ncard) {y : ℝ} :
    i + 1 ≤ countBelow T y ↔ nthElem T i < y := by
  have hs := nthElem_spec hT hi
  constructor
  · intro h
    by_contra hle
    have := countBelow_mono hT (not_lt.mp hle)
    omega
  · intro h
    have := countBelow_lt hT hs.1 h
    omega

/-- The elements below `y` are exactly the first `i`. -/
theorem countBelow_eq_iff (hT : T.Finite) {i : ℕ} (hik : i ≤ T.ncard) {y : ℝ} :
    countBelow T y = i ↔ (0 < i → nthElem T (i - 1) < y) ∧ (i < T.ncard → y ≤ nthElem T i) := by
  constructor
  · intro hc
    refine ⟨fun hi => ?_, fun hi => ?_⟩
    · exact (succ_le_countBelow_iff_nthElem_lt hT (y := y) (by omega)).mp (by omega)
    · by_contra hlt
      have := (succ_le_countBelow_iff_nthElem_lt hT hi (y := y)).mpr (not_le.mp hlt)
      omega
  · rintro ⟨h1, h2⟩
    have hge : i ≤ countBelow T y := by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact Nat.zero_le _
      · have := (succ_le_countBelow_iff_nthElem_lt hT (y := y) (by omega)).mpr (h1 hi)
        omega
    have hle : countBelow T y ≤ i := by
      rcases lt_or_eq_of_le hik with hlt | rfl
      · by_contra hgt
        have := (succ_le_countBelow_iff_nthElem_lt hT hlt (y := y)).mp (by omega)
        exact absurd (h2 hlt) (not_le.mpr this)
      · exact countBelow_le_ncard hT y
    omega

theorem mem_iff_eq_nthElem (hT : T.Finite) {y : ℝ} {i : ℕ} (hi : i < T.ncard)
    (hc : countBelow T y = i) : y ∈ T ↔ y = nthElem T i := by
  constructor
  · intro hy
    exact (eq_nthElem_iff hT hi).mpr ⟨hy, hc⟩
  · rintro rfl
    exact (nthElem_spec hT hi).1

theorem not_mem_of_countBelow_eq_ncard (hT : T.Finite) {y : ℝ} (hc : countBelow T y = T.ncard) :
    y ∉ T := fun hy => absurd hc (countBelow_lt_ncard hT hy).ne

end NLQCLean
