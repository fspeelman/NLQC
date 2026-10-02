import NLQCLean.Semialgebraic.PurePowerZeros
import NLQCLean.Semialgebraic.PiecewiseC1
import NLQCLean.Semialgebraic.FormatParameters
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Isolated zeros of a nonnegative polynomial

A finite set of isolated zeros of a polynomial `F ≥ 0` of total degree at most
`2D` in `N` variables has at most `(2D+1)^N` points.

Around each zero `p`, `F` is positive on a small sphere. For small `ε > 0` the
polynomial `G = F + ε Σᵢ xᵢ^{2D+2}` is smaller at `p` than anywhere on that
sphere, so it has an interior local minimum `q_p` in the ball. All partial
derivatives of `G` vanish at `q_p`, and they form a pure-power system with
leading forms `ε (2D+2) xᵢ^{2D+1}`, whose common zeros number at most
`(2D+1)^N` (`PurePowerZeros`). No Sard theorem, genericity, implicit function
theorem or connected components are used.
-/

namespace NLQCLean.PurePowerZeros

open MvPolynomial Filter Metric Topology

variable {N : ℕ}

/-- **Local minimum.** At a local minimum of a polynomial function every partial
derivative vanishes. -/
theorem eval_pderiv_eq_zero_of_isLocalMin (G : MvPolynomial (Fin N) ℝ) {q : Fin N → ℝ}
    (h : IsLocalMin (fun x => eval x G) q) (i : Fin N) : eval q (pderiv i G) = 0 := by
  have hd := hasDerivAt_eval_update G q i (q i)
  rw [Function.update_eq_self] at hd
  have hcont : Continuous fun s : ℝ => Function.update q i s :=
    continuous_const.update i continuous_id
  have h' : IsLocalMin (fun x => eval x G) (Function.update q i (q i)) := by
    rwa [Function.update_eq_self]
  have hmin : IsLocalMin (fun s => eval (Function.update q i s) G) (q i) :=
    h'.comp_continuous hcont.continuousAt
  exact hmin.hasDerivAt_eq_zero hd

/-- `pderiv` does not raise the total degree. -/
theorem totalDegree_pderiv_le (p : MvPolynomial (Fin N) ℝ) (i : Fin N) :
    (pderiv i p).totalDegree ≤ p.totalDegree := by
  by_cases h : pderiv i p = 0
  · rw [h, totalDegree_zero]; exact Nat.zero_le _
  · exact (totalDegree_pderiv_lt h).le

/-- The perturbation `G_ε = F + ε Σⱼ xⱼ^{e+1}`. -/
noncomputable def perturbation (F : MvPolynomial (Fin N) ℝ) (ε : ℝ) (e : ℕ) :
    MvPolynomial (Fin N) ℝ :=
  F + C ε * ∑ j, X j ^ (e + 1)

theorem eval_perturbation (F : MvPolynomial (Fin N) ℝ) (ε : ℝ) (e : ℕ) (x : Fin N → ℝ) :
    eval x (perturbation F ε e) = eval x F + ε * ∑ j, x j ^ (e + 1) := by
  simp [perturbation]

theorem pderiv_perturbation (F : MvPolynomial (Fin N) ℝ) (ε : ℝ) (e : ℕ) (i : Fin N) :
    pderiv i (perturbation F ε e) = C (ε * (e + 1)) * X i ^ e + pderiv i F := by
  classical
  have hsum : pderiv i (∑ j, X j ^ (e + 1) : MvPolynomial (Fin N) ℝ) =
      C ((e : ℝ) + 1) * X i ^ e := by
    rw [map_sum, Finset.sum_eq_single i]
    · rw [Derivation.leibniz_pow, pderiv_X_self, smul_eq_mul, mul_one, Nat.add_sub_cancel,
        nsmul_eq_mul]
      simp [map_add, map_natCast]
    · intro j _ hji
      rw [Derivation.leibniz_pow, pderiv_X_of_ne hji]
      simp
    · simp
  rw [perturbation, map_add, pderiv_C_mul, hsum, add_comm, ← mul_assoc, ← map_mul]

/-- The partial derivatives of the perturbation form a pure-power system. -/
theorem purePowerSystem_pderiv_perturbation {F : MvPolynomial (Fin N) ℝ} {D : ℕ}
    (hF : F.totalDegree ≤ 2 * D) {ε : ℝ} (hε : ε ≠ 0) :
    PurePowerSystem (2 * D + 1) fun i => pderiv i (perturbation F ε (2 * D + 1)) := by
  intro i
  refine ⟨ε * ((2 * D + 1 : ℕ) + 1), mul_ne_zero hε (by positivity), pderiv i F,
    pderiv_perturbation F ε _ i, ?_⟩
  exact lt_of_le_of_lt ((totalDegree_pderiv_le F i).trans hF) (by omega)

theorem sum_pow_nonneg (D : ℕ) (x : Fin N → ℝ) : 0 ≤ ∑ j, x j ^ (2 * D + 1 + 1) :=
  Finset.sum_nonneg fun j _ => Even.pow_nonneg ⟨D + 1, by ring⟩ _

/-- Around one isolated zero, the perturbation has an interior local minimum for
every small `ε > 0`. -/
theorem eventually_exists_isLocalMin_perturbation {F : MvPolynomial (Fin N) ℝ} (D : ℕ)
    {p : Fin N → ℝ} (hp : eval p F = 0) {r : ℝ} (hr : 0 < r)
    (hpos : ∀ x ∈ sphere p r, 0 < eval x F) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ q ∈ ball p r,
      IsLocalMin (fun x => eval x (perturbation F ε (2 * D + 1))) q := by
  -- A positive lower bound for `F` on the sphere.
  obtain ⟨δ, hδ, hδF⟩ : ∃ δ > 0, ∀ x ∈ sphere p r, δ ≤ eval x F := by
    rcases (sphere p r).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_sphere p r).exists_isMinOn hne
        (MvPolynomial.continuous_eval F).continuousOn
      exact ⟨eval x₀ F, hpos x₀ hx₀, fun x hx => hmin hx⟩
  set P : ℝ := ∑ j, p j ^ (2 * D + 1 + 1) with hP
  have hP0 : 0 ≤ P := sum_pow_nonneg D p
  have hlim : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * P < δ := by
    have hc : Tendsto (fun ε : ℝ => ε * P) (𝓝[>] 0) (𝓝 (0 * P)) :=
      (tendsto_id.mul_const P).mono_left nhdsWithin_le_nhds
    rw [zero_mul] at hc
    exact hc.eventually (gt_mem_nhds hδ)
  filter_upwards [hlim, self_mem_nhdsWithin] with ε hεP hε
  have hε0 : (0 : ℝ) < ε := hε
  set g : (Fin N → ℝ) → ℝ := fun x => eval x (perturbation F ε (2 * D + 1)) with hg
  have hgcont : Continuous g := MvPolynomial.continuous_eval _
  obtain ⟨q, hq, hqmin⟩ := (isCompact_closedBall p r).exists_isMinOn
    (nonempty_closedBall.mpr hr.le) hgcont.continuousOn
  have hgp : g p = ε * P := by
    simp only [hg, eval_perturbation, hp, zero_add, hP]
  have hqball : q ∈ ball p r := by
    rcases lt_or_eq_of_le (mem_closedBall.mp hq) with h | h
    · exact mem_ball.mpr h
    · exfalso
      have hqs : q ∈ sphere p r := mem_sphere.mpr h
      have h1 : δ ≤ g q := by
        simp only [hg, eval_perturbation]
        have := mul_nonneg hε0.le (sum_pow_nonneg D q)
        linarith [hδF q hqs]
      have h2 : g q ≤ g p := hqmin (mem_closedBall_self hr.le)
      linarith
  refine ⟨q, hqball, hqmin.isLocalMin ?_⟩
  exact mem_of_superset (isOpen_ball.mem_nhds hqball) ball_subset_closedBall

/-- **Isolated zeros of a nonnegative polynomial.** A finite set of isolated
zeros of `F ≥ 0` with `deg F ≤ 2D` in `N` variables has at most `(2D+1)^N`
points. -/
theorem card_isolatedZeros_le {F : MvPolynomial (Fin N) ℝ} {D : ℕ}
    (hF : F.totalDegree ≤ 2 * D) (hnn : ∀ x, 0 ≤ eval x F) (T : Finset (Fin N → ℝ))
    (hT : ∀ p ∈ T, eval p F = 0 ∧ ∀ᶠ x in 𝓝[≠] p, eval x F ≠ 0) :
    T.card ≤ (2 * D + 1) ^ N := by
  classical
  -- A common radius: punctured balls free of zeros, and pairwise disjoint balls.
  obtain ⟨r, hr, hiso, hsep⟩ : ∃ r > 0, (∀ p ∈ T, ∀ x ∈ closedBall p r, x ≠ p → eval x F ≠ 0) ∧
      ∀ p ∈ T, ∀ p' ∈ T, p ≠ p' → 2 * r < dist p p' := by
    have h1 : ∀ p ∈ T, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ∀ x ∈ closedBall p r, x ≠ p → eval x F ≠ 0 := by
      intro p hp
      obtain ⟨s, hs, hball⟩ := Metric.mem_nhdsWithin_iff.mp (hT p hp).2
      filter_upwards [Ioo_mem_nhdsGT hs] with r hr x hx hxp
      exact hball ⟨mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hx) hr.2), hxp⟩
    have h2 : ∀ p ∈ T, ∀ p' ∈ T, ∀ᶠ r in 𝓝[>] (0 : ℝ), p ≠ p' → 2 * r < dist p p' := by
      intro p _ p' _
      by_cases hpp : p = p'
      · exact Eventually.of_forall fun _ h => absurd hpp h
      · have hd : 0 < dist p p' / 2 := by have := dist_pos.mpr hpp; linarith
        filter_upwards [Ioo_mem_nhdsGT hd] with r hr _
        linarith [hr.2]
    have h1' := (eventually_all_finset T).mpr h1
    have h2' : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ p ∈ T, ∀ p' ∈ T, p ≠ p' → 2 * r < dist p p' :=
      (eventually_all_finset T).mpr fun p hp => (eventually_all_finset T).mpr (h2 p hp)
    obtain ⟨r, ⟨hr1, hr2⟩, hr0⟩ := ((h1'.and h2').and self_mem_nhdsWithin).exists
    exact ⟨r, hr0, hr1, hr2⟩
  -- One small `ε` that works at every point of `T`.
  have hpos : ∀ p ∈ T, ∀ x ∈ sphere p r, 0 < eval x F := by
    intro p hp x hx
    have hxp : x ≠ p := by
      intro h
      rw [h, mem_sphere, dist_self] at hx
      linarith
    exact lt_of_le_of_ne (hnn x)
      (Ne.symm (hiso p hp x (sphere_subset_closedBall hx) hxp))
  have hev := (eventually_all_finset T).mpr fun p hp =>
    eventually_exists_isLocalMin_perturbation D (hT p hp).1 hr (hpos p hp)
  obtain ⟨ε, hεq, hε⟩ := (hev.and self_mem_nhdsWithin).exists
  have hε0 : ε ≠ 0 := ne_of_gt hε
  choose! q hqball hqmin using hεq
  -- The minimisers are distinct common zeros of the pure-power system.
  have hzero : ∀ p ∈ T, q p ∈ commonZeros fun i => pderiv i (perturbation F ε (2 * D + 1)) :=
    fun p hp i => eval_pderiv_eq_zero_of_isLocalMin _ (hqmin p hp) i
  have hinj : Set.InjOn q T := by
    intro p hp p' hp' hqq
    by_contra hpp
    have h1 := mem_ball.mp (hqball p hp)
    have h2 := mem_ball.mp (hqball p' hp')
    have := hsep p hp p' hp' hpp
    have htri := dist_triangle p (q p') p'
    rw [hqq] at h1
    linarith [dist_comm p (q p')]
  have hcard := card_le_of_subset_commonZeros
    (purePowerSystem_pderiv_perturbation hF hε0) (T.image q)
    (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact hzero p hp)
  rwa [Finset.card_image_of_injOn hinj] at hcard

end NLQCLean.PurePowerZeros

namespace NLQCLean

open MvPolynomial Filter Topology PurePowerZeros

/-- The sum of squares of the equality atoms of a clause. -/
noncomputable def clauseEqualitySquares {n : ℕ} :
    List (PolynomialSignAtom n) → MvPolynomial (Fin n) ℝ
  | [] => 0
  | A :: L => (if A.sign = .zero then A.polynomial ^ 2 else 0) + clauseEqualitySquares L

theorem eval_clauseEqualitySquares_nonneg {n : ℕ} (L : List (PolynomialSignAtom n))
    (y : Fin n → ℝ) : 0 ≤ eval y (clauseEqualitySquares L) := by
  induction L with
  | nil => simp [clauseEqualitySquares]
  | cons A L ih =>
    rw [clauseEqualitySquares, map_add]
    refine add_nonneg ?_ ih
    split_ifs <;> simp [sq_nonneg]

/-- The sum of squares vanishes exactly where every equality atom does. -/
theorem eval_clauseEqualitySquares_eq_zero_iff {n : ℕ} (L : List (PolynomialSignAtom n))
    (y : Fin n → ℝ) :
    eval y (clauseEqualitySquares L) = 0 ↔
      ∀ A ∈ L, A.sign = .zero → eval y A.polynomial = 0 := by
  induction L with
  | nil => simp [clauseEqualitySquares]
  | cons A L ih =>
    have hA : 0 ≤ eval y (if A.sign = .zero then A.polynomial ^ 2 else 0) := by
      split_ifs <;> simp [sq_nonneg]
    rw [clauseEqualitySquares, map_add,
      add_eq_zero_iff_of_nonneg hA (eval_clauseEqualitySquares_nonneg L y), ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    refine and_congr ?_ Iff.rfl
    split_ifs with hz
    · simp [hz]
    · simp [hz]

theorem totalDegree_clauseEqualitySquares_le {n D : ℕ} {L : List (PolynomialSignAtom n)}
    (hL : ∀ A ∈ L, A.polynomial.totalDegree ≤ D) :
    (clauseEqualitySquares L).totalDegree ≤ 2 * D := by
  induction L with
  | nil => simp [clauseEqualitySquares]
  | cons A L ih =>
    rw [clauseEqualitySquares]
    refine (totalDegree_add _ _).trans (max_le ?_ (ih fun B hB => hL B (List.mem_cons_of_mem _ hB)))
    split_ifs
    · exact (totalDegree_pow _ 2).trans
        (Nat.mul_le_mul_left 2 (hL A List.mem_cons_self))
    · rw [totalDegree_zero]; exact Nat.zero_le _

/-- A finite set satisfying one clause has at most `(2D+1)^N` points. -/
theorem ncard_clause_le_of_finite {N D : ℕ} {L : List (PolynomialSignAtom N)}
    (hL : ∀ A ∈ L, A.polynomial.totalDegree ≤ D)
    (hfin : {x : RealEuclidean N | PolynomialSignDNF.clauseHolds L x}.Finite) :
    {x : RealEuclidean N | PolynomialSignDNF.clauseHolds L x}.ncard ≤ (2 * D + 1) ^ N := by
  classical
  set T := {x : RealEuclidean N | PolynomialSignDNF.clauseHolds L x} with hTdef
  set T' : Set (Fin N → ℝ) := (fun y => WithLp.toLp 2 y) ⁻¹' T with hT'def
  have hinj : Function.Injective (fun y : Fin N → ℝ => (WithLp.toLp 2 y : RealEuclidean N)) :=
    fun _ _ h => by simpa using congrArg WithLp.ofLp h
  have hT'fin : T'.Finite := hfin.preimage hinj.injOn
  have hT'card : T'.ncard = T.ncard := by
    have himage : (fun y => (WithLp.toLp 2 y : RealEuclidean N)) '' T' = T := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨WithLp.ofLp x, by simpa [hT'def] using hx, by simp⟩
    rw [← himage, Set.ncard_image_of_injective _ hinj]
  have hholds : ∀ y : Fin N → ℝ, ∀ A : PolynomialSignAtom N,
      A.Holds (WithLp.toLp 2 y) ↔ A.sign.Holds (eval y A.polynomial) := by
    intro y A
    rfl
  -- Every point of `T'` is an isolated zero of the equality squares.
  have hiso : ∀ p ∈ T', eval p (clauseEqualitySquares L) = 0 ∧
      ∀ᶠ y in 𝓝[≠] p, eval y (clauseEqualitySquares L) ≠ 0 := by
    intro p hp
    have hpL : ∀ A ∈ L, A.sign.Holds (eval p A.polynomial) := fun A hA =>
      (hholds p A).mp (hp A hA)
    refine ⟨(eval_clauseEqualitySquares_eq_zero_iff L p).mpr fun A hA hz => by
      have := hpL A hA; rw [hz] at this; exact this, ?_⟩
    -- Strict atoms keep their signs near `p`.
    have hstrict : ∀ᶠ y in 𝓝 p, ∀ A ∈ L.toFinset, A.sign ≠ .zero →
        A.sign.Holds (eval y A.polynomial) := by
      refine (eventually_all_finset _).mpr fun A hA => ?_
      have hcont := (MvPolynomial.continuous_eval A.polynomial).continuousAt (x := p)
      have hpA := hpL A (List.mem_toFinset.mp hA)
      cases hsign : A.sign with
      | zero => exact Eventually.of_forall fun _ h => absurd rfl h
      | negative =>
        rw [hsign] at hpA
        exact (hcont.eventually (gt_mem_nhds hpA)).mono fun y hy _ => hy
      | positive =>
        rw [hsign] at hpA
        exact (hcont.eventually (lt_mem_nhds hpA)).mono fun y hy _ => hy
    -- Away from `p`, no other point of the finite set `T'`.
    have haway : ∀ᶠ y in 𝓝 p, y ∉ T' \ {p} :=
      (hT'fin.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl
    filter_upwards [nhdsWithin_le_nhds (hstrict.and haway), self_mem_nhdsWithin]
      with y ⟨hys, hya⟩ hyp hzero
    have hyT : y ∈ T' := by
      intro A hA
      rw [hholds]
      by_cases hz : A.sign = .zero
      · rw [hz]
        exact (eval_clauseEqualitySquares_eq_zero_iff L y).mp hzero A hA hz
      · exact hys A (List.mem_toFinset.mpr hA) hz
    exact hya ⟨hyT, hyp⟩
  obtain ⟨S, hS⟩ := hT'fin.exists_finset_coe
  have hcard := card_isolatedZeros_le (totalDegree_clauseEqualitySquares_le hL)
    (eval_clauseEqualitySquares_nonneg L) S (fun p hp => hiso p (hS ▸ hp))
  rw [← hT'card, ← hS, Set.ncard_coe_finset]
  exact hcard

theorem ncard_biUnion_finset_le {α ι : Type*} (s : Finset ι) (t : ι → Set α) :
    (⋃ i ∈ s, t i).ncard ≤ ∑ i ∈ s, (t i).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

/-- **Point count for finite sets of bounded format.** A finite set with a sign
description of format `(c, D)` in `ℝ^N` has at most `(c+1)(2D+1)^N` points.
This replaces the component bound wherever only finite sets are counted. -/
theorem HasSemialgebraicFormat.ncard_le_of_finite {N c D : ℕ} {S : Set (RealEuclidean N)}
    (hS : HasSemialgebraicFormat S c D) (hfin : S.Finite) :
    S.ncard ≤ (c + 1) * (2 * D + 1) ^ N := by
  classical
  obtain ⟨F, hFS, hF⟩ := hS
  obtain ⟨G, hGF, hlen, -, hdeg⟩ := hF.exists_bounded_counts
  set T : List (PolynomialSignAtom N) → Set (RealEuclidean N) :=
    fun L => {x | PolynomialSignDNF.clauseHolds L x} with hTdef
  have hTS : ∀ L ∈ G.clauses, T L ⊆ S := fun L hL x hx => by
    rw [← hFS, ← hGF]; exact ⟨L, hL, hx⟩
  have hTfin : ∀ L ∈ G.clauses, (T L).Finite := fun L hL => hfin.subset (hTS L hL)
  have hSU : S ⊆ ⋃ L ∈ G.clauses.toFinset, T L := by
    intro x hx
    rw [← hFS, ← hGF] at hx
    obtain ⟨L, hL, hxL⟩ := hx
    exact Set.mem_biUnion (List.mem_toFinset.mpr hL) hxL
  calc S.ncard ≤ (⋃ L ∈ G.clauses.toFinset, T L).ncard :=
        Set.ncard_le_ncard hSU (Set.Finite.biUnion G.clauses.toFinset.finite_toSet
          fun L hL => hTfin L (List.mem_toFinset.mp hL))
    _ ≤ ∑ L ∈ G.clauses.toFinset, (T L).ncard := ncard_biUnion_finset_le _ _
    _ ≤ ∑ _L ∈ G.clauses.toFinset, (2 * D + 1) ^ N :=
        Finset.sum_le_sum fun L hL =>
          ncard_clause_le_of_finite (hdeg L (List.mem_toFinset.mp hL))
            (hTfin L (List.mem_toFinset.mp hL))
    _ = G.clauses.toFinset.card * (2 * D + 1) ^ N := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (c + 1) * (2 * D + 1) ^ N :=
        Nat.mul_le_mul_right _ ((List.toFinset_card_le _).trans hlen)

end NLQCLean
