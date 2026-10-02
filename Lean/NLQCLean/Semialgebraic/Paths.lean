import NLQCLean.Semialgebraic.CurveSelection

/-!
# Semialgebraic paths in connected semialgebraic sets (`fact:paths`)

Any two points of a connected semialgebraic set are joined by a continuous
semialgebraic path inside it. The set is a finite union of semialgebraically
path-connected pieces; the points reachable from a base point form a union of
pieces, and curve selection shows that this union and its complement are
separated, so by connectedness everything is reachable.
-/

noncomputable section

namespace NLQCLean

open Set

variable {m : ℕ}

theorem IsSAPath.reverse {c : ℝ → Fin m → ℝ} (hc : IsSAPath c) : IsSAPath fun t => c (1 - t) := by
  refine ⟨hc.continuousOn.comp (continuous_const.sub continuous_id).continuousOn
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
  refine (hc.graph.preimage (Option.elim · (1 - MvPolynomial.X none) fun i =>
    MvPolynomial.X (some i))).congr fun h => ?_
  simp only [mem_ofPred_eq, pathGraph, mem_Icc, Option.elim, map_sub, map_one,
    MvPolynomial.eval_X]
  constructor
  · rintro ⟨⟨h0, h1⟩, hi⟩
    exact ⟨⟨by linarith, by linarith⟩, hi⟩
  · rintro ⟨⟨h0, h1⟩, hi⟩
    exact ⟨⟨by linarith, by linarith⟩, hi⟩

/-- Concatenation of paths. -/
def pathTrans (c₁ c₂ : ℝ → Fin m → ℝ) : ℝ → Fin m → ℝ :=
  fun t => if t ≤ 1 / 2 then c₁ (2 * t) else c₂ (2 * t - 1)

theorem IsSAPath.trans {c₁ c₂ : ℝ → Fin m → ℝ} (h₁ : IsSAPath c₁) (h₂ : IsSAPath c₂)
    (h : c₁ 1 = c₂ 0) : IsSAPath (pathTrans c₁ c₂) := by
  classical
  refine ⟨?_, ?_⟩
  · have hU : Icc (0 : ℝ) 1 = Icc 0 (1 / 2) ∪ Icc (1 / 2) 1 :=
      (Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)).symm
    rw [hU]
    have hm₁ : MapsTo (fun t : ℝ => 2 * t) (Icc 0 (1 / 2)) (Icc 0 1) :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hm₂ : MapsTo (fun t : ℝ => 2 * t - 1) (Icc (1 / 2) 1) (Icc 0 1) :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · refine (h₁.continuousOn.comp (by fun_prop : Continuous fun t : ℝ => 2 * t).continuousOn
        hm₁).congr fun t ht => ?_
      show pathTrans c₁ c₂ t = c₁ (2 * t)
      unfold pathTrans
      rw [ite_eq_left ht.2]
    · refine (h₂.continuousOn.comp (by fun_prop : Continuous fun t : ℝ => 2 * t - 1).continuousOn
        hm₂).congr fun t ht => ?_
      show pathTrans c₁ c₂ t = c₂ (2 * t - 1)
      unfold pathTrans
      rcases eq_or_lt_of_le ht.1 with h0 | hlt
      · subst h0
        rw [ite_eq_left le_rfl]
        norm_num
        exact h
      · rw [ite_eq_right (not_le.mpr hlt)]
  · let Q₁ : Option (Fin m) → MvPolynomial (Option (Fin m)) ℝ :=
      fun o => Option.elim o (2 * MvPolynomial.X none) fun i => MvPolynomial.X (some i)
    let Q₂ : Option (Fin m) → MvPolynomial (Option (Fin m)) ℝ :=
      fun o => Option.elim o (2 * MvPolynomial.X none - 1) fun i => MvPolynomial.X (some i)
    have hA : SAOn {x : Option (Fin m) → ℝ | x none ≤ 1 / 2 ∧
        (fun o => MvPolynomial.eval x (Q₁ o)) ∈ pathGraph c₁} :=
      ((SAOn.le (MvPolynomial.X none) (MvPolynomial.C (1 / 2))).congr fun x => by simp; rfl).inter
        (h₁.graph.preimage Q₁)
    have hB : SAOn {x : Option (Fin m) → ℝ | 1 / 2 < x none ∧
        (fun o => MvPolynomial.eval x (Q₂ o)) ∈ pathGraph c₂} :=
      ((SAOn.lt (MvPolynomial.C (1 / 2)) (MvPolynomial.X none)).congr fun x => by simp; rfl).inter
        (h₂.graph.preimage Q₂)
    refine (hA.union hB).congr fun x => ?_
    simp only [mem_union, mem_ofPred_eq, pathGraph, mem_Icc, Q₁, Q₂, Option.elim, map_mul, map_sub,
      map_one, MvPolynomial.eval_X, MvPolynomial.eval_ofNat, pathTrans]
    by_cases ht : x none ≤ 1 / 2
    · simp only [ht, ite_true, true_and, not_lt.mpr ht, false_and, or_false]
      constructor
      · rintro ⟨⟨h0, h1⟩, hi⟩
        exact ⟨⟨by linarith, by linarith⟩, hi⟩
      · rintro ⟨⟨h0, h1⟩, hi⟩
        exact ⟨⟨by linarith, by linarith⟩, hi⟩
    · simp only [ht, ite_false, false_and, not_le.mp ht, true_and, false_or]
      have ht' := not_le.mp ht
      constructor
      · rintro ⟨⟨h0, h1⟩, hi⟩
        exact ⟨⟨by linarith, by linarith⟩, hi⟩
      · rintro ⟨⟨h0, h1⟩, hi⟩
        exact ⟨⟨by linarith, by linarith⟩, hi⟩

theorem pathTrans_zero {c₁ c₂ : ℝ → Fin m → ℝ} : pathTrans c₁ c₂ 0 = c₁ 0 := by
  simp [pathTrans]

theorem pathTrans_one {c₁ c₂ : ℝ → Fin m → ℝ} : pathTrans c₁ c₂ 1 = c₂ 1 := by
  simp [pathTrans]
  norm_num

theorem mapsTo_pathTrans {c₁ c₂ : ℝ → Fin m → ℝ} {S : Set (Fin m → ℝ)}
    (h₁ : MapsTo c₁ (Icc 0 1) S) (h₂ : MapsTo c₂ (Icc 0 1) S) :
    MapsTo (pathTrans c₁ c₂) (Icc 0 1) S := by
  intro t ht
  unfold pathTrans
  split_ifs with h
  · exact h₁ ⟨by linarith [ht.1], by linarith⟩
  · exact h₂ ⟨by linarith [not_le.mp h], by linarith [ht.2]⟩

/-- Joinable points. -/
def SAJoined (S : Set (Fin m → ℝ)) (x y : Fin m → ℝ) : Prop :=
  ∃ c : ℝ → Fin m → ℝ, IsSAPath c ∧ c 0 = x ∧ c 1 = y ∧ MapsTo c (Icc 0 1) S

theorem SAJoined.trans {S : Set (Fin m → ℝ)} {x y z : Fin m → ℝ} (h₁ : SAJoined S x y)
    (h₂ : SAJoined S y z) : SAJoined S x z := by
  obtain ⟨c₁, hc₁, h₁0, h₁1, hm₁⟩ := h₁
  obtain ⟨c₂, hc₂, h₂0, h₂1, hm₂⟩ := h₂
  exact ⟨pathTrans c₁ c₂, hc₁.trans hc₂ (h₁1.trans h₂0.symm), pathTrans_zero.trans h₁0,
    pathTrans_one.trans h₂1, mapsTo_pathTrans hm₁ hm₂⟩

/-- A path from a closure point of a piece into the piece. -/
theorem exists_joined_of_mem_closure {S D : Set (Fin m → ℝ)} (hD : SAOn D) (hDS : D ⊆ S)
    {v : Fin m → ℝ} (hv : v ∈ S) (hvD : v ∈ closure D) :
    ∃ w ∈ D, SAJoined S v w ∧ SAJoined S w v := by
  obtain ⟨γ, hγ, hγ0, hγD⟩ := curve_selection hD hvD
  have hmaps : MapsTo γ (Icc 0 1) S := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · rw [← h0, hγ0]
      exact hv
    · exact hDS (hγD t ⟨hpos, ht.2⟩)
  have h1 : γ 1 ∈ D := hγD 1 ⟨zero_lt_one, le_refl 1⟩
  refine ⟨γ 1, h1, ⟨γ, hγ, hγ0, rfl, hmaps⟩, ⟨fun t => γ (1 - t), hγ.reverse, by simp, ?_, ?_⟩⟩
  · simp [hγ0]
  · intro t ht
    exact hmaps ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- **Connected semialgebraic sets are semialgebraically path connected.** -/
theorem SAOn.saPathConnected_of_isPreconnected {S : Set (Fin m → ℝ)} (hS : SAOn S)
    (hc : IsPreconnected S) : SAPathConnected S := by
  obtain ⟨𝒟, hfin, hprop, hSeq⟩ := exists_saPathConnected_decomposition m S hS
  have hDS : ∀ D ∈ 𝒟, D ⊆ S := fun D hD => hSeq ▸ subset_sUnion_of_mem hD
  intro x hx
  let R : Set (Fin m → ℝ) := {y | SAJoined S x y}
  have hRS : R ⊆ S := by
    rintro y ⟨c, -, -, hc1, hm⟩
    rw [← hc1]
    exact hm ⟨zero_le_one, le_refl 1⟩
  have hxR : x ∈ R := ⟨fun _ => x, IsSAPath.const x, rfl, rfl, fun _ _ => hx⟩
  -- a piece meeting `R` lies in `R`
  have hpiece : ∀ D ∈ 𝒟, (D ∩ R).Nonempty → D ⊆ R := by
    rintro D hD ⟨y, hyD, hyR⟩ z hz
    obtain ⟨c, hc, hc0, hc1, hm⟩ := (hprop D hD).2 y hyD z hz
    exact SAJoined.trans hyR ⟨c, hc, hc0, hc1, hm.mono_right (hDS D hD)⟩
  let 𝒟R := {D ∈ 𝒟 | (D ∩ R).Nonempty}
  let 𝒟V := {D ∈ 𝒟 | ¬ (D ∩ R).Nonempty}
  have hpre := isPreconnected_closed_iff.mp hc (closure (⋃₀ 𝒟R)) (closure (⋃₀ 𝒟V))
    isClosed_closure isClosed_closure
  have hcover : S ⊆ closure (⋃₀ 𝒟R) ∪ closure (⋃₀ 𝒟V) := by
    intro s hs
    rw [hSeq] at hs
    obtain ⟨D, hD, hsD⟩ := hs
    by_cases hDR : (D ∩ R).Nonempty
    · exact Or.inl (subset_closure ⟨D, ⟨hD, hDR⟩, hsD⟩)
    · exact Or.inr (subset_closure ⟨D, ⟨hD, hDR⟩, hsD⟩)
  have hxt : (S ∩ closure (⋃₀ 𝒟R)).Nonempty := by
    have hx' := hx
    rw [hSeq] at hx'
    obtain ⟨D, hD, hxD⟩ := hx'
    exact ⟨x, hx, subset_closure ⟨D, ⟨hD, x, hxD, hxR⟩, hxD⟩⟩
  intro y hy
  by_contra hyR
  have hyt : (S ∩ closure (⋃₀ 𝒟V)).Nonempty := by
    have hy' := hy
    rw [hSeq] at hy'
    obtain ⟨D, hD, hyD⟩ := hy'
    refine ⟨y, hy, subset_closure ⟨D, ⟨hD, fun hDR => hyR (hpiece D hD hDR hyD)⟩, hyD⟩⟩
  obtain ⟨s, hs, hs1, hs2⟩ := hpre hcover hxt hyt
  rw [(hfin.subset fun D hD => hD.1).closure_sUnion, mem_iUnion₂] at hs1 hs2
  obtain ⟨D₁, ⟨hD₁, hD₁R⟩, hsD₁⟩ := hs1
  obtain ⟨D₂, ⟨hD₂, hD₂R⟩, hsD₂⟩ := hs2
  -- `s` is reachable through `D₁`
  obtain ⟨w₁, hw₁, -, hw₁s⟩ := exists_joined_of_mem_closure (hprop D₁ hD₁).1 (hDS D₁ hD₁) hs hsD₁
  have hsR : s ∈ R := SAJoined.trans (hpiece D₁ hD₁ hD₁R hw₁) hw₁s
  -- hence so is a point of `D₂`
  obtain ⟨w₂, hw₂, hsw₂, -⟩ := exists_joined_of_mem_closure (hprop D₂ hD₂).1 (hDS D₂ hD₂) hs hsD₂
  exact hD₂R ⟨w₂, hw₂, SAJoined.trans hsR hsw₂⟩

/-- **`fact:paths`.** Any two points of a connected semialgebraic subset of
`ℝⁿ` are joined by a continuous path inside it whose graph over `[0,1]` is
semialgebraic. -/
theorem fact_paths {n : ℕ} {S : Set (RealEuclidean n)} (hS : Semialgebraic S)
    (hc : IsPreconnected S) {x y : RealEuclidean n} (hx : x ∈ S) (hy : y ∈ S) :
    ∃ c : ℝ → RealEuclidean n, ContinuousOn c (Icc 0 1) ∧ c 0 = x ∧ c 1 = y ∧
      MapsTo c (Icc 0 1) S ∧
      Semialgebraic {p : RealEuclidean (n + 1) | p 0 ∈ Icc (0 : ℝ) 1 ∧
        ∀ i : Fin n, p i.succ = c (p 0) i} := by
  have hS₀ : SAOn ((WithLp.toLp 2) ⁻¹' S) := (semialgebraic_iff_saOn S).mp hS
  have hc₀ : IsPreconnected ((WithLp.toLp 2) ⁻¹' S : Set (Fin n → ℝ)) := by
    have h := hc.image WithLp.ofLp (PiLp.continuous_ofLp 2 _).continuousOn
    convert h using 1
    ext g
    simp only [mem_preimage, mem_image]
    exact ⟨fun hg => ⟨_, hg, rfl⟩, by rintro ⟨z, hz, rfl⟩; simpa using hz⟩
  obtain ⟨c, hcp, hc0, hc1, hmaps⟩ :=
    hS₀.saPathConnected_of_isPreconnected hc₀ (WithLp.ofLp x) (by simpa using hx)
      (WithLp.ofLp y) (by simpa using hy)
  refine ⟨fun t => WithLp.toLp 2 (c t), (PiLp.continuous_toLp 2 _).comp_continuousOn hcp.continuousOn,
    by simp [hc0], by simp [hc1], fun t ht => hmaps ht, ?_⟩
  rw [semialgebraic_iff_saOn]
  let e : Option (Fin n) → Fin (n + 1) := fun o => o.elim 0 Fin.succ
  refine (hcp.graph.comap e).congr fun g => ?_
  simp [pathGraph, e]

end NLQCLean
