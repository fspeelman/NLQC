import NLQCLean.Arithmetic.EliminationSize
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Iterated resultant elimination with explicit bounds

Let `P₁, …, P_s ∈ ℤ[y, c][z₁, …, zₙ]` have joint degree at most `D`, coefficient mass at
most `M` and `s ≤ D`, and assume they have no common zero over an algebraic closure of
`ℚ(y, c)`, the generic parameter point. Then some nonzero `α ∈ ℤ[y, c]`, of degree at most
`elimDeg n D` and coefficient mass at most `elimMass n D M`, vanishes at every parameter
value over which the `Pᵢ` have a common zero, in any commutative ring.

Each step shears one nonzero polynomial to a constant leading coefficient and takes the
`u`-coefficients of the Kronecker resultant `Res_{z₀}(f, Σ uⁱ Gᵢ)`.
-/

namespace NLQCLean.Elimination

open MvPolynomial

/-- The algebraic closure of `ℚ(y, c)`, home of the generic parameter point. -/
abbrev GenericField := AlgebraicClosure (FractionRing Par)

theorem algebraMap_generic_injective : Function.Injective (algebraMap Par GenericField) := by
  rw [IsScalarTower.algebraMap_eq Par (FractionRing Par) GenericField]
  exact (algebraMap (FractionRing Par) GenericField).injective.comp
    (IsFractionRing.injective Par (FractionRing Par))

/-- Degree bound after `n` elimination steps. -/
def elimDeg : ℕ → ℕ → ℕ
  | 0, D => D
  | n + 1, D => elimDeg n (5 * D ^ 2)

/-- Coefficient-mass bound after `n` elimination steps. -/
def elimMass : ℕ → ℕ → ℕ → ℕ
  | 0, _, M => M
  | n + 1, D, M => elimMass n (5 * D ^ 2) ((2 * D).factorial * (D * (M * (D + 1) ^ D)) ^ (2 * D))

theorem le_elimDeg : ∀ (n D : ℕ), D ≤ elimDeg n D
  | 0, _ => le_rfl
  | n + 1, D => by
    refine le_trans ?_ (le_elimDeg n _)
    nlinarith

theorem one_le_step {D M : ℕ} (hD : 1 ≤ D) (_hM : 1 ≤ M) :
    M ≤ (2 * D).factorial * (D * (M * (D + 1) ^ D)) ^ (2 * D) := by
  have h1 : M ≤ D * (M * (D + 1) ^ D) := by
    calc M = 1 * (M * 1) := by ring
      _ ≤ D * (M * (D + 1) ^ D) :=
        Nat.mul_le_mul hD (Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega)))
  have h2 : D * (M * (D + 1) ^ D) ≤ (D * (M * (D + 1) ^ D)) ^ (2 * D) :=
    Nat.le_self_pow (by omega) _
  calc M ≤ (D * (M * (D + 1) ^ D)) ^ (2 * D) := h1.trans h2
    _ ≤ _ := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)

theorem le_elimMass : ∀ (n D M : ℕ), 1 ≤ D → 1 ≤ M → M ≤ elimMass n D M
  | 0, _, _, _, _ => le_rfl
  | n + 1, D, M, hD, hM => by
    have hstep := one_le_step hD hM
    refine hstep.trans (le_elimMass n _ _ (by nlinarith) (hM.trans hstep))

theorem elimDeg_le : ∀ (n D : ℕ), elimDeg n D ≤ (5 * D) ^ (2 ^ n)
  | 0, D => by simp only [elimDeg, pow_zero, pow_one]; omega
  | n + 1, D => by
    calc elimDeg (n + 1) D = elimDeg n (5 * D ^ 2) := rfl
      _ ≤ (5 * (5 * D ^ 2)) ^ (2 ^ n) := elimDeg_le n _
      _ = (5 * D) ^ (2 ^ (n + 1)) := by
          rw [pow_succ 2 n, mul_comm (2 ^ n) 2, pow_mul]
          congr 1
          ring

theorem le_pow_self_of_two_le {Λ D : ℕ} (hΛ : 2 ≤ Λ) : D + 1 ≤ Λ ^ D :=
  (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left hΛ D)

/-- The masses stay below `Λ ^ (degree³)`. -/
theorem elimMass_le : ∀ (n D M Λ : ℕ), 1 ≤ D → 2 ≤ Λ → M ≤ Λ ^ (D ^ 3) →
    elimMass n D M ≤ Λ ^ (elimDeg n D ^ 3)
  | 0, D, M, Λ, _, _, hM => hM
  | n + 1, D, M, Λ, hD, hΛ, hM => by
    refine elimMass_le n (5 * D ^ 2) _ Λ (by nlinarith) hΛ ?_
    have hΛ1 : 1 ≤ Λ := by omega
    have hDΛ : D + 1 ≤ Λ ^ D := le_pow_self_of_two_le hΛ
    have h2D : 2 * D ≤ Λ ^ (2 * D) := (Nat.le_succ _).trans (le_pow_self_of_two_le hΛ)
    have hfac : (2 * D).factorial ≤ Λ ^ (4 * D ^ 2) :=
      calc (2 * D).factorial ≤ (2 * D) ^ (2 * D) := Nat.factorial_le_pow _
        _ ≤ (Λ ^ (2 * D)) ^ (2 * D) := Nat.pow_le_pow_left h2D _
        _ = Λ ^ (4 * D ^ 2) := by rw [← pow_mul]; ring_nf
    have hinner : D * (M * (D + 1) ^ D) ≤ Λ ^ (3 * D ^ 3) :=
      calc D * (M * (D + 1) ^ D) ≤ Λ ^ D * (Λ ^ (D ^ 3) * (Λ ^ D) ^ D) :=
            Nat.mul_le_mul ((Nat.le_succ D).trans hDΛ)
              (Nat.mul_le_mul hM (Nat.pow_le_pow_left hDΛ D))
        _ = Λ ^ (D + D ^ 3 + D ^ 2) := by rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
        _ ≤ Λ ^ (3 * D ^ 3) := Nat.pow_le_pow_right hΛ1 (by nlinarith)
    calc (2 * D).factorial * (D * (M * (D + 1) ^ D)) ^ (2 * D)
        ≤ Λ ^ (4 * D ^ 2) * (Λ ^ (3 * D ^ 3)) ^ (2 * D) :=
          Nat.mul_le_mul hfac (Nat.pow_le_pow_left hinner _)
      _ = Λ ^ (4 * D ^ 2 + 6 * D ^ 4) := by rw [← pow_mul, ← pow_add]; ring_nf
      _ ≤ Λ ^ ((5 * D ^ 2) ^ 3) := by
          refine Nat.pow_le_pow_right hΛ1 ?_
          have h1 : D ^ 2 ≤ D ^ 4 := Nat.pow_le_pow_right hD (by norm_num)
          have h2 : D ^ 4 ≤ D ^ 6 := Nat.pow_le_pow_right hD (by norm_num)
          have : (5 * D ^ 2) ^ 3 = 125 * D ^ 6 := by ring
          rw [this]
          omega

/-- Evaluation after splitting off `z₀`. -/
theorem eval₂_cons_eq {n : ℕ} {S : Type*} [CommRing S] (ρ : Par →+* S) (t : S)
    (ζ : Fin n → S) (Q : MvPolynomial (Fin (n + 1)) Par) :
    eval₂ ρ (Fin.cons t ζ) Q = (finSuccEquiv Par n Q).eval₂ (eval₂Hom ρ ζ) t := by
  have h : eval₂Hom ρ (Fin.cons t ζ : Fin (n + 1) → S) =
      (Polynomial.eval₂RingHom (eval₂Hom ρ ζ) t).comp
        (finSuccEquiv Par n).toRingEquiv.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [coe_eval₂Hom, eval₂_C, RingHom.coe_comp, Function.comp_apply,
        RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe]
      rw [show (C r : MvPolynomial (Fin (n + 1)) Par) = algebraMap Par _ r from rfl,
        AlgEquiv.commutes]
      simp
    · cases i using Fin.cases with
      | zero => simp [finSuccEquiv_X_zero]
      | succ j => simp [finSuccEquiv_X_succ]
  exact RingHom.congr_fun h Q

theorem eval₂_shear {n : ℕ} {S : Type*} [CommRing S] (ρ : Par →+* S) (x : Fin (n + 1) → S)
    (a : Fin n → Par) (Q : MvPolynomial (Fin (n + 1)) Par) :
    eval₂ ρ x (shear a Q) = eval₂ ρ (fun i => eval₂ ρ x (shearVariables a i)) Q :=
  eval₂Hom_bind₁ ρ x (shearVariables a) Q

theorem SizeLE.of_rename_inr {n : ℕ} {α : Par} {d M : ℕ}
    (h : SizeLE (MvPolynomial.rename (Sum.inr : Fin 2 → Fin n ⊕ Fin 2) α) d M) :
    SizeLE α d M := by
  have := h.rename (Sum.elim (fun _ => (0 : Fin 2)) id)
  rwa [MvPolynomial.rename_rename,
    show (Sum.elim (fun _ => (0 : Fin 2)) id ∘ Sum.inr : Fin 2 → Fin 2) = id from rfl,
    MvPolynomial.rename_id_apply] at this

/-- **Iterated elimination**, nested form. -/
theorem elim_nested : ∀ (n D M s : ℕ) (P : Fin s → MvPolynomial (Fin n) Par),
    1 ≤ D → 1 ≤ M → s ≤ D → (∀ i, SizeLE (flat n (P i)) D M) →
    (∀ ζ : Fin n → GenericField, ∃ i, eval₂ (algebraMap Par GenericField) ζ (P i) ≠ 0) →
    ∃ α : Par, α ≠ 0 ∧ SizeLE α (elimDeg n D) (elimMass n D M) ∧
      ∀ (S : Type) [CommRing S] (ρ : Par →+* S) (x : Fin n → S),
        (∀ i, eval₂ ρ x (P i) = 0) → ρ α = 0 := by
  intro n
  induction n with
  | zero =>
    intro D M s P hD hM hs hsize hgen
    obtain ⟨i, hi⟩ := hgen Fin.elim0
    have hPi : P i = C ((P i).coeff 0) := eq_C_of_isEmpty (P i)
    refine ⟨(P i).coeff 0, ?_, ?_, ?_⟩
    · intro h0
      apply hi
      rw [hPi, h0]
      simp
    · have := hsize i
      rw [hPi, flat_C] at this
      exact this.of_rename_inr
    · intro S _ ρ x hx
      have := hx i
      rwa [hPi, eval₂_C] at this
  | succ n ih =>
    intro D M s P hD hM hs hsize hgen
    obtain ⟨i0, hi0⟩ := hgen 0
    have hP0 : P i0 ≠ 0 := fun h => hi0 (by rw [h]; simp)
    by_cases hdeg : (P i0).totalDegree = 0
    · obtain ⟨α, hα⟩ : ∃ α, P i0 = C α := ⟨_, totalDegree_eq_zero_iff_eq_C.mp hdeg⟩
      refine ⟨α, ?_, ?_, ?_⟩
      · rintro rfl
        exact hP0 (by rw [hα, C_0])
      · have := hsize i0
        rw [hα, flat_C] at this
        exact this.of_rename_inr.mono (le_elimDeg _ _) (le_elimMass _ _ _ hD hM)
      · intro S _ ρ x hx
        have := hx i0
        rwa [hα, eval₂_C] at this
    obtain ⟨b, hbe, hnat, c, hc0, hlc⟩ := exists_shear_leadingCoeff hP0
    set e := (P i0).totalDegree with he
    set a : Fin n → Par := fun j => (b j : Par) with ha
    set G : Fin s → Polynomial (MvPolynomial (Fin n) Par) :=
      fun i => finSuccEquiv Par n (shear a (P i)) with hG
    set f := G i0 with hf
    have hshdeg : ∀ i, (flat (n + 1) (shear a (P i))).totalDegree ≤ D := fun i => by
      rw [flat_shear]
      exact (PhysicalPolynomial.totalDegree_bind₁_le_of_linear_variables _
        (fun v => (SizeLE.flatShearVariables b hbe v).1) _).trans (hsize i).1
    have heD : e ≤ D := by
      rw [← hnat]
      refine (natDegree_le_totalDegree_flatU n _).trans ?_
      rw [flatU_finSuccEquiv]
      exact (totalDegree_rename_le _ _).trans (hshdeg i0)
    have hbD : ∀ j, b j ≤ D := fun j => (hbe j).trans heD
    set M1 := M * (D + 1) ^ D with hM1
    have hsh : ∀ i, SizeLE (flat (n + 1) (shear a (P i))) D M1 := fun i =>
      (hsize i).flat_shear b hbD
    have hGc : ∀ i k, SizeLE (flat n ((G i).coeff k)) D M1 := fun i k =>
      (hsh i).flatU_finSuccEquiv.flat_coeff k
    have hGdeg : ∀ i, (G i).natDegree ≤ D := fun i =>
      (natDegree_le_totalDegree_flatU n _).trans (hsh i).flatU_finSuccEquiv.1
    have hM1pos : 1 ≤ D * M1 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by omega) (by positivity)))
    set R := eliminant f G f.natDegree D with hR
    set M' := (2 * D).factorial * (D * M1) ^ (2 * D) with hM'
    have hRsize : SizeLE (flatU n R) (4 * D ^ 2) M' := by
      have := SizeLE.flatU_eliminant (m := f.natDegree) (n' := D) hD hs (hGc i0) hGc
      refine this.mono ?_ ?_
      · rw [hnat]; nlinarith
      · rw [hnat]
        exact Nat.mul_le_mul (Nat.factorial_le (by omega))
          (Nat.pow_le_pow_right hM1pos (by omega))
    have hRzero : ∀ k, 4 * D ^ 2 < k → R.coeff k = 0 := fun k hk =>
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (((natDegree_le_totalDegree_flatU n R).trans hRsize.1).trans_lt hk)
    have hM'pos : 1 ≤ M' :=
      Nat.mul_le_mul (Nat.factorial_pos _) (Nat.one_le_pow _ _ hM1pos) |>.trans' (by simp)
    have hgenR : ∀ ζ' : Fin n → GenericField, ∃ k : Fin (4 * D ^ 2 + 1),
        eval₂ (algebraMap Par GenericField) ζ' (R.coeff k) ≠ 0 := by
      intro ζ'
      by_contra! hall
      let φ := eval₂Hom (algebraMap Par GenericField) ζ'
      have hφR : ∀ k, φ (R.coeff k) = 0 := fun k => by
        by_cases hk : k ≤ 4 * D ^ 2
        · exact hall ⟨k, by omega⟩
        · rw [hRzero k (by omega), map_zero]
      have hlcφ : φ f.leadingCoeff ≠ 0 := by
        rw [hlc]
        simp only [φ, coe_eval₂Hom, eval₂_C]
        exact (map_ne_zero_iff _ algebraMap_generic_injective).mpr hc0
      obtain ⟨t, -, hGt⟩ := exists_common_root_of_eliminant hGdeg φ hlcφ hφR
      obtain ⟨i, hi⟩ := hgen (fun v => eval₂ (algebraMap Par GenericField)
        (Fin.cons t ζ' : Fin (n + 1) → GenericField) (shearVariables a v))
      apply hi
      rw [← eval₂_shear, eval₂_cons_eq]
      exact hGt i
    obtain ⟨α, hα0, hαsize, hαvan⟩ := ih (5 * D ^ 2) M' (4 * D ^ 2 + 1)
      (fun k => R.coeff k) (by nlinarith) hM'pos (by nlinarith)
      (fun k => (hRsize.flat_coeff k).mono (by nlinarith) le_rfl) hgenR
    refine ⟨α, hα0, hαsize, ?_⟩
    intro S _ ρ x hx
    let xs : Fin (n + 1) → S := Fin.cons (x 0) (fun j => x j.succ - (b j : S) * x 0)
    have hshv : (fun v => eval₂ ρ xs (shearVariables a v)) = x := by
      funext v
      cases v using Fin.cases with
      | zero => simp [xs, shearVariables]
      | succ j => simp [xs, shearVariables, ha]
    have hzero : ∀ i, eval₂ ρ xs (shear a (P i)) = 0 := fun i => by
      rw [eval₂_shear, hshv]; exact hx i
    have hGψ : ∀ i, (G i).eval₂ (eval₂Hom ρ (Fin.tail xs)) (xs 0) = 0 := fun i => by
      rw [hG, ← eval₂_cons_eq, Fin.cons_self_tail]
      exact hzero i
    have hcoef := map_coeff_eliminant_eq_zero (by rw [hnat]; exact hdeg) le_rfl hGdeg
      (eval₂Hom ρ (Fin.tail xs)) (hGψ i0) hGψ
    exact hαvan S ρ (Fin.tail xs) (fun k => hcoef k)


theorem eval₂_eq_eval₂_flat {n : ℕ} {S : Type*} [CommRing S] (ρ : Par →+* S) (ζ : Fin n → S)
    (Q : MvPolynomial (Fin n) Par) :
    eval₂ ρ ζ Q = eval₂ (Int.castRingHom S) (Sum.elim ζ fun k => ρ (X k)) (flat n Q) := by
  have hρ : eval₂Hom (Int.castRingHom S) (fun k : Fin 2 => ρ (X k)) = ρ :=
    MvPolynomial.ringHom_ext (fun z => by simp) (fun k => by simp)
  have h : eval₂Hom ρ ζ = (eval₂Hom (Int.castRingHom S) (Sum.elim ζ fun k => ρ (X k))).comp
      (flat n) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [coe_eval₂Hom, eval₂_C, RingHom.coe_comp, Function.comp_apply, flat_C,
        eval₂_rename]
      exact (RingHom.congr_fun hρ r).symm
    · simp
  exact RingHom.congr_fun h Q

/-- **Iterated elimination**, flat form: integer polynomials in two parameters and the
variables `W`, indexed by a finite type `E`. -/
theorem elim_flat {W E : Type*} [Fintype W] [Fintype E] {n : ℕ} (e : W ≃ Fin n) {D M : ℕ}
    (P : E → MvPolynomial (Fin 2 ⊕ W) ℤ) (hD : 1 ≤ D) (hM : 1 ≤ M)
    (hs : Fintype.card E ≤ D) (hsize : ∀ i, SizeLE (P i) D M)
    (hgen : ∀ w : W → GenericField, ∃ i, eval₂ (Int.castRingHom GenericField)
      (Sum.elim (fun k => algebraMap Par GenericField (X k)) w) (P i) ≠ 0) :
    ∃ α : Par, α ≠ 0 ∧ SizeLE α (elimDeg n D) (elimMass n D M) ∧
      ∀ (y : Fin 2 → ℝ) (w : W → ℝ),
        (∀ i, eval₂ (Int.castRingHom ℝ) (Sum.elim y w) (P i) = 0) →
          eval₂ (Int.castRingHom ℝ) y α = 0 := by
  classical
  let eE := Fintype.equivFin E
  let r : Fin 2 ⊕ W → Fin n ⊕ Fin 2 := Sum.elim Sum.inr (fun w => Sum.inl (e w))
  let P' : Fin (Fintype.card E) → MvPolynomial (Fin n) Par := fun i =>
    sumRingEquiv ℤ (Fin n) (Fin 2) (MvPolynomial.rename r (P (eE.symm i)))
  have hflat : ∀ i, flat n (P' i) = MvPolynomial.rename r (P (eE.symm i)) := fun i => by
    rw [flat_eq_sumRingEquiv_symm]
    exact (sumRingEquiv ℤ (Fin n) (Fin 2)).symm_apply_apply _
  have hev : ∀ {S : Type} [CommRing S] (ρ : Par →+* S) (x : Fin n → S) i,
      eval₂ ρ x (P' i) = eval₂ (Int.castRingHom S)
        (Sum.elim (fun k => ρ (X k)) (fun w => x (e w))) (P (eE.symm i)) := by
    intro S _ ρ x i
    rw [eval₂_eq_eval₂_flat, hflat, eval₂_rename]
    congr 1
    funext v
    rcases v with k | w <;> rfl
  obtain ⟨α, hα0, hαsize, hαvan⟩ := elim_nested n D M (Fintype.card E) P' hD hM hs
    (fun i => by rw [hflat]; exact (hsize _).rename r) (fun ζ => by
      obtain ⟨i, hi⟩ := hgen (fun w => ζ (e w))
      refine ⟨eE i, ?_⟩
      rw [hev]
      simpa using hi)
  refine ⟨α, hα0, hαsize, fun y w hw => ?_⟩
  have := hαvan ℝ (eval₂Hom (Int.castRingHom ℝ) y) (fun i => w (e.symm i)) (fun i => by
    rw [hev]
    have hyw : (Sum.elim (fun k => eval₂Hom (Int.castRingHom ℝ) y (X k))
        (fun v => w (e.symm (e v)))) = Sum.elim y w := by
      funext v; rcases v with k | v <;> simp
    rw [hyw]
    exact hw (eE.symm i))
  simpa using this

end NLQCLean.Elimination
