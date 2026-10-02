import NLQCLean.Arithmetic.GelfondNumerics

/-!
# A Liouville inequality over `ℤ[i][ϑ]`

Let `G ∈ ℤ[i][X]` be irreducible with a root `β₀`, `|β₀| ≤ 2`, let `f ∈ ℤ[X]` be monic of degree
`m ≥ 1` with a root `ϑ`, and let `Q_e ∈ ℤ[i][X]` (`e < m`) have degree at most `q` and
coefficients at most `A`. If `ρ = Σ_e ϑ^e Q_e(β₀)` satisfies `|ρ| Λ < 1` for an explicit `Λ`,
then `ρ = 0`.

Multiplication by `ρ` on `(1, ϑ, …, ϑ^{m-1})` is given by a matrix `Φ(β₀)` with
`Φ ∈ M_m(ℤ[i][X])`, so `ρ` is a root of the characteristic polynomial of `Φ(β₀)`. Its lowest
nonzero coefficient `C_k(β₀)` is at most `|ρ|` times a Lipschitz constant; `C_k ∈ ℤ[i][X]` has
degree at most `qm` and values `≤ V max(1,|β|)^{qm}` (eigenvalue bound and Mahler measure), and
the Liouville inequality over `ℤ[i]` gives `|C_k(β₀)| V^{g-1} M(G)^{qm} ≥ 1`.
-/

namespace NLQCLean.Gelfond

open Polynomial GaussianInt
open scoped Matrix

/-! ### Liouville over `ℤ[i]` with value bounds -/

/-- **Liouville over `ℤ[i]`**, with a bound on the values of `Q` instead of its coefficients. -/
theorem dvd_of_norm_eval_root_small_of_value {G Q : GaussianInt[X]} (hG : Irreducible G)
    (hdeg : 0 < G.natDegree) {β₀ : ℂ} (hβ : (G.map toComplex).eval β₀ = 0) {D : ℕ} {V : ℝ}
    (hV0 : 0 ≤ V) (hD : Q.natDegree ≤ D)
    (hV : ∀ β, ‖(Q.map toComplex).eval β‖ ≤ V * max 1 ‖β‖ ^ D)
    (hsmall : ‖(Q.map toComplex).eval β₀‖ *
      (V ^ (G.natDegree - 1) * (G.map toComplex).mahlerMeasure ^ D) < 1) :
    G ∣ Q := by
  classical
  by_cases hQ0 : Q = 0
  · rw [hQ0]; exact dvd_zero _
  set Gc := G.map toComplex with hGc
  set Qc := Q.map toComplex with hQc
  have hGdeg : Gc.natDegree = G.natDegree := natDegree_map_eq_of_injective toComplex_injective _
  have hQdeg : Qc.natDegree = Q.natDegree := natDegree_map_eq_of_injective toComplex_injective _
  have hG0 : G ≠ 0 := hG.ne_zero
  have hGc0 : Gc ≠ 0 := (Polynomial.map_ne_zero_iff toComplex_injective).mpr hG0
  have hsplit : Gc.Splits := IsAlgClosed.splits Gc
  set R := resultant G Q with hR
  have hRc : (R : ℂ) = Gc.leadingCoeff ^ Q.natDegree * (Gc.roots.map Qc.eval).prod := by
    have h1 := resultant_map_map G Q G.natDegree Q.natDegree toComplex
    have h2 := resultant_eq_prod_eval Gc Qc Q.natDegree hQdeg.le hsplit
    rw [hGdeg] at h2
    rw [hR]
    change toComplex (resultant G Q G.natDegree Q.natDegree) = _
    rw [← h1]
    exact h2
  have hroot : β₀ ∈ Gc.roots := (mem_roots hGc0).mpr hβ
  have hcard : Gc.roots.card = G.natDegree := by
    rw [← hGdeg]; exact hsplit.natDegree_eq_card_roots.symm
  have hlc1 : 1 ≤ ‖Gc.leadingCoeff‖ := by
    rw [hGc, leadingCoeff_map_of_injective toComplex_injective]
    exact one_le_norm_toComplex (leadingCoeff_ne_zero.mpr hG0)
  have hRsmall : ‖(R : ℂ)‖ < 1 := by
    have hprodle : ‖((Gc.roots.erase β₀).map Qc.eval).prod‖ ≤
        ((Gc.roots.erase β₀).map fun β => V * max 1 ‖β‖ ^ D).prod :=
      norm_prod_map_le _ _ _ hV
    have h2 : ((Gc.roots.erase β₀).map fun β => V * max 1 ‖β‖ ^ D).prod =
        V ^ (G.natDegree - 1) * ((Gc.roots.erase β₀).map fun β => max 1 ‖β‖ ^ D).prod := by
      rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
        Multiset.card_erase_of_mem hroot, hcard]
      rfl
    have hmax0 : 0 ≤ ((Gc.roots.erase β₀).map fun β => max 1 ‖β‖ ^ D).prod :=
      Multiset.prod_nonneg fun x hx => by
        obtain ⟨β, -, rfl⟩ := Multiset.mem_map.mp hx
        positivity
    have h3 : ((Gc.roots.erase β₀).map fun β => max 1 ‖β‖ ^ D).prod ≤
        (Gc.roots.map fun β => max 1 ‖β‖).prod ^ D := by
      rw [← Multiset.prod_map_pow, ← Multiset.prod_map_erase hroot]
      exact le_mul_of_one_le_left hmax0 (one_le_pow₀ (le_max_left _ _))
    have hM := mahlerMeasure_eq_leadingCoeff_mul_prod_roots Gc
    have hlcpow : ‖Gc.leadingCoeff‖ ^ Q.natDegree ≤ ‖Gc.leadingCoeff‖ ^ D :=
      pow_le_pow_right₀ hlc1 (hQdeg ▸ hD)
    have hVg : 0 ≤ V ^ (G.natDegree - 1) := by positivity
    calc ‖(R : ℂ)‖
        = ‖Gc.leadingCoeff‖ ^ Q.natDegree *
            (‖Qc.eval β₀‖ * ‖((Gc.roots.erase β₀).map Qc.eval).prod‖) := by
          rw [hRc, norm_mul, norm_pow, ← Multiset.prod_map_erase hroot, norm_mul]
      _ ≤ ‖Gc.leadingCoeff‖ ^ D * (‖Qc.eval β₀‖ * (V ^ (G.natDegree - 1) *
            (Gc.roots.map fun β => max 1 ‖β‖).prod ^ D)) := by
          refine mul_le_mul hlcpow (mul_le_mul_of_nonneg_left ?_ (_root_.norm_nonneg _))
            (by positivity) (by positivity)
          exact hprodle.trans (h2 ▸ mul_le_mul_of_nonneg_left h3 hVg)
      _ = ‖Qc.eval β₀‖ * (V ^ (G.natDegree - 1) *
            (‖Gc.leadingCoeff‖ * (Gc.roots.map fun β => max 1 ‖β‖).prod) ^ D) := by ring
      _ = ‖Qc.eval β₀‖ * (V ^ (G.natDegree - 1) * Gc.mahlerMeasure ^ D) := by rw [hM]
      _ < 1 := hsmall
  have hR0 : R = 0 := by
    by_contra hne
    exact absurd (one_le_norm_toComplex hne) (not_le.mpr hRsmall)
  have hinj : Function.Injective (algebraMap GaussianInt (FractionRing GaussianInt)) :=
    IsFractionRing.injective _ _
  have hresK : resultant (G.map (algebraMap GaussianInt (FractionRing GaussianInt)))
      (Q.map (algebraMap GaussianInt (FractionRing GaussianInt))) = 0 := by
    have := resultant_map_map G Q G.natDegree Q.natDegree
      (algebraMap GaussianInt (FractionRing GaussianInt))
    rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj] at *
    rw [this, ← hR, hR0, map_zero]
  have hprim := hG.isPrimitive hdeg.ne'
  have hGK : Irreducible (G.map (algebraMap GaussianInt (FractionRing GaussianInt))) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map).mp hG
  have hncop := ((resultant_eq_zero_iff).mp hresK).2
  have hdvdK : G.map (algebraMap GaussianInt (FractionRing GaussianInt)) ∣
      Q.map (algebraMap GaussianInt (FractionRing GaussianInt)) := by
    by_contra hnd
    exact hncop ((hGK.coprime_iff_not_dvd).mpr hnd)
  exact hprim.dvd_of_fraction_map_dvd_fraction_map hdvdK

/-! ### Degrees of characteristic-polynomial coefficients -/

section CharpolyDegree

variable {R : Type*} [CommRing R]

/-- Every coefficient of `p ∈ R[X][Y]` has degree at most `d` in `X`. -/
def CoeffDegLE (d : ℕ) (p : R[X][X]) : Prop := ∀ k, (p.coeff k).natDegree ≤ d

theorem coeffDegLE_mul {a b : ℕ} {p r : R[X][X]} (hp : CoeffDegLE a p) (hr : CoeffDegLE b r) :
    CoeffDegLE (a + b) (p * r) := fun k => by
  rw [coeff_mul]
  exact natDegree_sum_le_of_forall_le _ _ fun x _ =>
    natDegree_mul_le.trans (add_le_add (hp _) (hr _))

theorem coeffDegLE_one : CoeffDegLE 0 (1 : R[X][X]) := fun k => by
  simp only [Polynomial.coeff_one]
  split_ifs <;> simp

theorem coeffDegLE_prod {ι : Type*} (s : Finset ι) (f : ι → R[X][X]) {d : ℕ}
    (h : ∀ i ∈ s, CoeffDegLE d (f i)) : CoeffDegLE (d * s.card) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using (coeffDegLE_one (R := R))
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.card_cons, mul_add, mul_one, add_comm]
    exact coeffDegLE_mul (h a (Finset.mem_cons_self a s))
      (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

theorem coeffDegLE_charmatrix {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n R[X])
    {q : ℕ} (hM : ∀ i j, (M i j).natDegree ≤ q) (i j : n) : CoeffDegLE q (M.charmatrix i j) := by
  intro k
  rw [Matrix.charmatrix_apply, coeff_sub, coeff_C]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, coeff_X]
      split_ifs <;> simp
    · rw [Matrix.diagonal_apply_ne _ hij, coeff_zero, natDegree_zero]; exact Nat.zero_le _
  · split_ifs
    · exact hM i j
    · rw [natDegree_zero]; exact Nat.zero_le _

/-- The coefficients of the characteristic polynomial of a matrix over `R[X]` with entries of
degree at most `q` have degree at most `q n`. -/
theorem natDegree_charpoly_coeff_le {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n R[X])
    {q : ℕ} (hM : ∀ i j, (M i j).natDegree ≤ q) (k : ℕ) :
    (M.charpoly.coeff k).natDegree ≤ q * Fintype.card n := by
  rw [Matrix.charpoly, Matrix.det_apply, finsetSum_coeff]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [Units.smul_def, coeff_smul]
  refine (natDegree_smul_le _ _).trans ?_
  have := coeffDegLE_prod Finset.univ (fun i => M.charmatrix (σ i) i)
    (fun i _ => coeffDegLE_charmatrix M hM (σ i) i) k
  rwa [Finset.card_univ] at this

end CharpolyDegree

/-! ### Coefficients of complex characteristic polynomials -/

theorem norm_le_of_charpoly_eval_eq_zero {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ) {E : ℝ}
    (hE : ∀ i j, ‖N i j‖ ≤ E) {μ : ℂ} (hμ : N.charpoly.eval μ = 0) : ‖μ‖ ≤ m * E := by
  classical
  rw [Matrix.eval_charpoly] at hμ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at h
    exact hv0 (funext fun i => (h.false i).elim)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖v i‖) hne
  have hvi : 0 < ‖v i‖ := by
    by_contra h
    apply hv0
    funext j
    have := hi j (Finset.mem_univ _)
    exact norm_le_zero_iff.mp (this.trans (not_lt.mp h))
  have heq : μ * v i = (N *ᵥ v) i := by
    have := congrFun hv i
    rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal,
      Pi.zero_apply, sub_eq_zero] at this
    exact this
  have hE0 : 0 ≤ E := (_root_.norm_nonneg _).trans (hE i i)
  have hbound : ‖(N *ᵥ v) i‖ ≤ m * E * ‖v i‖ := by
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖N i j * v j‖ ≤ ∑ _j : Fin m, E * ‖v i‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]; exact mul_le_mul (hE i j) (hi j (Finset.mem_univ _)) (_root_.norm_nonneg _) hE0
      _ = m * E * ‖v i‖ := by simp; ring
  rw [← heq, norm_mul] at hbound
  exact le_of_mul_le_mul_right hbound hvi

theorem prod_max_one_le_pow (s : Multiset ℂ) {b : ℝ} (h : ∀ μ ∈ s, max 1 ‖μ‖ ≤ b) :
    (s.map fun μ => max 1 ‖μ‖).prod ≤ b ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]
    have hb : 0 ≤ b := (zero_le_one.trans (le_max_left _ _)).trans
      (h a (Multiset.mem_cons_self a s))
    exact mul_le_mul (ih fun μ hμ => h μ (Multiset.mem_cons_of_mem hμ))
      (h a (Multiset.mem_cons_self a s)) (by positivity) (pow_nonneg hb _)

/-- **Charpoly coefficient bound.** -/
theorem norm_charpoly_coeff_le {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ) {E : ℝ}
    (hE : ∀ i j, ‖N i j‖ ≤ E) (k : ℕ) :
    ‖N.charpoly.coeff k‖ ≤ 2 ^ m * max 1 (m * E) ^ m := by
  set χ := N.charpoly
  have hmon : χ.Monic := Matrix.charpoly_monic N
  have hdeg : χ.natDegree = m := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hsplit : χ.Splits := IsAlgClosed.splits χ
  have hcard : χ.roots.card = m := by rw [← hdeg]; exact hsplit.natDegree_eq_card_roots.symm
  have hM : χ.mahlerMeasure ≤ max 1 (m * E) ^ m := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hmon.leadingCoeff, norm_one, one_mul]
    have := prod_max_one_le_pow χ.roots (b := max 1 (m * E)) fun μ hμ =>
      max_le_max le_rfl (norm_le_of_charpoly_eval_eq_zero N hE
        ((mem_roots hmon.ne_zero).mp hμ))
    rwa [hcard] at this
  refine (norm_coeff_le_choose_mul_mahlerMeasure k χ).trans ?_
  rw [hdeg]
  have hch : ((m.choose k : ℕ) : ℝ) ≤ 2 ^ m := by exact_mod_cast Nat.choose_le_two_pow m k
  exact mul_le_mul hch hM (mahlerMeasure_nonneg _) (by positivity)

/-! ### Reduction modulo a monic polynomial -/

/-- `π(n, k)`: the coefficient of `ϑ^k` in `ϑ^n` modulo `f`. -/
noncomputable def redCoeff (f : ℤ[X]) (n k : ℕ) : ℤ := ((X ^ n : ℤ[X]) %ₘ f).coeff k

theorem sum_redCoeff {f : ℤ[X]} (hf : f.Monic) {m : ℕ} (hmf : f.natDegree = m) {ϑ : ℂ}
    (hϑ : f.eval₂ (Int.castRingHom ℂ) ϑ = 0) (n : ℕ) :
    ∑ k : Fin m, (redCoeff f n k : ℂ) * ϑ ^ (k : ℕ) = ϑ ^ n := by
  subst hmf
  have hf1 : f ≠ 1 := by
    rintro rfl; simp at hϑ
  have hdiv := modByMonic_add_div (X ^ n : ℤ[X]) f
  have heval := congrArg (eval₂ (Int.castRingHom ℂ) ϑ) hdiv
  rw [eval₂_add, eval₂_mul, hϑ, zero_mul, add_zero, eval₂_X_pow] at heval
  rw [← heval, eval₂_eq_sum_range' _ (natDegree_modByMonic_lt _ hf hf1),
    ← Fin.sum_univ_eq_sum_range]
  rfl

theorem abs_redCoeff_le {f : ℤ[X]} (hf : f.Monic) (hm : 1 ≤ f.natDegree) {F : ℝ} (hF0 : 0 ≤ F)
    (hF : ∀ i, |(f.coeff i : ℝ)| ≤ F) (n k : ℕ) : |(redCoeff f n k : ℝ)| ≤ (1 + F) ^ n := by
  set fc := f.map (Int.castRingHom ℂ)
  have hfc : fc.Monic := hf.map _
  have hfcdeg : fc.natDegree = f.natDegree := hf.natDegree_map _
  have hmap : ((redCoeff f n k : ℤ) : ℂ) = (((X ^ n : ℂ[X]) %ₘ fc).coeff k) := by
    rw [redCoeff, show ((((X ^ n : ℤ[X]) %ₘ f).coeff k : ℤ) : ℂ) =
      (Int.castRingHom ℂ) (((X ^ n : ℤ[X]) %ₘ f).coeff k) from rfl, ← coeff_map,
      map_modByMonic _ hf, Polynomial.map_pow, map_X]
  have h := norm_coeff_X_pow_modByMonic_le hfc (hfcdeg ▸ hm) hF0 (fun i _ => by
    rw [coeff_map, eq_intCast, Complex.norm_intCast]; exact hF i) n k
  rw [← hmap, Complex.norm_intCast] at h
  exact h

/-! ### The Liouville inequality -/

/-- The value multiplier `m (1+F)^{2m} (q+1) A` of the entries of `Φ`. -/
noncomputable def angleE (m : ℕ) (F : ℝ) (q : ℕ) (A : ℝ) : ℝ :=
  m * ((1 + F) ^ (2 * m) * ((q + 1) * A))

/-- The Liouville constant `Λ`. -/
noncomputable def angleLiouville (G : GaussianInt[X]) (m : ℕ) (F : ℝ) (q : ℕ) (A : ℝ) : ℝ :=
  ((m + 1) * (m * ((2 ^ m * (m * (angleE m F q A * 2 ^ q)) ^ m) * 2 ^ m))) *
    ((2 ^ m * (m * angleE m F q A) ^ m) ^ (G.natDegree - 1) *
      (G.map toComplex).mahlerMeasure ^ (q * m))

theorem one_le_angleE {m : ℕ} (hm : 1 ≤ m) {F : ℝ} (hF0 : 0 ≤ F) {q : ℕ} {A : ℝ}
    (hA1 : 1 ≤ A) : 1 ≤ angleE m F q A := by
  unfold angleE
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (1 : ℝ) ≤ (1 + F) ^ (2 * m) := one_le_pow₀ (by linarith)
  have h3 : (1 : ℝ) ≤ (q + 1) * A := by
    have : (1 : ℝ) ≤ q + 1 := by linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
    nlinarith
  exact one_le_mul_of_one_le_of_one_le h1 (one_le_mul_of_one_le_of_one_le h2 h3)

theorem one_le_mahlerMeasure_of_ne_zero {G : GaussianInt[X]} (hG0 : G ≠ 0) :
    1 ≤ (G.map toComplex).mahlerMeasure := by
  refine one_le_mahlerMeasure_of_one_le_norm_leadingCoeff ?_
  rw [leadingCoeff_map_of_injective toComplex_injective]
  exact one_le_norm_toComplex (leadingCoeff_ne_zero.mpr hG0)

theorem one_le_angleLiouville {G : GaussianInt[X]} (hG0 : G ≠ 0) {m : ℕ} (hm : 1 ≤ m) {F : ℝ}
    (hF0 : 0 ≤ F) {q : ℕ} {A : ℝ} (hA1 : 1 ≤ A) : 1 ≤ angleLiouville G m F q A := by
  unfold angleLiouville
  have hE := one_le_angleE hm hF0 (q := q) hA1
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have h2q : (1 : ℝ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
  have hW : (1 : ℝ) ≤ (2 ^ m * (m * (angleE m F q A * 2 ^ q)) ^ m) :=
    one_le_mul_of_one_le_of_one_le h2 (one_le_pow₀ (one_le_mul_of_one_le_of_one_le h1
      (one_le_mul_of_one_le_of_one_le hE h2q)))
  have hL : (1 : ℝ) ≤ (m + 1) * (m * ((2 ^ m * (m * (angleE m F q A * 2 ^ q)) ^ m) * 2 ^ m)) :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_mul_of_one_le_of_one_le h1
      (one_le_mul_of_one_le_of_one_le hW h2))
  have hV : (1 : ℝ) ≤ (2 ^ m * (m * angleE m F q A) ^ m) ^ (G.natDegree - 1) :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le h2 (one_le_pow₀
      (one_le_mul_of_one_le_of_one_le h1 hE)))
  have hM : (1 : ℝ) ≤ (G.map toComplex).mahlerMeasure ^ (q * m) :=
    one_le_pow₀ (one_le_mahlerMeasure_of_ne_zero hG0)
  exact one_le_mul_of_one_le_of_one_le hL (one_le_mul_of_one_le_of_one_le hV hM)

/-- **Liouville over `ℤ[i][ϑ]`.** -/
theorem eq_zero_of_norm_small_angle {G : GaussianInt[X]} (hG : Irreducible G)
    (hdeg : 0 < G.natDegree) {β₀ : ℂ} (hβ : (G.map toComplex).eval β₀ = 0) (hβ2 : ‖β₀‖ ≤ 2)
    {f : ℤ[X]} (hf : f.Monic) {m : ℕ} (hmf : f.natDegree = m) (hm : 1 ≤ m) {ϑ : ℂ}
    (hϑ : f.eval₂ (Int.castRingHom ℂ) ϑ = 0) {F : ℝ} (hF0 : 0 ≤ F)
    (hF : ∀ i, |(f.coeff i : ℝ)| ≤ F) (Q : Fin m → GaussianInt[X]) {q : ℕ} {A : ℝ}
    (hA1 : 1 ≤ A) (hq : ∀ e, (Q e).natDegree ≤ q)
    (hA : ∀ e k, ‖(((Q e).coeff k : GaussianInt) : ℂ)‖ ≤ A)
    (hsmall : ‖∑ e : Fin m, ϑ ^ (e : ℕ) * ((Q e).map toComplex).eval β₀‖ *
      angleLiouville G m F q A < 1) :
    ∑ e : Fin m, ϑ ^ (e : ℕ) * ((Q e).map toComplex).eval β₀ = 0 := by
  classical
  set ρ := ∑ e : Fin m, ϑ ^ (e : ℕ) * ((Q e).map toComplex).eval β₀ with hρdef
  have hG0 : G ≠ 0 := hG.ne_zero
  have hΛ1 := one_le_angleLiouville hG0 hm hF0 (q := q) hA1
  have hρ1 : ‖ρ‖ < 1 := by
    by_contra h
    have := mul_le_mul (not_lt.mp h) hΛ1 zero_le_one (_root_.norm_nonneg _)
    linarith
  set E1 := angleE m F q A with hE1def
  have hE1 : 1 ≤ E1 := one_le_angleE hm hF0 hA1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- the matrix `Φ`
  let Φ : Matrix (Fin m) (Fin m) GaussianInt[X] := Matrix.of fun i k =>
    ∑ e : Fin m, C ((redCoeff f ((i : ℕ) + e) k : ℤ) : GaussianInt) * Q e
  have hΦapp : ∀ i k, Φ i k =
      ∑ e : Fin m, C ((redCoeff f ((i : ℕ) + e) k : ℤ) : GaussianInt) * Q e := fun _ _ => rfl
  have hΦdeg : ∀ i k, (Φ i k).natDegree ≤ q := fun i k => by
    rw [hΦapp]
    exact natDegree_sum_le_of_forall_le _ _ fun e _ => (natDegree_C_mul_le _ _).trans (hq e)
  let ψ : ℂ → GaussianInt[X] →+* ℂ := fun β => eval₂RingHom toComplex β
  have hψ : ∀ β p, ψ β p = (p.map toComplex).eval β := fun β p => by
    simp [ψ, eval_map]
  have hψΦ : ∀ β i k, ψ β (Φ i k) = ∑ e : Fin m,
      ((redCoeff f ((i : ℕ) + e) k : ℤ) : ℂ) * ((Q e).map toComplex).eval β := fun β i k => by
    rw [hΦapp, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_mul, hψ, hψ, Polynomial.map_C, eval_C, map_intCast]
  have hπ : ∀ (i e : Fin m) (k : ℕ), ‖((redCoeff f ((i : ℕ) + e) k : ℤ) : ℂ)‖ ≤ (1 + F) ^ (2 * m) :=
    fun i e k => by
      rw [Complex.norm_intCast]
      refine (abs_redCoeff_le hf (hmf ▸ hm) hF0 hF _ k).trans (pow_le_pow_right₀ (by linarith) ?_)
      have := i.isLt; have := e.isLt; omega
  have hQval : ∀ e β, ‖((Q e).map toComplex).eval β‖ ≤ (q + 1) * A * max 1 ‖β‖ ^ q :=
    fun e β => norm_eval_le_of_coeff_le ((natDegree_map_le).trans (hq e))
      (fun k => by rw [coeff_map]; exact hA e k) β
  have hΦval : ∀ β i k, ‖ψ β (Φ i k)‖ ≤ E1 * max 1 ‖β‖ ^ q := by
    intro β i k
    rw [hψΦ]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ e : Fin m, ‖((redCoeff f ((i : ℕ) + e) k : ℤ) : ℂ) * ((Q e).map toComplex).eval β‖
        ≤ ∑ _e : Fin m, (1 + F) ^ (2 * m) * ((q + 1) * A * max 1 ‖β‖ ^ q) :=
          Finset.sum_le_sum fun e _ => by
            rw [norm_mul]
            have hA0 : 0 ≤ A := by linarith
            exact mul_le_mul (hπ i e k) (hQval e β) (_root_.norm_nonneg _) (by positivity)
      _ = E1 * max 1 ‖β‖ ^ q := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hE1def, angleE]
          ring
  -- coefficients of the characteristic polynomial
  set χ := Φ.charpoly with hχ
  have hχmap : ∀ β, (Φ.map (ψ β)).charpoly = χ.map (ψ β) := fun β => Matrix.charpoly_map _ _
  have hCval : ∀ k β, ‖ψ β (χ.coeff k)‖ ≤
      (2 ^ m * (m * E1) ^ m) * max 1 ‖β‖ ^ (q * m) := by
    intro k β
    have h := norm_charpoly_coeff_le (Φ.map (ψ β)) (E := E1 * max 1 ‖β‖ ^ q)
      (fun i j => hΦval β i j) k
    rw [hχmap, coeff_map] at h
    refine h.trans (le_of_eq ?_)
    have hge : 1 ≤ (m : ℝ) * (E1 * max 1 ‖β‖ ^ q) :=
      one_le_mul_of_one_le_of_one_le hm1 (one_le_mul_of_one_le_of_one_le hE1
        (one_le_pow₀ (le_max_left _ _)))
    rw [max_eq_right hge, pow_mul]
    ring
  have hCdeg : ∀ k, (χ.coeff k).natDegree ≤ q * m := fun k => by
    have := natDegree_charpoly_coeff_le Φ hΦdeg k
    rwa [Fintype.card_fin] at this
  -- the eigenvector at `β₀`
  set N := Φ.map (ψ β₀) with hN
  let v : Fin m → ℂ := fun i => ϑ ^ (i : ℕ)
  have hNv : N *ᵥ v = ρ • v := by
    funext i
    simp only [hN, Matrix.mulVec, dotProduct, Matrix.map_apply, hψΦ, Pi.smul_apply, smul_eq_mul,
      v, hρdef]
    rw [Finset.sum_mul]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hs := sum_redCoeff hf hmf hϑ ((i : ℕ) + e)
    calc ∑ k : Fin m, ((redCoeff f ((i : ℕ) + e) k : ℤ) : ℂ) *
          ((Q e).map toComplex).eval β₀ * ϑ ^ (k : ℕ)
        = (∑ k : Fin m, ((redCoeff f ((i : ℕ) + e) k : ℤ) : ℂ) * ϑ ^ (k : ℕ)) *
            ((Q e).map toComplex).eval β₀ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = ϑ ^ (e : ℕ) * ((Q e).map toComplex).eval β₀ * ϑ ^ (i : ℕ) := by
          rw [hs, pow_add]; ring
  have hv0 : v ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp [v] at this
  have hχN : N.charpoly.eval ρ = 0 := by
    rw [Matrix.eval_charpoly]
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, hNv, Matrix.scalar_apply]
    funext i
    simp
  by_contra hρ0
  -- the lowest nonzero coefficient
  set χN := N.charpoly with hχNdef
  have hmon : χN.Monic := Matrix.charpoly_monic N
  have hex : ∃ k, χN.coeff k ≠ 0 := ⟨χN.natDegree, by
    rw [← leadingCoeff, hmon.leadingCoeff]; exact one_ne_zero⟩
  set k₀ := Nat.find hex with hk₀
  have hk₀ne : χN.coeff k₀ ≠ 0 := Nat.find_spec hex
  have hlow : ∀ d < k₀, χN.coeff d = 0 := fun d hd => by
    have := Nat.find_min hex hd
    exact not_not.mp this
  obtain ⟨Rp, hRp⟩ := X_pow_dvd_iff.mpr hlow
  have hRcoeff : ∀ j, Rp.coeff j = χN.coeff (j + k₀) := fun j => by
    rw [hRp, coeff_X_pow_mul]
  have hχNdeg : χN.natDegree = m := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hRdeg : Rp.natDegree ≤ m := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
    rw [hRcoeff]
    refine coeff_eq_zero_of_natDegree_lt ?_
    rw [hχNdeg]
    have : m < j := by exact_mod_cast hj
    omega
  set W := 2 ^ m * (m * (E1 * 2 ^ q)) ^ m with hW
  have hNentry : ∀ i j, ‖N i j‖ ≤ E1 * 2 ^ q := fun i j => by
    refine (hΦval β₀ i j).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    exact pow_le_pow_left₀ (by positivity) (max_le (by norm_num) hβ2) q
  have hRbound : ∀ j, ‖Rp.coeff j‖ ≤ W := fun j => by
    rw [hRcoeff]
    refine (norm_charpoly_coeff_le N hNentry _).trans (le_of_eq ?_)
    have hge : 1 ≤ (m : ℝ) * (E1 * 2 ^ q) :=
      one_le_mul_of_one_le_of_one_le hm1 (one_le_mul_of_one_le_of_one_le hE1
        (one_le_pow₀ (by norm_num)))
    rw [max_eq_right hge]
  have hReval : Rp.eval ρ = 0 := by
    have h := hχN
    rw [hRp, eval_mul, eval_pow, eval_X] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hρ0)
  have hR0 : Rp.eval 0 = χN.coeff k₀ := by
    rw [← coeff_zero_eq_eval_zero, hRcoeff, zero_add]
  have hlip := norm_eval_sub_eval_le hRdeg hRbound (x := 0) (y := ρ) (by simp) (by linarith)
  rw [hR0, hReval, sub_zero, zero_sub, norm_neg] at hlip
  -- the coefficient polynomial `C_{k₀}`
  have hCk : ψ β₀ (χ.coeff k₀) = χN.coeff k₀ := by
    rw [hχNdef, hN, hχmap, coeff_map]
  have hndvd : ¬ G ∣ χ.coeff k₀ := by
    rintro ⟨U, hU⟩
    apply hk₀ne
    rw [← hCk, hψ, hU, Polynomial.map_mul, eval_mul, hβ, zero_mul]
  have hge := not_lt.mp fun h => hndvd (dvd_of_norm_eval_root_small_of_value hG hdeg hβ
    (V := 2 ^ m * (m * E1) ^ m) (by positivity) (hCdeg k₀) (fun β => by rw [← hψ]; exact hCval k₀ β) h)
  rw [← hψ, hCk] at hge
  have hVM : 0 ≤ (2 ^ m * (m * E1) ^ m) ^ (G.natDegree - 1) *
      (G.map toComplex).mahlerMeasure ^ (q * m) := by
    have := (G.map toComplex).mahlerMeasure_nonneg
    positivity
  have hfinal : 1 ≤ ‖ρ‖ * angleLiouville G m F q A := by
    calc (1 : ℝ) ≤ ‖χN.coeff k₀‖ * ((2 ^ m * (m * E1) ^ m) ^ (G.natDegree - 1) *
          (G.map toComplex).mahlerMeasure ^ (q * m)) := hge
      _ ≤ ‖ρ‖ * (((m : ℕ) + 1) * ((m : ℕ) * (W * 2 ^ m))) *
          ((2 ^ m * (m * E1) ^ m) ^ (G.natDegree - 1) *
            (G.map toComplex).mahlerMeasure ^ (q * m)) :=
          mul_le_mul_of_nonneg_right hlip hVM
      _ = ‖ρ‖ * angleLiouville G m F q A := by
          rw [angleLiouville, ← hE1def, hW]; ring
  linarith

end NLQCLean.Gelfond
