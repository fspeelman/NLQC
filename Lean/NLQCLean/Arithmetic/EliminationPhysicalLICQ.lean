import NLQCLean.Arithmetic.PhysicalPolynomialEncoding
import NLQCLean.Arithmetic.EliminationKKT

/-!
# Independent physical constraints

A non-redundant subfamily of the physical constraint equations: the unit-resource equation,
and for every isometry block the real parts of `(VᴴV - 1)ᵢⱼ` with `i ≤ j` and the imaginary
parts with `i < j`, in a fixed enumeration. It cuts out the same physical set, and at every
physical point its differential is onto (`δ = V H / 2` realizes a Hermitian `H`).
-/

namespace NLQCLean.PhysicalPolynomial

attribute [local implicit_reducible] Matrix

open Matrix MvPolynomial ComplexConjugate

section Block

variable {σ : Type*}

theorem coordinateVector_add_smul {ε : Type*} (entry : ε × Fin 2 → σ) (x δ : σ → ℝ) (t : ℝ) :
    coordinateVector entry (x + t • δ) =
      coordinateVector entry x + (t : ℂ) • coordinateVector entry δ := by
  funext e
  apply Complex.ext <;> simp [coordinateVector]

theorem coordinateMatrix_add_smul {m n : Type*} (entry : (m × n) × Fin 2 → σ) (x δ : σ → ℝ)
    (t : ℝ) : coordinateMatrix entry (x + t • δ) =
      coordinateMatrix entry x + (t : ℂ) • coordinateMatrix entry δ := by
  ext i j
  apply Complex.ext <;> simp [coordinateMatrix, coordinateVector]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Linear part of `Vᴴ V` along `Δ`. -/
def gramLinear (V Δ : Matrix m n ℂ) : Matrix n n ℂ := Vᴴ * Δ + Δᴴ * V

omit [Fintype n] [DecidableEq n] in
theorem gram_line (V Δ : Matrix m n ℂ) (t : ℝ) :
    (V + (t : ℂ) • Δ)ᴴ * (V + (t : ℂ) • Δ) =
      Vᴴ * V + (t : ℂ) • gramLinear V Δ + ((t : ℂ) ^ 2) • (Δᴴ * Δ) := by
  rw [conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    gramLinear, smul_add, pow_two]
  abel

/-- The coordinate of a constraint index in a Gram-type matrix. -/
def partValue (G : Matrix n n ℂ) (p : (n × n) × Fin 2) : ℝ :=
  if p.2 = 0 then (G p.1.1 p.1.2).re else (G p.1.1 p.1.2).im

omit [Fintype n] in
theorem eval_isometryPartConstraint (entry : (m × n) × Fin 2 → σ) (x : σ → ℝ)
    (p : (n × n) × Fin 2) :
    eval x (isometryPartConstraint entry p) =
      partValue ((coordinateMatrix entry x)ᴴ * coordinateMatrix entry x - 1) p := by
  unfold isometryPartConstraint partValue
  split_ifs
  · rw [isometryRealConstraint_eval]; simp
  · rw [isometryImagConstraint_eval]
    by_cases h : p.1.1 = p.1.2 <;> simp [h]

omit [Fintype n] [DecidableEq n] in
theorem partValue_add (G G' : Matrix n n ℂ) (p : (n × n) × Fin 2) :
    partValue (G + G') p = partValue G p + partValue G' p := by
  unfold partValue; split_ifs <;> simp

omit [Fintype n] [DecidableEq n] in
theorem partValue_real_smul (c : ℝ) (G : Matrix n n ℂ) (p : (n × n) × Fin 2) :
    partValue ((c : ℂ) • G) p = c * partValue G p := by
  unfold partValue; split_ifs <;> simp

omit [Fintype n] in
theorem gram_sub_one_line (V Δ : Matrix m n ℂ) (t : ℝ) :
    Vᴴ * V + (t : ℂ) • gramLinear V Δ + ((t : ℂ) ^ 2) • (Δᴴ * Δ) - 1 =
      (Vᴴ * V - 1) + (t : ℂ) • gramLinear V Δ + ((t ^ 2 : ℝ) : ℂ) • (Δᴴ * Δ) := by
  push_cast; abel

omit [Fintype n] in
theorem eval_isometryPartConstraint_line (entry : (m × n) × Fin 2 → σ) (x δ : σ → ℝ)
    (p : (n × n) × Fin 2) (t : ℝ) :
    eval (x + t • δ) (isometryPartConstraint entry p) =
      eval x (isometryPartConstraint entry p) +
        t * partValue (gramLinear (coordinateMatrix entry x) (coordinateMatrix entry δ)) p +
        t ^ 2 * partValue ((coordinateMatrix entry δ)ᴴ * coordinateMatrix entry δ) p := by
  rw [eval_isometryPartConstraint, eval_isometryPartConstraint, coordinateMatrix_add_smul,
    gram_line]
  rw [gram_sub_one_line, partValue_add, partValue_add, partValue_real_smul, partValue_real_smul]

/-- An enumeration of the input index. -/
noncomputable def rank (n : Type*) [Fintype n] (i : n) : ℕ := (Fintype.equivFin n i : ℕ)

omit [DecidableEq n] in
theorem rank_injective : Function.Injective (rank n) := fun _ _ h =>
  (Fintype.equivFin n).injective (Fin.ext h)

/-- Non-redundant constraint indices. -/
def NonRed (p : (n × n) × Fin 2) : Prop :=
  (p.2 = 0 ∧ rank n p.1.1 ≤ rank n p.1.2) ∨ (p.2 ≠ 0 ∧ rank n p.1.1 < rank n p.1.2)

noncomputable instance : DecidablePred (NonRed (n := n)) := fun _ => Classical.dec _

abbrev NR (n : Type*) [Fintype n] [DecidableEq n] := {p : (n × n) × Fin 2 // NonRed p}

/-- A Hermitian matrix with prescribed non-redundant parts. -/
noncomputable def hermOf (b : NR n → ℝ) : Matrix n n ℂ := fun i j =>
  if hij : rank n i ≤ rank n j then
    ⟨b ⟨((i, j), 0), Or.inl ⟨rfl, hij⟩⟩,
      if h : rank n i < rank n j then b ⟨((i, j), 1), Or.inr ⟨one_ne_zero, h⟩⟩ else 0⟩
  else
    ⟨b ⟨((j, i), 0), Or.inl ⟨rfl, (not_le.mp hij).le⟩⟩,
      -b ⟨((j, i), 1), Or.inr ⟨one_ne_zero, not_le.mp hij⟩⟩⟩

theorem hermOf_isHermitian (b : NR n → ℝ) : (hermOf b)ᴴ = hermOf b := by
  ext i j
  rw [conjTranspose_apply]
  apply Complex.ext
  · rcases lt_trichotomy (rank n i) (rank n j) with h | h | h
    · simp [hermOf, h.le, not_le.mpr h]
    · have := rank_injective h; subst this; simp [hermOf]
    · simp [hermOf, h.le, not_le.mpr h]
  · rcases lt_trichotomy (rank n i) (rank n j) with h | h | h
    · simp [hermOf, h.le, not_le.mpr h, h]
    · have := rank_injective h; subst this; simp [hermOf]
    · simp [hermOf, h.le, not_le.mpr h, h]

theorem partValue_hermOf (b : NR n → ℝ) (p : NR n) : partValue (hermOf b) p.1 = b p := by
  obtain ⟨⟨⟨i, j⟩, c⟩, hp⟩ := p
  fin_cases c
  · have hij : rank n i ≤ rank n j := by
      rcases hp with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd rfl h
    simp [partValue, hermOf, hij]
  · have hij : rank n i < rank n j := by
      rcases hp with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h (by simp)
      · exact h
    simp [partValue, hermOf, hij.le, hij]

theorem gramLinear_half_mul (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (H : Matrix n n ℂ)
    (hH : Hᴴ = H) : gramLinear V ((1 / 2 : ℂ) • (V * H)) = H := by
  rw [gramLinear, conjTranspose_smul, conjTranspose_mul, hH, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.mul_assoc, hV, Matrix.mul_assoc, hV]
  simp only [Matrix.one_mul, Matrix.mul_one, star_div₀, star_one, star_ofNat]
  rw [← add_smul]
  norm_num

theorem exists_block_direction (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (b : NR n → ℝ) :
    ∃ Δ : Matrix m n ℂ, ∀ p : NR n, partValue (gramLinear V Δ) p.1 = b p :=
  ⟨_, fun p => by rw [gramLinear_half_mul V hV _ (hermOf_isHermitian b)]; exact partValue_hermOf b p⟩

/-- The non-redundant equations cut out the isometries. -/
theorem isIsometry_of_nonRed (entry : (m × n) × Fin 2 → σ) (x : σ → ℝ)
    (h : ∀ p : NR n, eval x (isometryPartConstraint entry p.1) = 0) :
    IsIsometry (coordinateMatrix entry x) := by
  set V := coordinateMatrix entry x
  set G := Vᴴ * V - 1 with hG
  have hGH : Gᴴ = G := by rw [hG, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_one]
  have hval : ∀ p : NR n, partValue G p.1 = 0 := fun p => by
    rw [← eval_isometryPartConstraint]; exact h p
  have hentry : ∀ i j, rank n i ≤ rank n j → G i j = 0 := by
    intro i j hij
    apply Complex.ext
    · simpa [partValue] using hval ⟨((i, j), 0), Or.inl ⟨rfl, hij⟩⟩
    · rcases hij.lt_or_eq with hlt | heq
      · simpa [partValue] using hval ⟨((i, j), 1), Or.inr ⟨one_ne_zero, hlt⟩⟩
      · have := rank_injective heq; subst this
        have hd := congrArg (fun M : Matrix n n ℂ => M i i) hGH
        simp only [conjTranspose_apply] at hd
        have := congrArg Complex.im hd
        simp at this
        rw [Complex.zero_im]
        linarith
  have hall : G = 0 := by
    ext i j
    rcases le_total (rank n i) (rank n j) with hij | hji
    · exact hentry i j hij
    · have hd := congrArg (fun M : Matrix n n ℂ => M i j) hGH
      simp only [conjTranspose_apply, hentry j i hji, star_zero] at hd
      simpa using hd.symm
  exact sub_eq_zero.mp hall

theorem eval_unitResourceConstraint_line {ε : Type*} [Fintype ε] (entry : ε × Fin 2 → σ)
    (x δ : σ → ℝ) (t : ℝ) :
    eval (x + t • δ) (unitResourceConstraint entry) =
      eval x (unitResourceConstraint entry) +
        t * (2 * ∑ e, ((coordinateVector entry x e).re * (coordinateVector entry δ e).re +
          (coordinateVector entry x e).im * (coordinateVector entry δ e).im)) +
        t ^ 2 * ∑ e, Complex.normSq (coordinateVector entry δ e) := by
  simp only [eval, unitResourceConstraint, coe_eval₂Hom, eval₂_sub, eval₂_sum, eval₂_add,
    eval₂_pow, eval₂_X, eval₂_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordinateVector,
    Complex.normSq_apply, Finset.mul_sum]
  rw [sub_add_eq_add_sub, sub_add_eq_add_sub, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun e _ => by ring

end Block

section Physical

variable (t : Fin 8 → ℕ)

/-- Indices of the non-redundant physical equations. -/
abbrev IndepIndex :=
  Unit ⊕ (NR (EncoderAInputIndex 2 t) ⊕ (NR (EncoderBInputIndex 2 t) ⊕
    (NR (DecoderAInputIndex t) ⊕ NR (DecoderBInputIndex t))))

/-- The non-redundant physical equations. -/
noncomputable def indepConstraint : IndepIndex t → MvPolynomial (PhysicalCoordinateIndex 2 t) ℤ :=
  Sum.elim (fun _ => unitResourceConstraint (resourceCoordinates 2 t))
    (Sum.elim (fun p => isometryPartConstraint (encoderACoordinates 2 t) p.1)
      (Sum.elim (fun p => isometryPartConstraint (encoderBCoordinates 2 t) p.1)
        (Sum.elim (fun p => isometryPartConstraint (decoderACoordinates 2 t) p.1)
          (fun p => isometryPartConstraint (decoderBCoordinates 2 t) p.1))))

theorem indepConstraint_degree_le (q : IndepIndex t) : (indepConstraint t q).totalDegree ≤ 2 := by
  rcases q with q | q | q | q | q
  · exact unitResourceConstraint_degree_le _
  all_goals exact isometryPartConstraint_degree_le _ _

theorem physicalSet_iff_indep (x : PhysicalCoordinateIndex 2 t → ℝ) :
    (physicalCoordinatesEquiv 2 t).symm x ∈ physicalSet 2 t ↔
      ∀ q, eval x (indepConstraint t q) = 0 := by
  change IsUnitVector (coordinateVector (resourceCoordinates 2 t) x) ∧
    IsIsometry (coordinateMatrix (encoderACoordinates 2 t) x) ∧
    IsIsometry (coordinateMatrix (encoderBCoordinates 2 t) x) ∧
    IsIsometry (coordinateMatrix (decoderACoordinates 2 t) x) ∧
    IsIsometry (coordinateMatrix (decoderBCoordinates 2 t) x) ↔ _
  constructor
  · rintro ⟨hη, hA, hB, hDA, hDB⟩ q
    rcases q with q | q | q | q | q
    · exact (unitResourceConstraint_eval_eq_zero_iff _ x).mpr hη
    · exact (isometryPartConstraints_eval_eq_zero_iff _ x).mpr hA q.1
    · exact (isometryPartConstraints_eval_eq_zero_iff _ x).mpr hB q.1
    · exact (isometryPartConstraints_eval_eq_zero_iff _ x).mpr hDA q.1
    · exact (isometryPartConstraints_eval_eq_zero_iff _ x).mpr hDB q.1
  · intro h
    exact ⟨(unitResourceConstraint_eval_eq_zero_iff _ x).mp (h (Sum.inl ())),
      isIsometry_of_nonRed _ x fun p => h (Sum.inr (Sum.inl p)),
      isIsometry_of_nonRed _ x fun p => h (Sum.inr (Sum.inr (Sum.inl p))),
      isIsometry_of_nonRed _ x fun p => h (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))),
      isIsometry_of_nonRed _ x fun p => h (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))⟩

theorem coordinateVector_resource (y : PhysicalBlocks 2 t) :
    coordinateVector (resourceCoordinates 2 t) (physicalCoordinatesEquiv 2 t y) = y.1 := by
  funext e; apply Complex.ext <;> rfl

theorem coordinateMatrix_encoderA (y : PhysicalBlocks 2 t) :
    coordinateMatrix (encoderACoordinates 2 t) (physicalCoordinatesEquiv 2 t y) = y.2.1 := by
  ext i j; apply Complex.ext <;> rfl

theorem coordinateMatrix_encoderB (y : PhysicalBlocks 2 t) :
    coordinateMatrix (encoderBCoordinates 2 t) (physicalCoordinatesEquiv 2 t y) = y.2.2.1 := by
  ext i j; apply Complex.ext <;> rfl

theorem coordinateMatrix_decoderA (y : PhysicalBlocks 2 t) :
    coordinateMatrix (decoderACoordinates 2 t) (physicalCoordinatesEquiv 2 t y) = y.2.2.2.1 := by
  ext i j; apply Complex.ext <;> rfl

theorem coordinateMatrix_decoderB (y : PhysicalBlocks 2 t) :
    coordinateMatrix (decoderBCoordinates 2 t) (physicalCoordinatesEquiv 2 t y) = y.2.2.2.2 := by
  ext i j; apply Complex.ext <;> rfl

/-- **Independence.** At a physical point every prescribed first-order change of the
non-redundant equations is realized along a line. -/
theorem exists_line_of_physical (y : PhysicalBlocks 2 t) (hy : y ∈ physicalSet 2 t)
    (b : IndepIndex t → ℝ) :
    ∃ δ : PhysicalCoordinateIndex 2 t → ℝ, ∀ q, ∃ B : ℝ, ∀ s : ℝ,
      eval (physicalCoordinatesEquiv 2 t y + s • δ) (indepConstraint t q) =
        eval (physicalCoordinatesEquiv 2 t y) (indepConstraint t q) + s * b q + s ^ 2 * B := by
  obtain ⟨hη, hA, hB, hDA, hDB⟩ := hy
  obtain ⟨ΔA, hΔA⟩ := exists_block_direction y.2.1 hA (fun p => b (Sum.inr (Sum.inl p)))
  obtain ⟨ΔB, hΔB⟩ := exists_block_direction y.2.2.1 hB
    (fun p => b (Sum.inr (Sum.inr (Sum.inl p))))
  obtain ⟨ΔDA, hΔDA⟩ := exists_block_direction y.2.2.2.1 hDA
    (fun p => b (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))))
  obtain ⟨ΔDB, hΔDB⟩ := exists_block_direction y.2.2.2.2 hDB
    (fun p => b (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))))
  set ζ : Fin (t 0) × Fin (t 1) → ℂ := ((b (Sum.inl ()) / 2 : ℝ) : ℂ) • y.1
  refine ⟨physicalCoordinatesEquiv 2 t (ζ, ΔA, ΔB, ΔDA, ΔDB), fun q => ?_⟩
  set x := physicalCoordinatesEquiv 2 t y
  set δ := physicalCoordinatesEquiv 2 t (ζ, ΔA, ΔB, ΔDA, ΔDB)
  rcases q with q | q | q | q | q
  · cases q
    refine ⟨∑ e, Complex.normSq (ζ e), fun s => ?_⟩
    change eval (x + s • δ) (unitResourceConstraint (resourceCoordinates 2 t)) =
      eval x (unitResourceConstraint (resourceCoordinates 2 t)) + s * b (Sum.inl ()) +
        s ^ 2 * ∑ e, Complex.normSq (ζ e)
    rw [eval_unitResourceConstraint_line, coordinateVector_resource,
      show coordinateVector (resourceCoordinates 2 t) δ = ζ from coordinateVector_resource t _]
    have hunit : ∑ e, Complex.normSq (y.1 e) = 1 := hη
    have key : 2 * ∑ e, ((y.1 e).re * (ζ e).re + (y.1 e).im * (ζ e).im) = b (Sum.inl ()) := by
      simp only [ζ, Pi.smul_apply, smul_eq_mul, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
      calc 2 * ∑ e, ((y.1 e).re * (b (Sum.inl ()) / 2 * (y.1 e).re) +
            (y.1 e).im * (b (Sum.inl ()) / 2 * (y.1 e).im))
          = b (Sum.inl ()) * ∑ e, Complex.normSq (y.1 e) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun e _ => by rw [Complex.normSq_apply]; ring
        _ = b (Sum.inl ()) := by rw [hunit, mul_one]
    rw [key]
  · refine ⟨partValue ((coordinateMatrix (encoderACoordinates 2 t) δ)ᴴ *
      coordinateMatrix (encoderACoordinates 2 t) δ) q.1, fun s => ?_⟩
    refine (eval_isometryPartConstraint_line _ x δ q.1 s).trans ?_
    rw [coordinateMatrix_encoderA, show coordinateMatrix (encoderACoordinates 2 t) δ = ΔA from
      coordinateMatrix_encoderA t _, hΔA q]
    rfl
  · refine ⟨partValue ((coordinateMatrix (encoderBCoordinates 2 t) δ)ᴴ *
      coordinateMatrix (encoderBCoordinates 2 t) δ) q.1, fun s => ?_⟩
    refine (eval_isometryPartConstraint_line _ x δ q.1 s).trans ?_
    rw [coordinateMatrix_encoderB, show coordinateMatrix (encoderBCoordinates 2 t) δ = ΔB from
      coordinateMatrix_encoderB t _, hΔB q]
    rfl
  · refine ⟨partValue ((coordinateMatrix (decoderACoordinates 2 t) δ)ᴴ *
      coordinateMatrix (decoderACoordinates 2 t) δ) q.1, fun s => ?_⟩
    refine (eval_isometryPartConstraint_line _ x δ q.1 s).trans ?_
    rw [coordinateMatrix_decoderA, show coordinateMatrix (decoderACoordinates 2 t) δ = ΔDA from
      coordinateMatrix_decoderA t _, hΔDA q]
    rfl
  · refine ⟨partValue ((coordinateMatrix (decoderBCoordinates 2 t) δ)ᴴ *
      coordinateMatrix (decoderBCoordinates 2 t) δ) q.1, fun s => ?_⟩
    refine (eval_isometryPartConstraint_line _ x δ q.1 s).trans ?_
    rw [coordinateMatrix_decoderB, show coordinateMatrix (decoderBCoordinates 2 t) δ = ΔDB from
      coordinateMatrix_decoderB t _, hΔDB q]
    rfl

end Physical

end NLQCLean.PhysicalPolynomial
