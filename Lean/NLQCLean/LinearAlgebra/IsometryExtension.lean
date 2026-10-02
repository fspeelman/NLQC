import NLQCLean.LinearAlgebra.SupportFactorization
import NLQCLean.LinearAlgebra.IsometricCompletion

/-!
# Extending isometries to a prescribed number of columns

An isometry with `r` columns into an index set of size at least `k ≥ r` is the restriction of an
isometry with exactly `k` columns (extend its orthonormal columns to an orthonormal basis). The
coefficient-support factorizations can therefore be taken with any prescribed inner dimension
between the actual rank bound and the size of the register; this gives one register size for
all branches of an instrument.
-/

namespace NLQCLean

open Matrix WithLp
open scoped Kronecker

/-- **Isometry extension.** -/
theorem exists_isometry_extension {κ : Type*} [Fintype κ] [DecidableEq κ] {r k : ℕ}
    (hrk : r ≤ k) (hk : k ≤ Fintype.card κ) {J₀ : Matrix κ (Fin r) ℂ} (hJ₀ : IsIsometry J₀) :
    ∃ J : Matrix κ (Fin k) ℂ, IsIsometry J ∧ ∀ a j, J a (Fin.castLE hrk j) = J₀ a j := by
  classical
  set n := Fintype.card κ with hn
  have hfin : Module.finrank ℂ (EuclideanSpace ℂ κ) = Fintype.card (Fin n) := by
    simp [n]
  let v : Fin n → EuclideanSpace ℂ κ := fun i =>
    if h : i.val < r then toLp 2 (fun a => J₀ a ⟨i.val, h⟩) else 0
  let s : Set (Fin n) := {i | i.val < r}
  have hv : Orthonormal ℂ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i.val < r := hi
    have hj' : j.val < r := hj
    have hJ := congrFun (congrFun hJ₀ ⟨i.val, hi'⟩) ⟨j.val, hj'⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.mk.injEq] at hJ
    simp only [Set.domRestrict_apply, v, dite_eq_left hi', dite_eq_left hj',
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, Subtype.mk.injEq]
    have hsum : (∑ x, J₀ x ⟨j.val, hj'⟩ * star (J₀ x ⟨i.val, hi'⟩)) =
        ∑ x, star (J₀ x ⟨i.val, hi'⟩) * J₀ x ⟨j.val, hj'⟩ :=
      Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [hsum, hJ]
    exact if_congr Fin.val_inj rfl rfl
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hfin
  let J : Matrix κ (Fin k) ℂ := fun a l => (b (Fin.castLE hk l) : EuclideanSpace ℂ κ) a
  refine ⟨J, ?_, fun a j => ?_⟩
  · unfold IsIsometry
    ext i j
    change (∑ a, star (J a i) * J a j) = if i = j then 1 else 0
    have h := b.inner_eq_ite (Fin.castLE hk i) (Fin.castLE hk j)
    have hinj : Fin.castLE hk i = Fin.castLE hk j ↔ i = j := (Fin.castLE_injective hk).eq_iff
    have h' : inner ℂ (b (Fin.castLE hk i)) (b (Fin.castLE hk j)) = if i = j then 1 else 0 := by
      rw [h]
      exact if_congr hinj rfl rfl
    simpa only [J, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
      mul_comm] using h'
  · have hmem : Fin.castLE hk (Fin.castLE hrk j) ∈ s := by
      change (Fin.castLE hk (Fin.castLE hrk j)).val < r
      simp
    change (b (Fin.castLE hk (Fin.castLE hrk j)) : EuclideanSpace ℂ κ) a = J₀ a j
    rw [hb _ hmem]
    simp [v]

/-- The extended isometry composed with the coordinate inclusion is the original one. -/
theorem exists_isometry_extension_mul {κ : Type*} [Fintype κ] [DecidableEq κ] {r k : ℕ}
    (hrk : r ≤ k) (hk : k ≤ Fintype.card κ) {J₀ : Matrix κ (Fin r) ℂ} (hJ₀ : IsIsometry J₀) :
    ∃ J : Matrix κ (Fin k) ℂ, IsIsometry J ∧
      J * coordinateInclusion (Fin.castLEEmb hrk) = J₀ := by
  obtain ⟨J, hJ, hext⟩ := exists_isometry_extension hrk hk hJ₀
  refine ⟨J, hJ, ?_⟩
  ext a j
  simp [Matrix.mul_apply, coordinateInclusion, hext]

/-- Left coefficient factorization with a prescribed inner dimension. -/
theorem exists_left_coefficient_factorization_of_le {κ μ ι : Type*}
    [Fintype κ] [Fintype μ] [Fintype ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ι]
    (V : Matrix (κ × μ) ι ℂ) {k : ℕ}
    (hk : min (Fintype.card ι * Fintype.card μ) (Fintype.card κ) ≤ k)
    (hkκ : k ≤ Fintype.card κ) :
    ∃ J : Matrix κ (Fin k) ℂ, ∃ B : Matrix (Fin k × μ) ι ℂ,
      IsIsometry J ∧ V = (J ⊗ₖ (1 : Matrix μ μ ℂ)) * B := by
  obtain ⟨r, hr, J₀, B₀, hJ₀, hV⟩ := exists_left_coefficient_factorization V
  have hrκ : r ≤ Fintype.card κ := by simpa using hJ₀.card_le
  have hrk : r ≤ k := (le_min hr hrκ).trans hk
  obtain ⟨J, hJ, hJJ⟩ := exists_isometry_extension_mul hrk hkκ hJ₀
  refine ⟨J, (coordinateInclusion (Fin.castLEEmb hrk) ⊗ₖ (1 : Matrix μ μ ℂ)) * B₀, hJ, ?_⟩
  rw [hV, ← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, hJJ, Matrix.one_mul]

/-- Right coefficient factorization with a prescribed inner dimension. -/
theorem exists_right_coefficient_factorization_of_le {ι ε κ : Type*}
    [Fintype ι] [Fintype ε] [Fintype κ] [DecidableEq ι] [DecidableEq ε] [DecidableEq κ]
    (D : Matrix (ι × ε) κ ℂ) {k : ℕ}
    (hk : min (Fintype.card ι * Fintype.card κ) (Fintype.card ε) ≤ k)
    (hkε : k ≤ Fintype.card ε) :
    ∃ J : Matrix ε (Fin k) ℂ, ∃ B : Matrix (ι × Fin k) κ ℂ,
      IsIsometry J ∧ D = ((1 : Matrix ι ι ℂ) ⊗ₖ J) * B := by
  obtain ⟨r, hr, J₀, B₀, hJ₀, hD⟩ := exists_right_coefficient_factorization D
  have hrε : r ≤ Fintype.card ε := by simpa using hJ₀.card_le
  have hrk : r ≤ k := (le_min hr hrε).trans hk
  obtain ⟨J, hJ, hJJ⟩ := exists_isometry_extension_mul hrk hkε hJ₀
  refine ⟨J, ((1 : Matrix ι ι ℂ) ⊗ₖ coordinateInclusion (Fin.castLEEmb hrk)) * B₀, hJ, ?_⟩
  rw [hD, ← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, hJJ, Matrix.one_mul]

end NLQCLean
