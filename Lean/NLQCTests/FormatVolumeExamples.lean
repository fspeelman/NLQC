/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NLQCLean.Semialgebraic.FormatVolumeContinuity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Regression examples for bounded-format volume convergence

The examples cover collapsing rectangles, zero atoms, positive coefficient
rescaling and empty-set Hausdorff conventions. The rectangle limit is a
line segment, so its two-dimensional volume is zero.
-/

section

open MeasureTheory Filter Metric
open scoped Topology ENNReal

namespace NLQCLean.FormatVolumeExamples

noncomputable def nonnegative (p : MvPolynomial (Fin 2) ℝ) : PolynomialSignDNF 2 :=
  (PolynomialSignDNF.atom ⟨p, .zero⟩).disj (PolynomialSignDNF.atom ⟨p, .positive⟩)

theorem source_nonnegative (p : MvPolynomial (Fin 2) ℝ) :
    (nonnegative p).source = {x | 0 ≤ MvPolynomial.eval (fun i => x i) p} :=
  (PolynomialSignDNF.nonnegative_eq_source p).symm

def rectangle (e : ℝ) : Set (RealEuclidean 2) :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ e}

noncomputable def rectangleDescription (e : ℝ) : PolynomialSignDNF 2 :=
  (((nonnegative (MvPolynomial.X 0)).conj
    (nonnegative (MvPolynomial.C 1 - MvPolynomial.X 0))).conj
    (nonnegative (MvPolynomial.X 1))).conj
    (nonnegative (MvPolynomial.C e - MvPolynomial.X 1))

theorem source_rectangleDescription (e : ℝ) : (rectangleDescription e).source = rectangle e := by
  ext x
  simp only [rectangleDescription, PolynomialSignDNF.source_conj, source_nonnegative,
    Set.mem_inter_iff, Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_C,
    MvPolynomial.eval_X, rectangle]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
    exact ⟨h0, by linarith, h2, by linarith⟩
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨⟨⟨h0, by linarith⟩, h2⟩, by linarith⟩

theorem rectangle_hasFormat (e : ℝ) : HasSemialgebraicFormat (rectangle e) 64 1 := by
  have hdeg (t : ℝ) (i : Fin 2) :
      (MvPolynomial.C t - MvPolynomial.X i : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  have hdeg1 : (1 - MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 :=
    by simpa using hdeg 1 0
  refine ⟨rectangleDescription e, source_rectangleDescription e, ?_⟩
  simp [PolynomialSignDNF.HasFormat, rectangleDescription, nonnegative,
    PolynomialSignDNF.conj, PolynomialSignDNF.disj, PolynomialSignDNF.atom,
    PolynomialSignDNF.maxAtoms, hdeg, hdeg1]

theorem rectangle_isClosed (e : ℝ) : IsClosed (rectangle e) := by
  unfold rectangle
  have hc (i : Fin 2) : Continuous (fun x : RealEuclidean 2 => x i) := by fun_prop
  exact (isClosed_le continuous_const (hc 0)).inter
    ((isClosed_le (hc 0) continuous_const).inter
      ((isClosed_le continuous_const (hc 1)).inter (isClosed_le (hc 1) continuous_const)))

theorem rectangle_subset_ball {e : ℝ} (he : e ≤ 1) : rectangle e ⊆ closedBall 0 2 := by
  intro x hx
  obtain ⟨h0, h1, h2, h3⟩ := hx
  have hnorm := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_two] at hnorm
  have hx0 : (x 0) ^ 2 ≤ 1 := by nlinarith
  have hx1 : (x 1) ^ 2 ≤ 1 := by nlinarith
  simp only [mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg x]

theorem rectangle_isCompact {e : ℝ} (he : e ≤ 1) : IsCompact (rectangle e) :=
  (isCompact_closedBall (0 : RealEuclidean 2) 2).of_isClosed_subset
    (rectangle_isClosed e) (rectangle_subset_ball he)

theorem rectangle_hausdorff_le {e : ℝ} (he : 0 ≤ e) :
    hausdorffEDist (rectangle e) (rectangle 0) ≤ ENNReal.ofReal e := by
  apply hausdorffEDist_le_of_mem_edist
  · intro x hx
    let y : RealEuclidean 2 := WithLp.toLp 2 ![x 0, 0]
    have hy : y ∈ rectangle 0 := by
      exact ⟨hx.1, hx.2.1, le_rfl, le_rfl⟩
    refine ⟨y, hy, (edist_le_ofReal he).mpr ?_⟩
    have hnorm := EuclideanSpace.real_norm_sq_eq (x - y)
    simp [Fin.sum_univ_two, y] at hnorm
    rw [dist_eq_norm]
    have := hx.2.2
    nlinarith [norm_nonneg (x - y)]
  · intro x hx
    refine ⟨x, ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.trans he⟩, ?_⟩
    simp

theorem rectangle_zero_volume : volume (rectangle 0) = 0 := by
  apply measure_mono_null (t := {x : RealEuclidean 2 | MvPolynomial.eval (fun i => x i)
    (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ) = 0})
  · intro x hx
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X]
    exact le_antisymm hx.2.2.2 hx.2.2.1
  · exact mvPolynomial_zeroSet_volume_eq_zero _ (MvPolynomial.X_ne_zero _)

/-- The two-dimensional collapsing-rectangle regression, with
compactness, bounded format and Hausdorff convergence. -/
theorem shrinking_rectangles_volume :
    Tendsto (fun k : ℕ => volume (rectangle (1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
  have hpos (k : ℕ) : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
  have hone (k : ℕ) : 1 / ((k : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hhaus : Tendsto (fun k : ℕ => hausdorffEDist
      (rectangle (1 / ((k : ℝ) + 1))) (rectangle 0)) atTop (𝓝 0) := by
    have hupper : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k
      exact bot_le
    · intro k
      exact rectangle_hausdorff_le (hpos k)
  simpa only [rectangle_zero_volume] using
    tendsto_volume_of_bounded_format_hausdorff
      (fun k : ℕ => rectangle (1 / ((k : ℝ) + 1))) (rectangle 0)
      (fun k => rectangle_isCompact (hone k)) (rectangle_isClosed 0)
      (fun k => rectangle_hasFormat _) 2 (fun k => rectangle_subset_ball (hone k)) hhaus

theorem zero_atom_source (n : ℕ) :
    (PolynomialSignDNF.atom (⟨0, .zero⟩ : PolynomialSignAtom n)).source = Set.univ ∧
    (PolynomialSignDNF.atom (⟨0, .positive⟩ : PolynomialSignAtom n)).source = ∅ := by
  simp [PolynomialSignAtom.Holds, PolynomialSign.Holds]

theorem positive_rescaling_source {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (s : PolynomialSign) {t : ℝ} (ht : 0 < t) :
    (PolynomialSignDNF.atom ⟨t • p, s⟩).source = (PolynomialSignDNF.atom ⟨p, s⟩).source := by
  ext x
  simp only [PolynomialSignDNF.source_atom, Set.mem_ofPred_eq, PolynomialSignAtom.Holds]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
  cases s <;> simp only [PolynomialSign.Holds] <;> constructor <;> intro h <;> nlinarith

theorem empty_hausdorff_singleton (n : ℕ) :
    hausdorffEDist (∅ : Set (RealEuclidean n)) {0} = ∞ := by
  rw [hausdorffEDist_comm]
  exact hausdorffEDist_empty (Set.singleton_nonempty 0)

/-- A zero-format empty sequence satisfies the theorem in every dimension,
including dimension zero. -/
theorem empty_sequence_volume (n : ℕ) :
    Tendsto (fun _ : ℕ => volume (∅ : Set (RealEuclidean n))) atTop (𝓝 0) := by
  have hf : HasSemialgebraicFormat (∅ : Set (RealEuclidean n)) 0 0 :=
    ⟨PolynomialSignDNF.empty n, by simp, by simp [PolynomialSignDNF.HasFormat,
      PolynomialSignDNF.empty, PolynomialSignDNF.maxAtoms]⟩
  simpa only [measure_empty] using tendsto_volume_of_bounded_format_hausdorff
    (fun _ : ℕ => (∅ : Set (RealEuclidean n))) ∅ (fun _ => isCompact_empty) isClosed_empty
    (fun _ => hf) 0 (fun _ => Set.empty_subset _) (by simp)

end NLQCLean.FormatVolumeExamples
end
