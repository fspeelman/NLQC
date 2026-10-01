/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.BasicClosedFormat
import NLQCLean.Semialgebraic.Dimension
import NLQCLean.Semialgebraic.ParametricFormat

/-!
# The polynomial graph has the fixed LRT format

All graph equations are encoded by one polynomial of degree
at most 200. The sign format budget is the dimension-independent 21*2^20.
-/

section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace NLQCLean

@[fun_prop] theorem contDiff_mvPolynomial_eval {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ 1 (fun x : RealEuclidean n => MvPolynomial.eval (fun i => x i) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : RealEuclidean n => a))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, MvPolynomial.eval_X] using hp.mul (contDiff_piLp_apply 2 (i := i))

@[fun_prop] theorem contDiff_polynomialMap {n m : ℕ} (q : Fin m → MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ 1 (PolynomialSignDNF.polynomialMap q) := by
  apply (contDiff_piLp 2).2
  intro j
  exact contDiff_mvPolynomial_eval (q j)

@[fun_prop] theorem BoundedPolynomialMap.contDiff_eval {n m : ℕ} (p : BoundedPolynomialMap n m) :
    ContDiff ℝ 1 p.eval := contDiff_polynomialMap p.coordinates

theorem BoundedPolynomialMap.volume_image_eq_zero_of_dimension_lt {a m : ℕ}
    (p : BoundedPolynomialMap a m) (S : Set (RealEuclidean a)) (ham : a < m) :
    volume (p.eval '' S) = 0 := by
  apply volume_eq_zero_of_dimH_lt
  have h := (dimH_mono (image_subset_range p.eval S)).trans p.contDiff_eval.dimH_range_le
  exact h.trans_lt (by simpa using (show (a : ℝ≥0∞) < m by exact_mod_cast ham))

noncomputable def polynomialGraphEquation {a m : ℕ} (p : BoundedPolynomialMap a m) :
    MvPolynomial (Fin (a + m)) ℝ :=
  ∑ j, (MvPolynomial.X (Fin.natAdd a j) - MvPolynomial.rename (Fin.castAdd m) (p.coordinates j)) ^ 2

theorem polynomialGraphEquation_degree_le {a m : ℕ} (p : BoundedPolynomialMap a m) :
    (polynomialGraphEquation p).totalDegree ≤ 200 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  apply (MvPolynomial.totalDegree_pow _ 2).trans
  have hbase : (MvPolynomial.X (Fin.natAdd a j) -
      MvPolynomial.rename (Fin.castAdd m) (p.coordinates j)).totalDegree ≤ 100 :=
    (MvPolynomial.totalDegree_sub _ _).trans
    (max_le (by simp) ((MvPolynomial.totalDegree_rename_le _ _).trans (p.degree_le j)))
  omega

theorem polynomialGraphEquation_eq_zero_iff {a m : ℕ} (p : BoundedPolynomialMap a m)
    (z : RealEuclidean (a + m)) :
    MvPolynomial.eval (fun i => z i) (polynomialGraphEquation p) = 0 ↔
      coordinateProjection (Fin.natAdd a) z = p.eval (coordinateProjection (Fin.castAdd m) z) := by
  simp only [polynomialGraphEquation, map_sum, map_pow]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)]
  simp only [Finset.mem_univ, forall_const, sq_eq_zero_iff, map_sub, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, sub_eq_zero]
  constructor
  · intro h
    ext j
    exact h j
  · intro h j
    exact congrArg (fun x : RealEuclidean m => x j) h

def polynomialGraphSource {a m : ℕ} (F : PolynomialBasicClosedFormat a) (p : BoundedPolynomialMap a m) :
    Set (RealEuclidean (a + m)) := (fun x => euclideanPair x (p.eval x)) '' F.source

theorem polynomialGraphSource_isCompact {a m : ℕ}
    (F : PolynomialBasicClosedFormat a) (p : BoundedPolynomialMap a m) (hF : IsCompact F.source) :
    IsCompact (polynomialGraphSource F p) := by
  apply hF.image
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa using (PiLp.continuous_apply 2 (fun _ : Fin a => ℝ) j)
  · simpa [Function.comp_def] using
      (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) j).comp p.contDiff_eval.continuous

noncomputable def polynomialGraphSignDescription {a m : ℕ}
    (F : PolynomialBasicClosedFormat a) (p : BoundedPolynomialMap a m) : PolynomialSignDNF (a + m) :=
  basicClosedSignDescription
    (Fin.cons (polynomialGraphEquation p)
      (fun i => MvPolynomial.rename (Fin.castAdd m) (F.equations i)))
    (fun j => MvPolynomial.rename (Fin.castAdd m) (F.inequalities j))

theorem source_polynomialGraphSignDescription {a m : ℕ}
    (F : PolynomialBasicClosedFormat a) (p : BoundedPolynomialMap a m) :
    (polynomialGraphSignDescription F p).source = polynomialGraphSource F p := by
  rw [polynomialGraphSignDescription, source_basicClosedSignDescription]
  ext z
  simp only [mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    polynomialGraphEquation_eq_zero_iff, MvPolynomial.eval_rename]
  constructor
  · rintro ⟨⟨hgraph, heq⟩, hineq⟩
    refine ⟨coordinateProjection (Fin.castAdd m) z, ⟨heq, hineq⟩, ?_⟩
    change euclideanPair (coordinateProjection (Fin.castAdd m) z)
      (p.eval (coordinateProjection (Fin.castAdd m) z)) = z
    rw [← hgraph]
    exact euclideanPair_projections z
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨by simp, ?_⟩, ?_⟩
    · simpa only [Function.comp_def, euclideanPair_left] using hx.1
    · simpa only [Function.comp_def, euclideanPair_left] using hx.2

def lrtGraphFormatBudget : ℕ := 21 * 2 ^ 20

theorem polynomialGraphSource_hasFormat {a m : ℕ}
    (F : PolynomialBasicClosedFormat a) (p : BoundedPolynomialMap a m) :
    HasSemialgebraicFormat (polynomialGraphSource F p) lrtGraphFormatBudget 200 := by
  refine ⟨polynomialGraphSignDescription F p, source_polynomialGraphSignDescription F p, ?_⟩
  let eqs : Fin (F.numEquations + 1) → MvPolynomial (Fin (a + m)) ℝ :=
    Fin.cons (polynomialGraphEquation p)
      (fun i => MvPolynomial.rename (Fin.castAdd m) (F.equations i))
  have heq : ∀ i, (eqs i).totalDegree ≤ 200 := by
    refine Fin.cases (polynomialGraphEquation_degree_le p) ?_
    intro i
    exact (MvPolynomial.totalDegree_rename_le _ _).trans ((F.equations_degree i).trans (by omega))
  have hineq : ∀ j, (MvPolynomial.rename (Fin.castAdd m) (F.inequalities j)).totalDegree ≤ 200 := by
    intro j
    exact (MvPolynomial.totalDegree_rename_le _ _).trans ((F.inequalities_degree j).trans (by omega))
  apply (basicClosedSignDescription_hasFormat _ _ heq hineq).mono
  · have hcount := F.constraint_count
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))
  · exact le_rfl

end NLQCLean
end
