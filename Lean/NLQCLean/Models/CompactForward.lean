import NLQCLean.Models.ForwardCompression
import NLQCLean.Models.UnitaryScore
import Mathlib.Topology.Order.Compact

/-!
# Compact physical forward families

The five physical blocks are a unit resource vector and four rectangular
isometries. Their constraint set is compact in each fixed finite shape.
The sixth environment vector used by Sard is absent from this family.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

/-- The coefficient unit sphere is compact, including the empty-index case. -/
theorem isCompact_unitVectors (ε : Type*) [Fintype ε] :
    IsCompact {v : ε → ℂ | IsUnitVector v} := by
  classical
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq
      (_root_.ContDiff.sum (fun e _ =>
        ContDiff.complexNormSq (by fun_prop : ContDiff ℝ (⊤ : WithTop ℕ∞)
          (fun v : ε → ℂ => v e)))).continuous continuous_const
  · apply (isBounded_iff_forall_norm_le).mpr
    refine ⟨1, fun v hv => ?_⟩
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro e
    have h : Complex.normSq (v e) ≤ 1 :=
      (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (v i))
        (Finset.mem_univ e)).trans_eq hv
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (v e)]

/-- The squared Frobenius norm of a rectangular isometry counts its columns. -/
theorem IsIsometry.frobNorm_sq_eq_card {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {V : Matrix m n ℂ} (hV : IsIsometry V) :
    ‖V‖ ^ 2 = (Fintype.card n : ℝ) := by
  have h : frobNormSq V = (Fintype.card n : ℝ) := by
    simp only [frobNormSq, frobInner_self_of_isometry hV, Complex.natCast_re]
  rw [frobNormSq_eq_sum_normSq, Fintype.sum_prod_type] at h
  simpa only [frobNorm_sq, Complex.normSq_eq_norm_sq] using h

/-- A rectangular Stiefel set is closed and bounded, hence compact. -/
theorem isCompact_isometries (m n : Type*) [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] :
    IsCompact {V : Matrix m n ℂ | IsIsometry V} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq
      (ContDiff.matrixMul
        (ContDiff.matrixConjTranspose (contDiff_id :
          ContDiff ℝ (⊤ : WithTop ℕ∞) (fun V : Matrix m n ℂ => V)))
        contDiff_id).continuous continuous_const
  · apply (isBounded_iff_forall_norm_le).mpr
    refine ⟨(Fintype.card n : ℝ) + 1, fun V hV => ?_⟩
    have h := hV.frobNorm_sq_eq_card
    have hn : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
    nlinarith [norm_nonneg V, sq_nonneg (‖V‖ - 1)]

/-- Five physical blocks, on a fixed cardinality shape. -/
abbrev PhysicalBlocks (d : ℕ) (s : Fin 8 → ℕ) :=
  (Fin (s 0) × Fin (s 1) → ℂ) ×
    Matrix (Fin (s 2) × Fin (s 4)) (Fin d × Fin (s 0)) ℂ ×
    Matrix (Fin (s 3) × Fin (s 5)) (Fin d × Fin (s 1)) ℂ ×
    Matrix (Fin d × Fin (s 6)) (Fin (s 2) × Fin (s 5)) ℂ ×
    Matrix (Fin d × Fin (s 7)) (Fin (s 3) × Fin (s 4)) ℂ

/-- Independent sphere and Stiefel constraints, with no witness vector `g`. -/
def physicalSet (d : ℕ) (s : Fin 8 → ℕ) : Set (PhysicalBlocks d s) :=
  {η | IsUnitVector η} ×ˢ
    ({VA | IsIsometry VA} ×ˢ ({VB | IsIsometry VB} ×ˢ
      ({DA | IsIsometry DA} ×ˢ {DB | IsIsometry DB})))

theorem isCompact_physicalSet (d : ℕ) (s : Fin 8 → ℕ) :
    IsCompact (physicalSet d s) :=
  (isCompact_unitVectors _).prod ((isCompact_isometries _ _).prod
    ((isCompact_isometries _ _).prod
      ((isCompact_isometries _ _).prod (isCompact_isometries _ _))))

/-- A constrained point gives an ordinary protocol in the original model. -/
def PhysicalBlocks.toProtocol {d : ℕ} {s : Fin 8 → ℕ} (x : PhysicalBlocks d s)
    (hx : x ∈ physicalSet d s) : FinProtocol d s where
  resource := x.1
  resource_unit := hx.1
  encA := x.2.1
  encB := x.2.2.1
  encA_isometry := hx.2.1
  encB_isometry := hx.2.2.1
  decA := x.2.2.2.1
  decB := x.2.2.2.2
  decA_isometry := hx.2.2.2.1
  decB_isometry := hx.2.2.2.2

/-- The normalized Choi score, defined on the whole five-block space. -/
noncomputable def physicalScore {d : ℕ} (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    {s : Fin 8 → ℕ} (x : PhysicalBlocks d s) : ℝ :=
  scoreU U (operationalChannel x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)

theorem continuous_physicalScore {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (s : Fin 8 → ℕ) :
    Continuous (physicalScore U (s := s)) := by
  have hη : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun x : PhysicalBlocks d s => x.1) := contDiff_fst
  have hVA : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun x : PhysicalBlocks d s => x.2.1) := contDiff_fst.snd'
  have hVB : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun x : PhysicalBlocks d s => x.2.2.1) := contDiff_fst.snd'.snd'
  have hDA : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun x : PhysicalBlocks d s => x.2.2.2.1) := contDiff_fst.snd'.snd'.snd'
  have hDB : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun x : PhysicalBlocks d s => x.2.2.2.2) := contDiff_snd.snd'.snd'.snd'
  have hE := ContDiff.insertResource (ιA := Fin d) (ιB := Fin d) hη
  have hEx : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun _ : PhysicalBlocks d s =>
        exchangeMatrix (Fin (s 2)) (Fin (s 4)) (Fin (s 3)) (Fin (s 5))) := contDiff_const
  have hF := ContDiff.matrixMul (ContDiff.matrixKronecker hDA hDB)
    (ContDiff.matrixMul hEx (ContDiff.matrixMul (ContDiff.matrixKronecker hVA hVB) hE))
  exact (ContDiff.scoreU_channelOf U (ContDiff.matrixSubmatrix hF
    (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))) id)).continuous

/-- The score image of one shape; empty physical shapes cause no difficulty. -/
def shapeScores {d : ℕ} (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (s : Fin 8 → ℕ) : Set ℝ := physicalScore U '' physicalSet d s

theorem isCompact_shapeScores {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (s : Fin 8 → ℕ) :
    IsCompact (shapeScores U s) :=
  (isCompact_physicalSet d s).image (continuous_physicalScore U s)

/-- Every finite-index physical protocol occurs in its shape's score image. -/
theorem FinProtocol.score_mem_shapeScores {d : ℕ} {s : Fin 8 → ℕ}
    (P : FinProtocol d s) (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    scoreU U P.operationalChannel ∈ shapeScores U s :=
  ⟨(P.resource, P.encA, P.encB, P.decA, P.decB),
    ⟨P.resource_unit, P.encA_isometry, P.encB_isometry, P.decA_isometry, P.decB_isometry⟩,
    rfl⟩

/-- A finite box of internal dimensions supplied by exact compression. -/
abbrev BoundedShape (d K : ℕ) := Fin 8 → Fin (d ^ 2 * K + 1)

/-- The finite union of physical score images, with zero adjoined for a maximum.
Extra shapes in the bounding box are allowed; no claim of footprint at most K
is made for every point of this superset. -/
def boundedShapeScores {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) : Set ℝ :=
  (⋃ s : BoundedShape d K, shapeScores U (fun i => (s i).val)) ∪ {0}

theorem isCompact_boundedShapeScores {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) :
    IsCompact (boundedShapeScores U K) := by
  unfold boundedShapeScores
  apply IsCompact.union
  · exact isCompact_iUnion (fun s : BoundedShape d K =>
      isCompact_shapeScores U (fun i => (s i).val))
  · exact isCompact_singleton

theorem boundedShapeScores_nonempty {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) :
    (boundedShapeScores U K).Nonempty := ⟨0, Or.inr rfl⟩

/-- Exact compression places every budget-K score in this finite compact union. -/
theorem PureProtocol.score_mem_boundedShapeScores {d : ℕ} (hd : 2 ≤ d)
    {ρA ρB κA κB μA μB εA εB : Type*}
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (K : ℕ) (hK : P.HasFootprint K) :
    scoreU U P.operationalChannel ∈ boundedShapeScores U K := by
  obtain ⟨s, hs, Q, _, hchan⟩ := P.exists_bounded_fin_representative hd K hK
  rw [hchan]
  apply Or.inl
  apply Set.mem_iUnion.mpr
  refine ⟨fun i => ⟨s i, Nat.lt_succ_of_le (hs i).2⟩, ?_⟩
  exact Q.score_mem_shapeScores U

end NLQCLean
