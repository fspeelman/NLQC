/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.PolynomialImageVolumeHypothesis
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Concrete polynomial sign descriptions

The format definitions follow LRT Definitions 6--7.
A description is a finite disjunction of finite conjunctions of signed
real polynomial atoms. Empty conjunctions and disjunctions have their usual
truth values. Diagram complexity is disjunct count times maximum clause length.
No projection, dimension, stratification, or volume theorem is assumed here.
-/

section

namespace NLQCLean

/-- The three signs used in LRT's polynomial descriptions. -/
inductive PolynomialSign where
  | negative | zero | positive
  deriving DecidableEq

instance : Fintype PolynomialSign :=
  ⟨{.negative, .zero, .positive}, by intro s; cases s <;> simp⟩

/-- Interpretation of a sign, with strict inequalities for nonzero signs. -/
def PolynomialSign.Holds : PolynomialSign → ℝ → Prop
  | .negative, t => t < 0
  | .zero, t => t = 0
  | .positive, t => 0 < t

/-- A single signed real polynomial atom. -/
structure PolynomialSignAtom (n : ℕ) where
  polynomial : MvPolynomial (Fin n) ℝ
  sign : PolynomialSign

/-- Euclidean evaluation of an atom. -/
def PolynomialSignAtom.Holds {n : ℕ} (A : PolynomialSignAtom n)
    (x : RealEuclidean n) : Prop :=
  A.sign.Holds (MvPolynomial.eval (fun i => x i) A.polynomial)

/-- A finite polynomial sign description, without any imposed format cap. -/
structure PolynomialSignDNF (n : ℕ) where
  clauses : List (List (PolynomialSignAtom n))

/-- Conjunction of a list of atoms. -/
def PolynomialSignDNF.clauseHolds {n : ℕ} (L : List (PolynomialSignAtom n))
    (x : RealEuclidean n) : Prop := ∀ A ∈ L, A.Holds x

/-- The set represented by a finite polynomial sign description. -/
def PolynomialSignDNF.source {n : ℕ} (F : PolynomialSignDNF n) : Set (RealEuclidean n) :=
  {x | ∃ L ∈ F.clauses, clauseHolds L x}

/-- Maximum number of atoms in a clause; zero for the empty disjunction. -/
def PolynomialSignDNF.maxAtoms {n : ℕ} (F : PolynomialSignDNF n) : ℕ :=
  (F.clauses.map List.length).foldr max 0

/-- LRT's diagram bound: the product of disjunct count and maximum clause
length, together with a total-degree cap on every atom. -/
def PolynomialSignDNF.HasFormat {n : ℕ} (F : PolynomialSignDNF n) (c D : ℕ) : Prop :=
  F.clauses.length * F.maxAtoms ≤ c ∧
    ∀ L ∈ F.clauses, ∀ A ∈ L, A.polynomial.totalDegree ≤ D

/-- Semialgebraic means existence of a concrete finite polynomial description. -/
def Semialgebraic {n : ℕ} (S : Set (RealEuclidean n)) : Prop :=
  ∃ F : PolynomialSignDNF n, F.source = S

namespace PolynomialSignDNF

variable {n m : ℕ}

@[simp] theorem clauseHolds_nil (x : RealEuclidean n) : clauseHolds [] x := by
  simp [clauseHolds]

@[simp] theorem clauseHolds_cons (A : PolynomialSignAtom n) (L) (x) :
    clauseHolds (A :: L) x ↔ A.Holds x ∧ clauseHolds L x := by
  simp [clauseHolds]

@[simp] theorem clauseHolds_append (L K : List (PolynomialSignAtom n)) (x) :
    clauseHolds (L ++ K) x ↔ clauseHolds L x ∧ clauseHolds K x := by
  simp only [clauseHolds, List.mem_append]
  aesop

/-- The empty disjunction. -/
def empty (n : ℕ) : PolynomialSignDNF n := ⟨[]⟩

/-- One empty conjunction. -/
def univ (n : ℕ) : PolynomialSignDNF n := ⟨[[]]⟩

/-- One atom as a DNF. -/
def atom (A : PolynomialSignAtom n) : PolynomialSignDNF n := ⟨[[A]]⟩

@[simp] theorem source_empty : (empty n).source = ∅ := by
  ext x; simp [source, empty]

@[simp] theorem source_univ : (univ n).source = Set.univ := by
  ext x; simp [source, univ]

@[simp] theorem source_atom (A : PolynomialSignAtom n) : (atom A).source = {x | A.Holds x} := by
  ext x; simp [source, atom, clauseHolds]

@[simp] theorem maxAtoms_empty : (empty n).maxAtoms = 0 := rfl
@[simp] theorem maxAtoms_univ : (univ n).maxAtoms = 0 := rfl

/-- Disjunction by concatenation. -/
def disj (F G : PolynomialSignDNF n) : PolynomialSignDNF n := ⟨F.clauses ++ G.clauses⟩

@[simp] theorem source_disj (F G : PolynomialSignDNF n) :
    (F.disj G).source = F.source ∪ G.source := by
  ext x; simp [source, disj, or_and_right, exists_or]

/-- Conjunction by distributing over the two finite lists of clauses. -/
def conj (F G : PolynomialSignDNF n) : PolynomialSignDNF n :=
  ⟨F.clauses.flatMap fun L => G.clauses.map (L ++ ·)⟩

@[simp] theorem source_conj (F G : PolynomialSignDNF n) :
    (F.conj G).source = F.source ∩ G.source := by
  ext x
  simp only [source, conj, Set.mem_ofPred_eq, Set.mem_inter_iff,
    List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨L, hL, K, hK, rfl⟩, h⟩
    exact ⟨⟨L, hL, (clauseHolds_append L K x).mp h |>.1⟩,
      ⟨K, hK, (clauseHolds_append L K x).mp h |>.2⟩⟩
  · rintro ⟨⟨L, hL, hx⟩, ⟨K, hK, hy⟩⟩
    exact ⟨L ++ K, ⟨L, hL, K, hK, rfl⟩, (clauseHolds_append L K x).mpr ⟨hx, hy⟩⟩

/-- Complement of an atom, splitting into the other two signs. -/
def notAtom (A : PolynomialSignAtom n) : PolynomialSignDNF n :=
  match A.sign with
  | .negative => (atom ⟨A.polynomial, .zero⟩).disj (atom ⟨A.polynomial, .positive⟩)
  | .zero => (atom ⟨A.polynomial, .negative⟩).disj (atom ⟨A.polynomial, .positive⟩)
  | .positive => (atom ⟨A.polynomial, .negative⟩).disj (atom ⟨A.polynomial, .zero⟩)

@[simp] theorem source_notAtom (A : PolynomialSignAtom n) :
    (notAtom A).source = {x | ¬ A.Holds x} := by
  ext x
  rcases A with ⟨p, s⟩
  cases s <;>
    simp only [notAtom, source_disj, source_atom, Set.mem_union, Set.mem_ofPred_eq,
      PolynomialSignAtom.Holds, PolynomialSign.Holds]
  all_goals
    rcases lt_trichotomy (MvPolynomial.eval (fun i => x i) p) 0 with h | h | h <;>
      simp_all <;> (try constructor) <;> linarith

/-- De Morgan's law for a finite conjunction. -/
def notClause : List (PolynomialSignAtom n) → PolynomialSignDNF n
  | [] => empty n
  | A :: L => (notAtom A).disj (notClause L)

@[simp] theorem source_notClause (L : List (PolynomialSignAtom n)) :
    (notClause L).source = {x | ¬ clauseHolds L x} := by
  induction L with
  | nil => ext x; simp [notClause]
  | cons A L ih =>
    rw [notClause, source_disj, source_notAtom, ih]
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, clauseHolds_cons]
    tauto

/-- Complement of a finite disjunction, again as a finite DNF. -/
def compl (F : PolynomialSignDNF n) : PolynomialSignDNF n :=
  F.clauses.foldr (fun L G => (notClause L).conj G) (univ n)

@[simp] theorem source_compl (F : PolynomialSignDNF n) : F.compl.source = F.sourceᶜ := by
  rcases F with ⟨Ls⟩
  induction Ls with
  | nil => ext x; simp [compl, source, univ]
  | cons L Ls ih =>
    ext x
    simp only [compl, List.foldr_cons, source_conj, source_notClause,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    change (¬ clauseHolds L x ∧ x ∈ (PolynomialSignDNF.compl ⟨Ls⟩).source) ↔ _
    rw [ih]
    simp [source, not_or, not_and]

/-- Polynomial substitution, retaining the exact finite Boolean template. -/
noncomputable def pullback (F : PolynomialSignDNF n)
    (q : Fin n → MvPolynomial (Fin m) ℝ) : PolynomialSignDNF m :=
  ⟨F.clauses.map fun L => L.map fun A => ⟨MvPolynomial.bind₁ q A.polynomial, A.sign⟩⟩

/-- Evaluate a polynomial coordinate family in the Euclidean target. -/
noncomputable def polynomialMap (q : Fin n → MvPolynomial (Fin m) ℝ)
    (x : RealEuclidean m) : RealEuclidean n :=
  WithLp.toLp 2 (fun i => MvPolynomial.eval (fun j => x j) (q i))

@[simp] theorem source_pullback (F : PolynomialSignDNF n)
    (q : Fin n → MvPolynomial (Fin m) ℝ) :
    (F.pullback q).source = polynomialMap q ⁻¹' F.source := by
  ext x
  have heval (p : MvPolynomial (Fin n) ℝ) :
      MvPolynomial.eval (fun j => x j) (MvPolynomial.bind₁ q p) =
        MvPolynomial.eval (fun i => polynomialMap q x i) p :=
    MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℝ) (fun j => x j) q p
  simp only [source, pullback, List.mem_map, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨_, ⟨L, hL, rfl⟩, hx⟩
    refine ⟨L, hL, ?_⟩
    simpa only [clauseHolds, List.forall_mem_map, PolynomialSignAtom.Holds, heval] using hx
  · rintro ⟨L, hL, hx⟩
    refine ⟨_, ⟨L, hL, rfl⟩, ?_⟩
    simpa only [clauseHolds, List.forall_mem_map, PolynomialSignAtom.Holds, heval] using hx

/-- Weak inequalities split into zero and positive signs, without changing
which Euclidean points satisfy the condition. -/
theorem nonnegative_eq_source (p : MvPolynomial (Fin n) ℝ) :
    {x : RealEuclidean n | 0 ≤ MvPolynomial.eval (fun i => x i) p} =
      ((atom ⟨p, .zero⟩).disj (atom ⟨p, .positive⟩)).source := by
  ext x
  simp [PolynomialSignAtom.Holds, PolynomialSign.Holds, eq_comm, le_iff_eq_or_lt]

theorem HasFormat.mono {F : PolynomialSignDNF n} {c D c' D' : ℕ}
    (h : F.HasFormat c D) (hc : c ≤ c') (hD : D ≤ D') : F.HasFormat c' D' :=
  ⟨h.1.trans hc, fun L hL A hA => (h.2 L hL A hA).trans hD⟩

end PolynomialSignDNF

namespace Semialgebraic

variable {n m : ℕ} {S T : Set (RealEuclidean n)}

theorem empty : Semialgebraic (∅ : Set (RealEuclidean n)) :=
  ⟨PolynomialSignDNF.empty n, PolynomialSignDNF.source_empty⟩

theorem univ : Semialgebraic (Set.univ : Set (RealEuclidean n)) :=
  ⟨PolynomialSignDNF.univ n, PolynomialSignDNF.source_univ⟩

theorem union (hS : Semialgebraic S) (hT : Semialgebraic T) : Semialgebraic (S ∪ T) := by
  obtain ⟨F, rfl⟩ := hS
  obtain ⟨G, rfl⟩ := hT
  exact ⟨F.disj G, F.source_disj G⟩

theorem inter (hS : Semialgebraic S) (hT : Semialgebraic T) : Semialgebraic (S ∩ T) := by
  obtain ⟨F, rfl⟩ := hS
  obtain ⟨G, rfl⟩ := hT
  exact ⟨F.conj G, F.source_conj G⟩

theorem compl (hS : Semialgebraic S) : Semialgebraic Sᶜ := by
  obtain ⟨F, rfl⟩ := hS
  exact ⟨F.compl, F.source_compl⟩

theorem polynomial_preimage (hS : Semialgebraic S)
    (q : Fin n → MvPolynomial (Fin m) ℝ) :
    Semialgebraic (PolynomialSignDNF.polynomialMap q ⁻¹' S) := by
  obtain ⟨F, rfl⟩ := hS
  exact ⟨F.pullback q, F.source_pullback q⟩

end Semialgebraic
end NLQCLean
end
