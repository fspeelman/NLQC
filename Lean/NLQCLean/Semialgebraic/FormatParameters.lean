/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.Objects
import NLQCLean.Geometry.PolynomialCoefficients
import Mathlib.Topology.Sequences

/-!
# Fixed finite templates for bounded polynomial formats

Empty conjunctions/disjunctions are handled explicitly
before using the product format bound. Coefficients remain arbitrary reals.
-/

section

namespace NLQCLean

namespace PolynomialSignDNF

theorem length_le_maxAtoms {n : ℕ} (F : PolynomialSignDNF n)
    {L : List (PolynomialSignAtom n)} (hL : L ∈ F.clauses) : L.length ≤ F.maxAtoms := by
  exact List.le_max_of_le (List.mem_map.mpr ⟨L, hL, rfl⟩) le_rfl

theorem source_eq_univ_of_maxAtoms_eq_zero {n : ℕ} (F : PolynomialSignDNF n)
    (hF : F.clauses ≠ []) (hm : F.maxAtoms = 0) : F.source = Set.univ := by
  obtain ⟨L, hL⟩ := List.exists_mem_of_ne_nil _ hF
  have hlen : L.length = 0 := Nat.eq_zero_of_le_zero (hm ▸ F.length_le_maxAtoms hL)
  have hnil := List.length_eq_zero_iff.mp hlen
  ext x
  simp only [Set.mem_univ, iff_true]
  exact ⟨L, hL, by simp [clauseHolds, hnil]⟩

/-- Replace zero-atom templates by the canonical empty/universal description.
The counts are then separately bounded by c+1, without assuming c>0. -/
theorem HasFormat.exists_bounded_counts {n c D : ℕ} {F : PolynomialSignDNF n}
    (hF : F.HasFormat c D) :
    ∃ G : PolynomialSignDNF n, G.source = F.source ∧
      G.clauses.length ≤ c + 1 ∧
      (∀ L ∈ G.clauses, L.length ≤ c + 1) ∧
      (∀ L ∈ G.clauses, ∀ A ∈ L, A.polynomial.totalDegree ≤ D) := by
  by_cases hz : F.maxAtoms = 0
  · by_cases he : F.clauses = []
    · refine ⟨empty n, ?_, by simp [empty], by simp [empty], by simp [empty]⟩
      simp [source, empty, he]
    · refine ⟨univ n, ?_, by simp [univ], ?_, ?_⟩
      · rw [source_univ, F.source_eq_univ_of_maxAtoms_eq_zero he hz]
      · simp [univ]
      · simp [univ]
  · refine ⟨F, rfl, ?_, ?_, hF.2⟩
    · have := hF.1
      have : 1 ≤ F.maxAtoms := Nat.one_le_iff_ne_zero.mpr hz
      nlinarith
    · intro L hL
      have hr : 1 ≤ F.clauses.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hL)
      have := hF.1
      have := F.length_le_maxAtoms hL
      nlinarith

end PolynomialSignDNF

/-- An absent clause is false; an absent atom in a present clause is true. -/
abbrev PolynomialFormatTemplate (r b : ℕ) :=
  Fin r → Option (Fin b → Option PolynomialSign)

def PolynomialFormatTemplate.source {n D r b : ℕ} (T : PolynomialFormatTemplate r b)
    (c : Fin r → Fin b → PolynomialCoefficients n D) : Set (RealEuclidean n) :=
  {x | ∃ i A, T i = some A ∧ ∀ j s, A j = some s → s.Holds ((c i j).evaluate x)}

/-- The finite coefficient parameter space for one template. -/
abbrev PolynomialFormatCoefficients (n D r b : ℕ) :=
  Fin r → Fin b → PolynomialCoefficients n D

/-- Each polynomial is either zero or has unit coefficient norm. -/
def NormalizedFormatCoefficients {n D r b : ℕ} (c : PolynomialFormatCoefficients n D r b) : Prop :=
  ∀ i j, c i j = 0 ∨ ‖c i j‖ = 1

theorem isCompact_normalizedFormatCoefficients (n D r b : ℕ) :
    IsCompact {c : PolynomialFormatCoefficients n D r b | NormalizedFormatCoefficients c} := by
  have h : IsCompact {c : PolynomialCoefficients n D | c = 0 ∨ ‖c‖ = 1} :=
    isCompact_singleton.union PolynomialCoefficients.isCompact_unitSphere
  simpa only [NormalizedFormatCoefficients, Set.pi, Set.mem_univ, forall_true_left,
    Set.mem_ofPred_eq] using
    isCompact_univ_pi (fun _ : Fin r => isCompact_univ_pi (fun _ : Fin b => h))

namespace PolynomialSignDNF

/-- Embed a finite list description into fixed slots by marking padding absent. -/
def template {n : ℕ} (F : PolynomialSignDNF n) (r b : ℕ) : PolynomialFormatTemplate r b :=
  fun i => (F.clauses[i.val]?).map fun L j => (L[j.val]?).map (fun A => A.sign)

noncomputable def coefficients {n : ℕ} (F : PolynomialSignDNF n) (D r b : ℕ) :
    PolynomialFormatCoefficients n D r b :=
  fun i j => (((F.clauses[i.val]?).bind fun L => L[j.val]?).map
    fun A => PolynomialCoefficients.ofPolynomial A.polynomial).getD 0

theorem coefficients_eq_of_slots {n D r b : ℕ} (F : PolynomialSignDNF n)
    (i : Fin r) (j : Fin b) {L : List (PolynomialSignAtom n)} {A : PolynomialSignAtom n}
    (hi : F.clauses[i.val]? = some L) (hj : L[j.val]? = some A) :
    F.coefficients D r b i j = PolynomialCoefficients.ofPolynomial A.polynomial := by
  simp [coefficients, hi, hj]

/-- The finite slots give exactly the original source if their counts and
degree cap contain every clause and atom. -/
theorem source_template {n D r b : ℕ} (F : PolynomialSignDNF n)
    (hr : F.clauses.length ≤ r) (hb : ∀ L ∈ F.clauses, L.length ≤ b)
    (hD : ∀ L ∈ F.clauses, ∀ A ∈ L, A.polynomial.totalDegree ≤ D) :
    (F.template r b).source (F.coefficients D r b) = F.source := by
  classical
  have heval (i : Fin r) (j : Fin b) {L : List (PolynomialSignAtom n)}
      {A : PolynomialSignAtom n} (hi : F.clauses[i.val]? = some L)
      (hj : L[j.val]? = some A) (x : RealEuclidean n) :
      (F.coefficients D r b i j).evaluate x = MvPolynomial.eval (fun k => x k) A.polynomial := by
    rw [F.coefficients_eq_of_slots i j hi hj, PolynomialCoefficients.evaluate,
      PolynomialCoefficients.polynomial_ofPolynomial _
        (hD L (List.mem_of_getElem? hi) A (List.mem_of_getElem? hj))]
  ext x
  constructor
  · rintro ⟨i, B, hi, hx⟩
    obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hi
    refine ⟨L, List.mem_of_getElem? hL, ?_⟩
    intro A hA
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hA
    have hjlt := (List.getElem?_eq_some_iff.mp hj).choose
    let j' : Fin b := ⟨j, hjlt.trans_le (hb L (List.mem_of_getElem? hL))⟩
    have ha := hx j' A.sign (by simp [j', hj])
    simpa only [heval i j' hL hj x, PolynomialSignAtom.Holds] using ha
  · rintro ⟨L, hL, hx⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hL
    have hilt := (List.getElem?_eq_some_iff.mp hi).choose
    let i' : Fin r := ⟨i, hilt.trans_le hr⟩
    refine ⟨i', fun j => (L[j.val]?).map (fun A => A.sign), by simp [template, i', hi], ?_⟩
    intro j s hs
    obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp hs
    have ha := hx A (List.mem_of_getElem? hA)
    simpa only [heval i' j hi hA x, PolynomialSignAtom.Holds] using ha

end PolynomialSignDNF

theorem PolynomialCoefficients.sign_normalize_all {n D : ℕ} (s : PolynomialSign)
    (c : PolynomialCoefficients n D) (x : RealEuclidean n) :
    s.Holds (c.normalize.evaluate x) ↔ s.Holds (c.evaluate x) := by
  by_cases hc : c = 0
  · simp [hc]
  · exact PolynomialCoefficients.sign_normalize s hc x

theorem PolynomialFormatTemplate.source_normalize {n D r b : ℕ}
    (T : PolynomialFormatTemplate r b) (c : PolynomialFormatCoefficients n D r b) :
    T.source (fun i j => (c i j).normalize) = T.source c := by
  ext x
  simp only [source, Set.mem_ofPred_eq, PolynomialCoefficients.sign_normalize_all]

/-- Every bounded-format set has a fixed finite template with zero-or-unit
coefficient vectors. All normalizations preserve the evaluated source. -/
theorem HasSemialgebraicFormat.exists_normalized_parameters {n c D : ℕ}
    {S : Set (RealEuclidean n)} (h : HasSemialgebraicFormat S c D) :
    ∃ T : PolynomialFormatTemplate (c + 1) (c + 1),
      ∃ a : PolynomialFormatCoefficients n D (c + 1) (c + 1),
        NormalizedFormatCoefficients a ∧ T.source a = S := by
  obtain ⟨F, rfl, hF⟩ := h
  obtain ⟨G, hG, hr, hb, hD⟩ := hF.exists_bounded_counts
  let a := G.coefficients D (c + 1) (c + 1)
  refine ⟨G.template (c + 1) (c + 1), fun i j => (a i j).normalize, ?_, ?_⟩
  · intro i j
    by_cases hz : a i j = 0
    · exact Or.inl (by simp [hz])
    · exact Or.inr (PolynomialCoefficients.norm_normalize hz)
  · rw [PolynomialFormatTemplate.source_normalize, G.source_template hr hb hD, hG]

/-- A sequence of bounded-format sets has a subsequence with one fixed sign
template and convergent zero-or-unit coefficient vectors. The sequence index
is arbitrary; no definability in that index is required. -/
theorem exists_convergent_format_subsequence {n c D : ℕ}
    (S : ℕ → Set (RealEuclidean n)) (hS : ∀ j, HasSemialgebraicFormat (S j) c D) :
    ∃ T : PolynomialFormatTemplate (c + 1) (c + 1),
      ∃ a : ℕ → PolynomialFormatCoefficients n D (c + 1) (c + 1),
        ∃ aLimit : PolynomialFormatCoefficients n D (c + 1) (c + 1),
          ∃ k : ℕ → ℕ, StrictMono k ∧
            (∀ j, NormalizedFormatCoefficients (a j)) ∧
            (∀ j, T.source (a j) = S (k j)) ∧
            NormalizedFormatCoefficients aLimit ∧ Filter.Tendsto a Filter.atTop (nhds aLimit) := by
  classical
  choose T a ha hTa using fun j => (hS j).exists_normalized_parameters
  have hf : ∃ᶠ j in Filter.atTop, ∃ t : PolynomialFormatTemplate (c + 1) (c + 1), T j = t :=
    (Filter.Eventually.of_forall (fun j => ⟨T j, rfl⟩)).frequently
  obtain ⟨t, ht⟩ := Filter.frequently_exists.mp hf
  obtain ⟨k, hk, htk⟩ := Filter.extraction_of_frequently_atTop ht
  obtain ⟨aLimit, haLimit, l, hl, hlim⟩ :=
    (isCompact_normalizedFormatCoefficients n D (c + 1) (c + 1)).tendsto_subseq
      (fun j => ha (k j))
  refine ⟨t, fun j => a (k (l j)), aLimit, k ∘ l, hk.comp hl,
    fun j => ha (k (l j)), ?_, haLimit, hlim⟩
  intro j
  rw [← htk (l j)]
  exact hTa (k (l j))

end NLQCLean
end
