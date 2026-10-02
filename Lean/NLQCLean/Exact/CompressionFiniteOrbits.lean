import NLQCLean.Exact.RigidityStatements
import NLQCLean.Models.ForwardCompression

/-!
# Fixing the resource rank and message dimensions (`rem:compression`)

Every exact protocol can be compressed, with the same channel, so that its
resource registers have the Schmidt rank `r` of the shared state, the kept
registers have dimension at most `d r m`, and the garbage registers at most
`d² r m_A m_B` (`app:compression`). Hence the unitaries implementable with
Schmidt rank at most `r` and messages of dimensions `m_A, m_B` lie in
finitely many architectures, and form a finite union of full local-unitary
orbits.
-/

noncomputable section

namespace NLQCLean

open Matrix

variable {d : ℕ}

/-- A protocol of one architecture performing `U` exactly places `U` in that
architecture's exact targets. -/
theorem PureProtocol.mem_exactTargets [NeZero d] (s : ForwardShape)
    (P : PureProtocol (Fin d) (Fin d) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
      (Fin (s 4)) (Fin (s 5)) (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7)))
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hU : UnitaryTarget U)
    (htask : P.PerformsUnitary U) : U ∈ exactTargets d s := by
  obtain ⟨γ, hγ, hF⟩ := (P.performsUnitary_iff_frozen hU).mp htask
  refine ⟨(U, (P.resource, γ, P.encA, P.encB, P.decA, P.decB)), ⟨⟨P.resource_unit,
    P.encA_isometry, P.encB_isometry, P.decA_isometry, P.decB_isometry⟩, hγ,
    hU.self_mul_conjTranspose, hF⟩, rfl⟩

/-- **`app:compression`.** Every exact protocol has an exactly equivalent
protocol whose resource registers have dimension the Schmidt rank `r` of the
shared state, whose kept registers have dimensions at most `d r m_A` and
`d r m_B`, and whose garbage registers have dimensions at most `d² r m_A m_B`;
the message registers are unchanged. -/
theorem PureProtocol.exists_compressed_forward_bounds {ρA ρB κA κB μA μB εA εB : Type*}
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB) :
    ∃ r kA kB eA eB : ℕ, r = schmidtRank P.resource ∧
      kA ≤ d * r * Fintype.card μA ∧ kB ≤ d * r * Fintype.card μB ∧
      eA ≤ d ^ 2 * r * Fintype.card μA * Fintype.card μB ∧
      eB ≤ d ^ 2 * r * Fintype.card μA * Fintype.card μB ∧
      ∃ Q : PureProtocol (Fin d) (Fin d) (Fin r) (Fin r) (Fin kA) (Fin kB)
        μA μB (Fin d) (Fin d) (Fin eA) (Fin eB),
        P.operationalChannel = Q.operationalChannel := by
  obtain ⟨r, kA, kB, eA, eB, hr, hkA, hkB, heA, heB, Q, hQ⟩ := P.exists_compressed_forward
  refine ⟨r, kA, kB, eA, eB, hr, hkA, hkB, ?_, ?_, Q, hQ⟩
  · calc eA ≤ d * kA * Fintype.card μB := heA
      _ ≤ d * (d * r * Fintype.card μA) * Fintype.card μB := by gcongr
      _ = d ^ 2 * r * Fintype.card μA * Fintype.card μB := by ring
  · calc eB ≤ d * kB * Fintype.card μA := heB
      _ ≤ d * (d * r * Fintype.card μB) * Fintype.card μA := by gcongr
      _ = d ^ 2 * r * Fintype.card μA * Fintype.card μB := by ring

/-- Unitaries exactly implementable with resource Schmidt rank at most `r` and
message dimensions `m_A, m_B` (other registers of any finite dimension). -/
def exactUnitaryFixedRank (d r mA mB : ℕ) : Set (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  {U | UnitaryTarget U ∧ ∃ s : ForwardShape, s 4 = mA ∧ s 5 = mB ∧
    ∃ P : PureProtocol (Fin d) (Fin d) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
      (Fin (s 4)) (Fin (s 5)) (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7)),
      schmidtRank P.resource ≤ r ∧ P.PerformsUnitary U}

/-- The finitely many architectures reached after compression. -/
def compressedShapes (d r mA mB : ℕ) : Set ForwardShape :=
  {s | s 0 ≤ r ∧ s 1 ≤ r ∧ s 2 ≤ d * r * mA ∧ s 3 ≤ d * r * mB ∧ s 4 = mA ∧ s 5 = mB ∧
    s 6 ≤ d ^ 2 * r * mA * mB ∧ s 7 ≤ d ^ 2 * r * mA * mB}

theorem finite_compressedShapes (d r mA mB : ℕ) : (compressedShapes d r mA mB).Finite := by
  let M := r + d * r * mA + d * r * mB + mA + mB + d ^ 2 * r * mA * mB
  refine (Set.Finite.pi (t := fun _ : Fin 8 => Set.Iic M) fun _ => Set.finite_Iic M).subset ?_
  rintro s ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ i -
  simp only [Set.mem_Iic, M]
  fin_cases i <;> simp <;> omega

theorem exactUnitaryFixedRank_eq_iUnion [NeZero d] (r mA mB : ℕ) :
    exactUnitaryFixedRank d r mA mB = ⋃ s ∈ compressedShapes d r mA mB, exactTargets d s := by
  ext U
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hU, s, hs4, hs5, P, hrank, hP⟩
    obtain ⟨r', kA, kB, eA, eB, hr', hkA, hkB, heA, heB, Q, hQ⟩ :=
      P.exists_compressed_forward_bounds
    simp only [Fintype.card_fin, hs4, hs5] at hkA hkB heA heB
    have hr'r : r' ≤ r := hr' ▸ hrank
    let s' : ForwardShape := ![r', r', kA, kB, s 4, s 5, eA, eB]
    have hQ' : Q.PerformsUnitary U := by
      change Q.operationalChannel = adConj U
      rw [← hQ]
      exact hP
    refine ⟨s', ?_, PureProtocol.mem_exactTargets s' Q hU hQ'⟩
    refine ⟨hr'r, hr'r, ?_, ?_, hs4, hs5, ?_, ?_⟩
    · exact hkA.trans (by gcongr)
    · exact hkB.trans (by gcongr)
    · exact heA.trans (by gcongr)
    · exact heB.trans (by gcongr)
  · rintro ⟨s, ⟨h0, -, -, -, h4, h5, -, -⟩, z, hz, rfl⟩
    refine ⟨unitaryTarget_of_mem_exactTargets ⟨z, hz, rfl⟩, s, h4, h5,
      targetExactWitnessProtocol s hz, ?_, targetExactWitnessProtocol_performsUnitary s hz⟩
    exact (schmidtRank_le_card_left _).trans (by simpa using h0)

/-- **`rem:compression`.** For fixed `d`, Schmidt rank bound `r` and message
dimensions `m_A, m_B`, the exactly implementable unitaries are a finite union
of full local-unitary orbits of implementable unitaries, whatever the kept and
garbage dimensions. -/
theorem exists_finset_exactUnitaryFixedRank_eq_iUnion_orbits [NeZero d] (r mA mB : ℕ) :
    ∃ R : Finset (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      (∀ U ∈ R, U ∈ exactUnitaryFixedRank d r mA mB) ∧
        exactUnitaryFixedRank d r mA mB = ⋃ U ∈ R, unitaryDoubleOrbit (Fin d) (Fin d) U := by
  classical
  choose R hR hReq using fun s => exists_finset_exactTargets_eq_iUnion_orbits d s
  let B := (finite_compressedShapes d r mA mB).toFinset
  refine ⟨B.biUnion R, fun U hU => ?_, ?_⟩
  · obtain ⟨s, hs, hUs⟩ := Finset.mem_biUnion.mp hU
    rw [exactUnitaryFixedRank_eq_iUnion]
    exact Set.mem_biUnion ((finite_compressedShapes d r mA mB).mem_toFinset.mp hs) (hR s U hUs)
  · rw [exactUnitaryFixedRank_eq_iUnion]
    ext V
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_biUnion, B,
      Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨s, hs, hV⟩
      rw [hReq s] at hV
      simp only [Set.mem_iUnion, exists_prop] at hV
      obtain ⟨U, hU, hVU⟩ := hV
      exact ⟨U, ⟨s, hs, hU⟩, hVU⟩
    · rintro ⟨U, ⟨s, hs, hU⟩, hVU⟩
      refine ⟨s, hs, ?_⟩
      rw [hReq s]
      exact Set.mem_biUnion hU hVU

end NLQCLean
