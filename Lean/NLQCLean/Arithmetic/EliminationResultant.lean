import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# One elimination step by a Kronecker resultant

For `f, G₀, …, G_{s-1} ∈ B[X]` put `g = Σ uⁱ Gᵢ ∈ B[u][X]` and
`R = Res_X(f, g) ∈ B[u]` with formal degrees `m ≥ deg f` and `n ≥ deg Gᵢ`.

* If `f` and all `Gᵢ` have a common root `t` under a ring map `ψ : B → S`,
  every `u`-coefficient of `R` is killed by `ψ` (Bézout identity).
* Conversely, if `φ : B → L` into an algebraically closed field kills every
  `u`-coefficient of `R`, keeps the leading coefficient of `f` nonzero, and
  `m = deg f`, then `f` and all `Gᵢ` have a common root under `φ`.

This is the projection step of iterated-resultant elimination.
-/

namespace NLQCLean.Elimination

open Polynomial

variable {B : Type*} [CommRing B]

/-- The Kronecker combination `Σᵢ uⁱ Gᵢ`, a polynomial in `X` over `B[u]`. -/
noncomputable def kronecker {s : ℕ} (G : Fin s → B[X]) : (B[X])[X] :=
  ∑ i, (G i).map C * Polynomial.C (Polynomial.X ^ (i : ℕ))

/-- The eliminant `Res_X(f, Σᵢ uⁱ Gᵢ) ∈ B[u]`. -/
noncomputable def eliminant {s : ℕ} (f : B[X]) (G : Fin s → B[X]) (m n : ℕ) : B[X] :=
  resultant (f.map C) (kronecker G) m n

theorem natDegree_kronecker_le {s : ℕ} {G : Fin s → B[X]} {n : ℕ}
    (hG : ∀ i, (G i).natDegree ≤ n) : (kronecker G).natDegree ≤ n := by
  unfold kronecker
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine (natDegree_mul_le).trans ?_
  rw [natDegree_C, add_zero]
  exact natDegree_map_le.trans (hG i)

theorem mapRingHom_comp_C {L : Type*} [CommRing L] (φ : B →+* L) :
    (mapRingHom φ).comp (C : B →+* B[X]) = (C : L →+* L[X]).comp φ :=
  RingHom.ext fun b => by simp

theorem eval_map_map_C (p : B[X]) {L : Type*} [CommRing L] (φ : B →+* L) (t : L) :
    ((p.map C).map (mapRingHom φ)).eval (C t) = C (p.eval₂ φ t) := by
  rw [Polynomial.map_map, mapRingHom_comp_C, ← Polynomial.map_map, eval_map, eval₂_at_apply,
    eval_map]

/-- Common roots give vanishing `u`-coefficients of the eliminant. -/
theorem map_coeff_eliminant_eq_zero {s : ℕ} {f : B[X]} {G : Fin s → B[X]} {m n : ℕ}
    (hm : m ≠ 0) (hf : f.natDegree ≤ m) (hG : ∀ i, (G i).natDegree ≤ n)
    {S : Type*} [CommRing S] (ψ : B →+* S) {t : S}
    (hft : f.eval₂ ψ t = 0) (hGt : ∀ i, (G i).eval₂ ψ t = 0) (k : ℕ) :
    ψ ((eliminant f G m n).coeff k) = 0 := by
  obtain ⟨p, q, -, -, h⟩ := exists_mul_add_mul_eq_C_resultant (f.map C) (kronecker G)
    (natDegree_map_le.trans hf) (natDegree_kronecker_le hG) (Or.inl hm)
  let Θ : (B[X])[X] →+* S[X] := eval₂RingHom (mapRingHom ψ) (Polynomial.C t)
  have hΘf : Θ (f.map C) = 0 := by
    simp only [Θ, coe_eval₂RingHom, eval₂_map]
    rw [mapRingHom_comp_C, ← hom_eval₂, hft, map_zero]
  have hΘg : Θ (kronecker G) = 0 := by
    simp only [kronecker, map_sum, map_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi : Θ ((G i).map C) = 0 := by
      simp only [Θ, coe_eval₂RingHom, eval₂_map]
      rw [mapRingHom_comp_C, ← hom_eval₂, hGt i, map_zero]
    rw [hi, zero_mul]
  have hΘ := congrArg Θ h
  rw [map_add, map_mul, map_mul, hΘf, hΘg, zero_mul, zero_mul, add_zero] at hΘ
  have hR : (eliminant f G m n).map ψ = 0 := by
    have : Θ (Polynomial.C (eliminant f G m n)) = (eliminant f G m n).map ψ := by
      simp [Θ, eliminant]
    rw [← this, eliminant, ← hΘ]
  have := congrArg (fun p : S[X] => p.coeff k) hR
  simpa [coeff_map] using this

/-- Evaluating the mapped Kronecker combination at a constant. -/
theorem eval_map_kronecker {s : ℕ} (G : Fin s → B[X]) {L : Type*} [CommRing L] (φ : B →+* L)
    (t : L) : ((kronecker G).map (mapRingHom φ)).eval (C t) =
      ∑ i, C ((G i).eval₂ φ t) * X ^ (i : ℕ) := by
  simp only [kronecker, Polynomial.map_sum, Polynomial.map_mul, eval_finsetSum, eval_mul,
    eval_map_map_C, map_C, eval_C]
  simp

/-- Vanishing `u`-coefficients of the eliminant give a common root over an
algebraically closed field, when the leading coefficient of `f` survives. -/
theorem exists_common_root_of_eliminant {s : ℕ} {f : B[X]} {G : Fin s → B[X]} {n : ℕ}
    (hG : ∀ i, (G i).natDegree ≤ n)
    {L : Type*} [Field L] [IsAlgClosed L] (φ : B →+* L) (hlc : φ f.leadingCoeff ≠ 0)
    (hR : ∀ k, φ ((eliminant f G f.natDegree n).coeff k) = 0) :
    ∃ t : L, f.eval₂ φ t = 0 ∧ ∀ i, (G i).eval₂ φ t = 0 := by
  set fb : L[X] := f.map φ with hfb
  have hfbdeg : fb.natDegree = f.natDegree := natDegree_map_of_leadingCoeff_ne_zero φ hlc
  have hfblc : fb.leadingCoeff = φ f.leadingCoeff := leadingCoeff_map_of_leadingCoeff_ne_zero φ hlc
  set F : (L[X])[X] := fb.map C with hF
  have hCinj : Function.Injective (C : L →+* L[X]) := C_injective
  have hFdeg : F.natDegree = f.natDegree := by
    rw [hF, natDegree_map_eq_of_injective hCinj, hfbdeg]
  have hFlc : F.leadingCoeff = C (φ f.leadingCoeff) := by
    rw [hF, leadingCoeff_map_of_injective hCinj, hfblc]
  set g : (L[X])[X] := (kronecker G).map (mapRingHom φ) with hg
  have hgdeg : g.natDegree ≤ n := natDegree_map_le.trans (natDegree_kronecker_le hG)
  have hfbsplit : fb.Splits := IsAlgClosed.splits fb
  have hFsplit : F.Splits := hfbsplit.map C
  -- the eliminant maps to the resultant of the mapped polynomials
  have hres : resultant F g F.natDegree n = 0 := by
    have hmap : (eliminant f G f.natDegree n).map φ = 0 := by
      ext k
      simp [coeff_map, hR k]
    have hFeq : (f.map C).map (mapRingHom φ) = F := by
      rw [hF, hfb, Polynomial.map_map, Polynomial.map_map, mapRingHom_comp_C]
    rw [hFdeg, ← hFeq, hg, resultant_map_map]
    simpa [eliminant, coe_mapRingHom] using hmap
  rw [resultant_eq_prod_eval F g n hgdeg hFsplit, hFlc] at hres
  have hlcpow : (C (φ f.leadingCoeff)) ^ n ≠ 0 := pow_ne_zero _ (by simpa using hlc)
  have hprod := (mul_eq_zero.mp hres).resolve_left hlcpow
  obtain ⟨r, hr, hr0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod)
  have hroots : F.roots = fb.roots.map C := by
    rw [hF]
    exact (roots_map_of_injective_of_card_eq_natDegree hCinj
      (hfbsplit.natDegree_eq_card_roots).symm).symm
  rw [hroots, Multiset.mem_map] at hr
  obtain ⟨t, ht, rfl⟩ := hr
  refine ⟨t, ?_, fun i => ?_⟩
  · have := (mem_roots'.mp ht).2
    simpa [hfb, IsRoot, eval_map] using this
  · rw [hg, eval_map_kronecker] at hr0
    have hcoeff := congrArg (fun p : L[X] => p.coeff (i : ℕ)) hr0
    simpa [finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using hcoeff

end NLQCLean.Elimination
