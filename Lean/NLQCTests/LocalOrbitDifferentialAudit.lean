import NLQCLean.Invariants.LocalOrbitDifferential

/-! Full statements and standard-axiom checks for local-orbit scalar derivatives. -/

set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000

#check @NLQCLean.matrixExp_smul_mem_unitary
#check @NLQCLean.hasDerivAt_matrixExp_smul_zero
#check @NLQCLean.localUnitaryOrbitCurve
#check @NLQCLean.localUnitaryOrbitCurve_zero
#check @NLQCLean.localUnitaryOrbitCurve_mem
#check @NLQCLean.hasDerivAt_localUnitaryOrbitCurve_zero
#check @NLQCLean.fderiv_eq_zero_of_localSkew

set_option pp.universes false

/-- info: 'NLQCLean.matrixExp_smul_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.matrixExp_smul_mem_unitary

/-- info: 'NLQCLean.hasDerivAt_localUnitaryOrbitCurve_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.hasDerivAt_localUnitaryOrbitCurve_zero

/-- info: 'NLQCLean.fderiv_eq_zero_of_localSkew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.fderiv_eq_zero_of_localSkew

open NLQCLean
open scoped Matrix.Norms.Frobenius

universe u v

example {ιA : Type u} {ιB : Type v}
    [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]
    (f : Matrix (ιA × ιB) (ιA × ιB) ℂ → ℝ)
    {U a b : Matrix (ιA × ιB) (ιA × ιB) ℂ}
    (hdiff : DifferentiableAt ℝ f U)
    (hinv : ∀ V ∈ unitaryDoubleOrbit ιA ιB U, f V = f U)
    (ha : a ∈ localSkew ιA ιB) (hb : b ∈ localSkew ιA ιB) :
    fderiv ℝ f U (b * U + U * a) = 0 :=
  fderiv_eq_zero_of_localSkew f hdiff hinv ha hb
