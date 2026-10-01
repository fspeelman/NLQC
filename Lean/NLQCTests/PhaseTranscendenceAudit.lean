import NLQCLean.Arithmetic.PhaseTranscendence

/-! Full arithmetic statements and standard-axiom checks for phase transcendence. -/

set_option pp.universes true in
#check @NLQCLean.transcendental_exp_angle_int
set_option pp.universes true in
#check @NLQCLean.transcendental_exp_angle
set_option pp.universes true in
#check @NLQCLean.transcendental_exp_angle_of_isAlgebraic_int
set_option pp.universes true in
#check @NLQCLean.exp_angle_quadratic
set_option pp.universes true in
#check @NLQCLean.isAlgebraic_exp_angle_of_cos
set_option pp.universes true in
#check @NLQCLean.isAlgebraic_exp_angle_int_of_cos
set_option pp.universes true in
#check @NLQCLean.transcendental_cos_of_algebraic
set_option pp.universes true in
#check @NLQCLean.transcendental_cos_int_of_algebraic
set_option pp.universes true in
#check @NLQCLean.isAlgebraic_cos_of_phasePurityValue
set_option pp.universes true in
#check @NLQCLean.isAlgebraic_exp_angle_of_phasePurityValue
set_option pp.universes true in
#check @NLQCLean.transcendental_phasePurityValue
set_option pp.universes true in
#check @NLQCLean.transcendental_phasePurityValue_int
set_option pp.universes true in
#check @NLQCLean.transcendental_purity_controlledPhase
set_option pp.universes true in
#check @NLQCLean.transcendental_exp_I
set_option pp.universes true in
#check @NLQCLean.transcendental_exp_I_int
set_option pp.universes true in
#check @NLQCLean.transcendental_cos_one
set_option pp.universes true in
#check @NLQCLean.transcendental_cos_one_int
set_option pp.universes true in
#check @NLQCLean.transcendental_phasePurityValue_one
set_option pp.universes true in
#check @NLQCLean.transcendental_purity_controlledPhase_one

/-- info: 'NLQCLean.transcendental_exp_angle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.transcendental_exp_angle

/-- info: 'NLQCLean.isAlgebraic_exp_angle_of_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.isAlgebraic_exp_angle_of_cos

/-- info: 'NLQCLean.transcendental_cos_of_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.transcendental_cos_of_algebraic

/-- info: 'NLQCLean.transcendental_phasePurityValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.transcendental_phasePurityValue

/-- info: 'NLQCLean.transcendental_purity_controlledPhase_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.transcendental_purity_controlledPhase_one

example (θ : ℝ) (hθ0 : θ ≠ 0) (hθ : IsAlgebraic ℚ θ) :
    ¬ IsAlgebraic ℚ (Complex.exp ((θ : ℂ) * Complex.I)) ∧
      ¬ IsAlgebraic ℤ (Complex.exp ((θ : ℂ) * Complex.I)) ∧
      ¬ IsAlgebraic ℚ (Real.cos θ) ∧
      ¬ IsAlgebraic ℚ (NLQCLean.purity (1 / 16) (NLQCLean.controlledPhase θ)) :=
  ⟨NLQCLean.transcendental_exp_angle hθ0 hθ,
    NLQCLean.transcendental_exp_angle_int hθ0 hθ,
    NLQCLean.transcendental_cos_of_algebraic hθ0 hθ,
    NLQCLean.transcendental_purity_controlledPhase hθ0 hθ⟩

example : ¬ IsAlgebraic ℚ (Complex.exp Complex.I) ∧
    ¬ IsAlgebraic ℚ (Real.cos 1) ∧
    ¬ IsAlgebraic ℚ (NLQCLean.purity (1 / 16) (NLQCLean.controlledPhase 1)) :=
  ⟨NLQCLean.transcendental_exp_I,
    NLQCLean.transcendental_cos_one,
    NLQCLean.transcendental_purity_controlledPhase_one⟩
