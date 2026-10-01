import NLQCLean.Bounds.UniversalMaxBounds

/-! # Universal floor and precision maximum audit -/

set_option pp.all true in
#check @NLQCLean.exists_strongUniversalMaxResourceBound_of_external
set_option pp.all true in
#check @NLQCLean.exists_strongUniversalMaxDiamondResourceBound_of_external
#print axioms NLQCLean.exists_strongUniversalMaxResourceBound
#print axioms NLQCLean.exists_strongUniversalMaxResourceBound_of_external
#print axioms NLQCLean.exists_strongUniversalMaxDiamondResourceBound_of_external
