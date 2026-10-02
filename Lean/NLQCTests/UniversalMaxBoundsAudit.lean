import NLQCLean.Bounds.UniversalMaxBounds

/-! # Universal floor and precision maximum audit -/

set_option pp.all true in
#check @NLQCLean.exists_strongUniversalMaxResourceBound
set_option pp.all true in
#check @NLQCLean.exists_strongUniversalMaxDiamondResourceBound
#print axioms NLQCLean.exists_strongUniversalMaxResourceBound_of_imageVolumeBound
#print axioms NLQCLean.exists_strongUniversalMaxResourceBound
#print axioms NLQCLean.exists_strongUniversalMaxDiamondResourceBound
