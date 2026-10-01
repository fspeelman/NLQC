import NLQCLean.Invariants.PurityReindex

/-! Full statements and axioms of finite local basis invariance. -/

set_option pp.deepTerms true

set_option pp.universes true in
#check @NLQCLean.trace_submatrix_equiv
#print axioms NLQCLean.trace_submatrix_equiv

set_option pp.universes true in
#check @NLQCLean.realign_submatrix_prodCongr
#print axioms NLQCLean.realign_submatrix_prodCongr

set_option pp.universes true in
#check @NLQCLean.purity_reindex_equiv
/-- info: 'NLQCLean.purity_reindex_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.purity_reindex_equiv
