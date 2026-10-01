import NLQCLean.Models.ForwardCompression
import NLQCLean.Bounds.PVMQualitativeGap

/-!
# Support-charge preservation audit

Both types retain the architecture's resource-support charge and both message
dimensions while quantifying all original finite registers independently.
The pre-existing representative contracts are still checked by their callers.
-/

set_option pp.deepTerms true
set_option format.width 120

namespace NLQCTests

open NLQCLean

#check @PureProtocol.exists_bounded_support_charged_fin_representative
#check @PureProtocol.exists_bounded_support_charged_fin_pvm_representative

/-- info: 'NLQCLean.PureProtocol.exists_bounded_support_charged_fin_representative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PureProtocol.exists_bounded_support_charged_fin_representative

/-- info: 'NLQCLean.PureProtocol.exists_bounded_support_charged_fin_pvm_representative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PureProtocol.exists_bounded_support_charged_fin_pvm_representative

end NLQCTests
