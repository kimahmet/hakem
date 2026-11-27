import Hakem
import CorpusTrees
import Solution.Lang

/-! Untrusted proofs: the corpus (kernel computation only). -/

namespace Proofs

set_option maxRecDepth 100000 in
theorem conservation_holds : Doc.HoldsTree conservation_tree :=
  checkTree_sound _ (by decide +kernel)

set_option maxRecDepth 100000 in
theorem policy_holds : Doc.HoldsTree policy_tree :=
  checkTree_sound _ (by decide +kernel)

end Proofs
