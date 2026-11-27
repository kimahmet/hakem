import Hakem
import Solution.Lang
import CorpusTrees
/-! BAD SOLUTION: checks the document with compiled code instead of the kernel (`native_decide`).
Expected: unpermitted axiom (trust in the compiler). -/
theorem conservation_holds : Doc.HoldsTree conservation_tree :=
  Proofs.checkTree_sound _ (by native_decide)
