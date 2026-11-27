import Hakem
import Corpus
import Solution.Lang

/-! Güvenilmeyen ispatlar: külliyat (yalnızca çekirdek hesabı). -/

namespace Proofs

set_option maxRecDepth 100000 in
theorem korunum_holds : Doc.HoldsTree korunum_tree :=
  checkTree_sound _ (by decide +kernel)

set_option maxRecDepth 100000 in
theorem politika_holds : Doc.HoldsTree politika_tree :=
  checkTree_sound _ (by decide +kernel)

end Proofs
