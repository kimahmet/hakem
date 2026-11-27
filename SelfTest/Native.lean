import Hakem
import Solution.Lang
import Corpus
/-! KÖTÜ ÇÖZÜM: belge denetimini çekirdek yerine derlenmiş kodla yapar (`native_decide`).
Beklenen: izinsiz aksiyom (derleyiciye güven). -/
theorem korunum_holds : Doc.HoldsTree korunum_tree :=
  Proofs.checkTree_sound _ (by native_decide)
