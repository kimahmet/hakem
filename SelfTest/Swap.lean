import Hakem
/-! KÖTÜ ÇÖZÜM: güvenilen külliyatı içe aktarmaz; aynı adla boş bir belge ağacı tanımlar.
İfade terimi aynı görünür. Beklenen: anlam tabanı farklı. -/
def korunum_tree : List SExp := [.list [.atom "hakem", .atom "1"]]
theorem korunum_holds : Doc.HoldsTree korunum_tree := ⟨[], rfl, fun _ h => absurd h List.not_mem_nil⟩
