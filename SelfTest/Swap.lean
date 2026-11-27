import Hakem
/-! BAD SOLUTION: does not import the trusted corpus; defines an empty document tree under the
same name. The statement term looks identical. Expected: meaning base differs. -/
def conservation_tree : List SExp := [.list [.atom "hakem", .atom "1"]]
theorem conservation_holds : Doc.HoldsTree conservation_tree := ⟨[], rfl, fun _ h => absurd h List.not_mem_nil⟩
