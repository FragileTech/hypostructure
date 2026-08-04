import Hypostructure.Core.Strategy.Official.Strategies.Common

namespace Hypostructure.Core.Strategy.Official.Strategies.ClosedCodeExhaustion

def Repetitions (slot : FunctionTableSlot) :=
  slot.rows.product slot.rows |>.filter fun pair =>
    decide (pair.1.1 ≠ pair.2.1 ∧ pair.1.2 = pair.2.2)

/-- Exact whole-support codebook and every repeated-code witness. -/
structure Terminal (slot : FunctionTableSlot) where
  codebook : List (slot.left.Carrier × slot.right.Carrier)
  codebook_eq : codebook = slot.rows
  supportCovered : ∀ x, x ∈ codebook.map Prod.fst
  uniqueCode : ∀ {x y z}, (x, y) ∈ codebook → (x, z) ∈ codebook → y = z
  repetitions :
    List ((slot.left.Carrier × slot.right.Carrier) ×
      (slot.left.Carrier × slot.right.Carrier))
  repetitions_eq : repetitions = Repetitions slot
  work : Strategies.StaticWork (codebook.length * codebook.length)

def execute (slot : FunctionTableSlot) : Terminal slot :=
  { codebook := slot.rows
    codebook_eq := rfl
    supportCovered := fun x => Strategies.mem_map_fst (slot.total x)
    uniqueCode := slot.functional
    repetitions := Repetitions slot
    repetitions_eq := rfl
    work := Strategies.exactWork (slot.rows.length * slot.rows.length) }

end Hypostructure.Core.Strategy.Official.Strategies.ClosedCodeExhaustion
