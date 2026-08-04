import Hypostructure.Core.Strategy.OfficialRegistry

/-!
# Callback-free official source declarations

These declarations are deliberately inert.  They describe which typed problem
data slots exist and which closed framework strategies a DAG requests.  They
contain no executor, result, proof, transition, or routing hook.
-/

namespace Hypostructure.Core.Strategy.Official

open OfficialRegistry

/-- Closed categories of data accepted by the official compiler boundary. -/
inductive SlotKind where
  | finiteSchedule
  | finiteTable
  | naturalBudget
  | integerBudget
  | relation
  | graphPresentation
  | representedPresentation
  deriving DecidableEq, Repr, Inhabited

/-- A source slot is only an identifier and a closed data category. -/
structure Slot where
  index : Nat
  kind : SlotKind
  deriving DecidableEq, Repr, Inhabited

/-- Literal source schema presented by a problem declaration. -/
structure Source where
  slots : List Slot
  deriving DecidableEq, Repr, Inhabited

/-- Literal official DAG references.  Execution is resolved privately from
`OfficialRegistry.Id`; this structure cannot carry an implementation. -/
structure ReferenceInventory where
  refs : List OfficialRegistry.Ref
  deriving DecidableEq, Repr, Inhabited

end Hypostructure.Core.Strategy.Official
