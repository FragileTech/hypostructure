import Hypostructure.Fixtures.OfficialCallbackFreeBoundary

namespace Hypostructure.Fixtures.OfficialCallbackFreeBoundaryAudit

open Core.Strategy.Official
open Core.Strategy.OfficialRegistry

/-- Availability exposes only the bounded-slot proposition. -/
example (definition : ProblemDefinition) (ref : StrategyRef) :
    Available definition ref ↔
      ref.slot < slotCount definition.schema ref.id :=
  available_iff definition ref

/-- Neither a slot nor an availability witness can replace framework
ownership of an official identifier. -/
example (definition : ProblemDefinition) (ref : StrategyRef)
    (available : Available definition ref) :
    (describe ref.id).owner = (describe { ref with slot := 0 }.id).owner :=
  available_owner_fixed definition ref available

#print axioms Hypostructure.Core.Strategy.Official.available_iff
#print axioms Hypostructure.Core.Strategy.Official.available_owner_fixed

end Hypostructure.Fixtures.OfficialCallbackFreeBoundaryAudit
