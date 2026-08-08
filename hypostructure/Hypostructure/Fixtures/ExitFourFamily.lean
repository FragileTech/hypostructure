import Hypostructure.Graph.ExitFourFamily

/-!
# Fixture: structural metadata of the pre-route exit-`(4)` family

This fixture checks only the paper-defined Q1--Q4 family metadata.  It makes no
target-defect, peeling, or response-realization claim: those require the
coordinate-specific compatible-context semantics that are not yet formalized.
-/

namespace Hypostructure.Fixtures.ExitFourFamily

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.ExitFour

universe u

variable {Target : FiniteObject.{u} → Prop} {object : FiniteObject.{u}}
variable {support : Finset object.Vertex} {threshold : Nat}
variable {receiver : object.Vertex} {Carrier : Type u}
variable (family : ReceiverFamily Target support threshold receiver Carrier)

attribute [local instance] vertexDecEq

example {clause : ReceiverClause}
    {base identified : Finset family.entry.Coordinate}
    (generated : family.Generated clause base identified) :
    base ⊆ family.entry.coordinates ∧ identified ⊆ base :=
  ⟨family.generated_base generated, family.generated_identified generated⟩

example {load : object.Vertex}
    {identified : Finset family.entry.Coordinate} :
    load ∈ family.declaredLoads identified ↔
      load ∈ object.routedLoads support threshold receiver ∧
        family.coordinate load ∈ identified :=
  family.mem_declaredLoads

example {load : object.Vertex}
    (routed : load ∈ object.routedLoads support threshold receiver) :
    family.coordinate load ∈ family.entry.coordinates :=
  family.coordinate_declared load routed

end Hypostructure.Fixtures.ExitFourFamily
