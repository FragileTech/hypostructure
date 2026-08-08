import Hypostructure.Graph.TypeAVisibleQ1Pair

namespace Hypostructure.Graph

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

attribute [local instance] vertexDecEq

namespace VisibleEntry

/-- The receiver-entry response datum `(e, x_g, g(Gamma), Q)` on the
canonical cut interface of its Type A support. -/
structure ResponseCoordinate (object : FiniteObject.{u})
    (support : Finset object.Vertex) (receiver : object.Vertex) where
  outside : object.Vertex
  port : outside ∈ completionPorts object support receiver
  entry :
    Strategy.InterfaceReplacement.SupportAtom.BoundaryVertex object support
  connector : object.graph.Walk outside entry.1
  connectorOutside : ∀ vertex ∈ connector.support, vertex ≠ entry.1 →
    vertex ∉ support
  channel : object.graph.Walk entry.1 receiver
  isChannel : IsChannel object support channel

namespace ResponseCoordinate

variable {support : Finset object.Vertex} {receiver : object.Vertex}

/-- The manuscript label `g(Gamma)`, derived from the retained connector. -/
def connectorLabel (coordinate : ResponseCoordinate object support receiver) : Nat :=
  coordinate.connector.length

/-- A receiver-entry coordinate is registered in the exact boundary-degree
fibre of the selected support.  This is coordinate metadata; it does not
construct a replacement realization. -/
noncomputable def registeredBoundaryDegreeProfile
    (_coordinate : ResponseCoordinate object support receiver) :
    BoundaryDegreeProfile
      (Strategy.InterfaceReplacement.SupportAtom.boundary object support) :=
  (Strategy.InterfaceReplacement.SupportAtom.piece object support).boundaryDegreeProfile

theorem registeredBoundaryDegreeProfile_eq
    (left right : ResponseCoordinate object support receiver) :
    left.registeredBoundaryDegreeProfile =
      right.registeredBoundaryDegreeProfile := by
  rfl

end ResponseCoordinate
end VisibleEntry

namespace ExitFour

namespace VisibleFourUnpeeledPackage

variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {peeled : Finset object.Vertex}

/-- The paper coordinate of one canonically selected visible return. -/
noncomputable def selectedResponseCoordinate
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    VisibleEntry.ResponseCoordinate object support receiver where
  outside := package.outside
  port := package.port
  entry := package.selectedD1Coordinate load.1 load.2
  connector := (package.selectedReturn load.1 load.2).connector
  connectorOutside := (package.selectedReturn load.1 load.2).connectorOutside
  channel := (package.selectedReturn load.1 load.2).channel
  isChannel := (package.selectedReturn load.1 load.2).isChannel

@[simp] theorem selectedResponseCoordinate_outside
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    (package.selectedResponseCoordinate load).outside = package.outside := by
  rfl

@[simp] theorem selectedResponseCoordinate_entry
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    (package.selectedResponseCoordinate load).entry.1 =
      (package.selectedReturn load.1 load.2).entry := by
  rfl

/-- `g(Gamma)` is exactly the connector length from
`def:typeA-channel-spectrum`. -/
@[simp] theorem selectedResponseCoordinate_connectorLabel
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    (package.selectedResponseCoordinate load).connectorLabel =
      (package.selectedReturn load.1 load.2).connector.length := by
  rfl

@[simp] theorem selectedResponseCoordinate_connector
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    (package.selectedResponseCoordinate load).connector =
      (package.selectedReturn load.1 load.2).connector := by
  rfl

@[simp] theorem selectedResponseCoordinate_channel
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    (package.selectedResponseCoordinate load).channel =
      (package.selectedReturn load.1 load.2).channel := by
  rfl

/-- The coordinate retains the manuscript's ownership split: the connector is
outside the selected support before its entry, and the channel is a path inside
the support. -/
theorem selectedResponseCoordinate_ownership
    (package : VisibleFourUnpeeledPackage support threshold scale receiver peeled)
    (load : package.SelectedLoad) :
    (∀ vertex ∈ (package.selectedReturn load.1 load.2).connector.support,
      vertex ≠ (package.selectedResponseCoordinate load).entry.1 →
        vertex ∉ support) ∧
      VisibleEntry.IsChannel object support
        (package.selectedResponseCoordinate load).channel := by
  let return' := package.selectedReturn load.1 load.2
  change (∀ vertex ∈ return'.connector.support,
      vertex ≠ return'.entry → vertex ∉ support) ∧
    VisibleEntry.IsChannel object support return'.channel
  exact ⟨return'.connectorOutside, return'.isChannel⟩

namespace Q1OriginPair

variable
    {package : VisibleFourUnpeeledPackage support threshold scale receiver peeled}
    (pair : package.Q1OriginPair)

noncomputable def leftResponseCoordinate :
    VisibleEntry.ResponseCoordinate object support receiver :=
  package.selectedResponseCoordinate pair.left

noncomputable def rightResponseCoordinate :
    VisibleEntry.ResponseCoordinate object support receiver :=
  package.selectedResponseCoordinate pair.right

@[simp] theorem leftResponseCoordinate_connectorLabel :
    pair.leftResponseCoordinate.connectorLabel =
      pair.leftReturn.connector.length := by
  rfl

@[simp] theorem rightResponseCoordinate_connectorLabel :
    pair.rightResponseCoordinate.connectorLabel =
      pair.rightReturn.connector.length := by
  rfl

/-- Both selected coordinates are entries of the same exact-profile boundary
fibre.  No realization or target-completeness claim is made here. -/
theorem responseCoordinates_same_registered_fibre :
    pair.leftResponseCoordinate.registeredBoundaryDegreeProfile =
      pair.rightResponseCoordinate.registeredBoundaryDegreeProfile :=
  VisibleEntry.ResponseCoordinate.registeredBoundaryDegreeProfile_eq _ _

end Q1OriginPair
end VisibleFourUnpeeledPackage

end ExitFour
end Hypostructure.Graph
