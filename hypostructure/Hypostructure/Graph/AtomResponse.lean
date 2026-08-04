import Hypostructure.Graph.BoundariedAtom
import Hypostructure.Core.Residual.Query

/-!
# Arbitrary local response coordinates of one boundaried atom

The original graph argument permits any collection of local target-response
coordinates attached to a proper atom.  A coordinate need not itself be a
graph: it can encode a trace length, rooted-return test, curvature test, or
other marked response datum.  The only semantic data required here are its
registered boundary-degree fibre and its target realization against every
literal outside context.

Every coordinate system is indexed by the exact profile certificate generated
for the atom.  Membership in that fibre is therefore checked once when the
system is formed.  A target-complete quotient is an arbitrary certified setoid
whose identifications preserve the target response in every outside context.
Graph derives profile preservation, the canonical exact quotient, and the
context-universality projection.
-/

namespace Hypostructure.Graph.AtomResponse

open Hypostructure.Graph

universe u v

/-- An arbitrary collection of local response coordinates for one exact
proper atom.  `realize coordinate outside` is the global finite graph whose
target response that coordinate records in the supplied outside context. -/
structure CoordinateSystem {object : FiniteObject.{u}}
    {atom : ProperBoundariedAtom object}
    (certificate : BoundariedAtomProfileCertificate atom)
    (Target : FiniteObject.{u} -> Prop) where
  Coordinate : Type v
  boundaryDegreeProfile :
    Coordinate -> BoundaryDegreeProfile atom.decomposition.interface
  realize : Coordinate ->
    OutsideContext atom.decomposition.interface -> FiniteObject.{u}
  in_registered_fibre : forall coordinate,
    boundaryDegreeProfile coordinate = certificate.boundaryDegreeProfile

namespace CoordinateSystem

variable {object : FiniteObject.{u}}
variable {atom : ProperBoundariedAtom object}
variable {certificate : BoundariedAtomProfileCertificate atom}
variable {Target : FiniteObject.{u} -> Prop}

/-- Exact target response of one coordinate in one literal outside context. -/
def targetResponse (system : CoordinateSystem.{u, v} certificate Target)
    (coordinate : system.Coordinate)
    (outside : OutsideContext atom.decomposition.interface) : Prop :=
  Target (system.realize coordinate outside)

/-- Two arbitrary coordinates have the same target response against every
literal outside context. -/
def ContextEquivalent (system : CoordinateSystem.{u, v} certificate Target)
    (left right : system.Coordinate) : Prop :=
  forall outside : OutsideContext atom.decomposition.interface,
    system.targetResponse left outside <-> system.targetResponse right outside

/-- A system represented by same-boundary graph pieces is one specialization
of the arbitrary-coordinate API.  The caller proves once that each piece lies
in the atom's registered profile fibre. -/
noncomputable def ofPieces
    (Coordinate : Type v)
    (represented : Coordinate -> BoundaryPiece atom.decomposition.interface)
    (inRegisteredFibre : forall coordinate,
      (represented coordinate).boundaryDegreeProfile =
        certificate.boundaryDegreeProfile) :
    CoordinateSystem certificate Target where
  Coordinate := Coordinate
  boundaryDegreeProfile coordinate :=
    (represented coordinate).boundaryDegreeProfile
  realize coordinate outside := Graph.glue (represented coordinate) outside
  in_registered_fibre := inRegisteredFibre

@[simp] theorem targetResponse_ofPieces
    (Coordinate : Type v)
    (represented : Coordinate -> BoundaryPiece atom.decomposition.interface)
    (inRegisteredFibre : forall coordinate,
      (represented coordinate).boundaryDegreeProfile =
        certificate.boundaryDegreeProfile)
    (coordinate : Coordinate)
    (outside : OutsideContext atom.decomposition.interface) :
    (ofPieces (Target := Target) Coordinate represented
      inRegisteredFibre).targetResponse coordinate outside <->
        Target (Graph.glue (represented coordinate) outside) :=
  Iff.rfl

end CoordinateSystem

/-! A pair of response coordinates is the framework-owned representation of a
same-interface germ.  Its profile equality is derived from the coordinate
system's registered fibre; callers do not copy a second boundary profile into
the germ payload. -/
structure SameFibrePair
    {object : FiniteObject.{u}}
    {atom : ProperBoundariedAtom object}
    {certificate : BoundariedAtomProfileCertificate atom}
    {Target : FiniteObject.{u} -> Prop}
    (system : CoordinateSystem.{u, v} certificate Target) where
  left : system.Coordinate
  right : system.Coordinate

namespace SameFibrePair

variable {object : FiniteObject.{u}}
variable {atom : ProperBoundariedAtom object}
variable {certificate : BoundariedAtomProfileCertificate atom}
variable {Target : FiniteObject.{u} -> Prop}
variable {system : CoordinateSystem.{u, v} certificate Target}

def representatives (pair : SameFibrePair system) :
    Core.Response.Representatives system.Coordinate :=
  { source := pair.left, replacement := pair.right }

theorem profile_eq (pair : SameFibrePair system) :
    system.boundaryDegreeProfile pair.left =
      system.boundaryDegreeProfile pair.right := by
  exact (system.in_registered_fibre pair.left).trans
    (system.in_registered_fibre pair.right).symm

end SameFibrePair

/-- A quotient of an arbitrary coordinate collection is target-complete when
every identification preserves target response against every outside context.
Boundary-profile preservation is automatic because the collection was
registered in one exact Node-11 profile fibre. -/
structure TargetCompleteQuotient
    {object : FiniteObject.{u}}
    {atom : ProperBoundariedAtom object}
    {certificate : BoundariedAtomProfileCertificate atom}
    {Target : FiniteObject.{u} -> Prop}
    (system : CoordinateSystem.{u, v} certificate Target) where
  relation : Setoid system.Coordinate
  context_complete : forall {left right}, relation.r left right ->
    system.ContextEquivalent left right

namespace TargetCompleteQuotient

variable {object : FiniteObject.{u}}
variable {atom : ProperBoundariedAtom object}
variable {certificate : BoundariedAtomProfileCertificate atom}
variable {Target : FiniteObject.{u} -> Prop}
variable {system : CoordinateSystem.{u, v} certificate Target}

/-- The proof-relevant identification made by a certified quotient. -/
def Identified (quotient : TargetCompleteQuotient system)
    (left right : system.Coordinate) : Prop :=
  quotient.relation.r left right

/-- Actual quotient carrier generated by the certified equivalence relation. -/
abbrev Carrier (quotient : TargetCompleteQuotient system) : Type v :=
  Quotient quotient.relation

/-- Condition (a) of target completeness follows from the registered fibre
laws of the two coordinates. -/
theorem profile_preserved (quotient : TargetCompleteQuotient system)
    {left right : system.Coordinate}
    (_identified : quotient.Identified left right) :
    system.boundaryDegreeProfile left =
      system.boundaryDegreeProfile right :=
  (system.in_registered_fibre left).trans
    (system.in_registered_fibre right).symm

/-- Condition (b) of target completeness is exactly context universality. -/
theorem contextUniversal_of_identified
    (quotient : TargetCompleteQuotient system)
    {left right : system.Coordinate}
    (identified : quotient.Identified left right) :
    system.ContextEquivalent left right :=
  quotient.context_complete identified

/-! A certified quotient supplies the actual same-interface pair consumed by
later response or replacement strategies.  The pair carries no copied
profile or response fields; both are recovered from the quotient and the
registered coordinate fibre. -/
def pairOfIdentified
    (quotient : TargetCompleteQuotient system)
    {left right : system.Coordinate}
    (_identified : quotient.Identified left right) :
    SameFibrePair system :=
  { left := left, right := right }

theorem pairOfIdentified_profile_eq
    (quotient : TargetCompleteQuotient system)
    {left right : system.Coordinate}
    (identified : quotient.Identified left right) :
    system.boundaryDegreeProfile
        (quotient.pairOfIdentified identified).left =
      system.boundaryDegreeProfile
        (quotient.pairOfIdentified identified).right :=
  (quotient.pairOfIdentified identified).profile_eq

theorem pairOfIdentified_contextUniversal
    (quotient : TargetCompleteQuotient system)
    {left right : system.Coordinate}
    (identified : quotient.Identified left right) :
    system.ContextEquivalent
      (quotient.pairOfIdentified identified).left
      (quotient.pairOfIdentified identified).right :=
  quotient.contextUniversal_of_identified identified

end TargetCompleteQuotient

/-! Query-level construction for a same-interface pair.  All three inputs are
read from the same predecessor stage; the pair itself is reconstructed by the
existing quotient API, so no caller can inject a copied profile or response
certificate. -/
namespace QuerySurface

open Hypostructure.Core.Residual

universe uPrevious

variable {Previous : Sort uPrevious}
variable {object : FiniteObject.{u}}
variable {atom : ProperBoundariedAtom object}
variable {certificate : BoundariedAtomProfileCertificate atom}
variable {Target : FiniteObject.{u} -> Prop}
variable {system : CoordinateSystem.{u, v} certificate Target}

noncomputable def pairOfIdentified
    (quotient : Query Previous (fun _ => TargetCompleteQuotient system))
    (left : Query Previous (fun _ => system.Coordinate))
    (right : Query Previous (fun _ => system.Coordinate))
    (identified : Query Previous (fun previous =>
      (quotient.read previous).Identified
        (left.read previous) (right.read previous))) :
  Query Previous (fun previous => SameFibrePair system) :=
  Query.ofFunction fun previous =>
    (quotient.read previous).pairOfIdentified (identified.read previous)

def profileEquality
    (pairs : Query Previous (fun _ => SameFibrePair system)) :
    Query Previous (fun previous =>
      system.boundaryDegreeProfile (pairs.read previous).left =
        system.boundaryDegreeProfile (pairs.read previous).right) :=
  Query.ofFunction fun previous => (pairs.read previous).profile_eq

def contextUniversality
    (quotient : Query Previous (fun _ => TargetCompleteQuotient system))
    (left : Query Previous (fun _ => system.Coordinate))
    (right : Query Previous (fun _ => system.Coordinate))
    (identified : Query Previous (fun previous =>
      (quotient.read previous).Identified
        (left.read previous) (right.read previous))) :
    Query Previous (fun previous =>
      system.ContextEquivalent (left.read previous) (right.read previous)) :=
  Query.ofFunction fun previous =>
    (quotient.read previous).contextUniversal_of_identified
      (identified.read previous)

end QuerySurface

/-- A pair of coordinates is target-completely identified when some certified
target-complete quotient identifies it. -/
def TargetCompleteIdentification
    {object : FiniteObject.{u}}
    {atom : ProperBoundariedAtom object}
    {certificate : BoundariedAtomProfileCertificate atom}
    {Target : FiniteObject.{u} -> Prop}
    (system : CoordinateSystem.{u, v} certificate Target)
    (left right : system.Coordinate) : Prop :=
  Exists fun quotient : TargetCompleteQuotient system =>
    quotient.Identified left right

/-- A target-defective coordinate pair has one literal outside context whose
target response distinguishes the two coordinates. -/
def TargetDefect
    {object : FiniteObject.{u}}
    {atom : ProperBoundariedAtom object}
    {certificate : BoundariedAtomProfileCertificate atom}
    {Target : FiniteObject.{u} -> Prop}
    (system : CoordinateSystem.{u, v} certificate Target)
    (left right : system.Coordinate) : Prop :=
  exists outside : OutsideContext atom.decomposition.interface,
    Not (system.targetResponse left outside <->
      system.targetResponse right outside)

/-- Failure of all-context equivalence forbids every target-complete quotient
from identifying the two coordinates. -/
theorem not_targetCompleteIdentification_of_not_contextEquivalent
    {object : FiniteObject.{u}}
    {atom : ProperBoundariedAtom object}
    {certificate : BoundariedAtomProfileCertificate atom}
    {Target : FiniteObject.{u} -> Prop}
    {system : CoordinateSystem.{u, v} certificate Target}
    {left right : system.Coordinate}
    (failure : Not (system.ContextEquivalent left right)) :
    Not (TargetCompleteIdentification system left right) := by
  intro identified
  obtain ⟨quotient, quotientIdentifies⟩ := identified
  exact failure
    (quotient.contextUniversal_of_identified quotientIdentifies)

/-- Failure of all-context equivalence produces the distinguished outside
context promised by the target-defect alternative. -/
theorem targetDefect_of_not_contextEquivalent
    {object : FiniteObject.{u}}
    {atom : ProperBoundariedAtom object}
    {certificate : BoundariedAtomProfileCertificate atom}
    {Target : FiniteObject.{u} -> Prop}
    {system : CoordinateSystem.{u, v} certificate Target}
    {left right : system.Coordinate}
    (failure : Not (system.ContextEquivalent left right)) :
    TargetDefect system left right := by
  simp only [CoordinateSystem.ContextEquivalent, not_forall] at failure
  obtain ⟨outside, distinguishes⟩ := failure
  exact ⟨outside, distinguishes⟩

/-- The graph-local defective-identification corollary: a coordinate pair
that is not context-universal is both unavailable to target-complete
quotients and visibly target-defective. -/
theorem defectiveIdentification_of_not_contextEquivalent
    {object : FiniteObject.{u}}
    {atom : ProperBoundariedAtom object}
    {certificate : BoundariedAtomProfileCertificate atom}
    {Target : FiniteObject.{u} -> Prop}
    {system : CoordinateSystem.{u, v} certificate Target}
    {left right : system.Coordinate}
    (failure : Not (system.ContextEquivalent left right)) :
    Not (TargetCompleteIdentification system left right) ∧
      TargetDefect system left right :=
  ⟨not_targetCompleteIdentification_of_not_contextEquivalent failure,
    targetDefect_of_not_contextEquivalent failure⟩

namespace CoordinateSystem

variable {object : FiniteObject.{u}}
variable {atom : ProperBoundariedAtom object}
variable {certificate : BoundariedAtomProfileCertificate atom}
variable {Target : FiniteObject.{u} -> Prop}

/-- Literal all-context response equivalence is an equivalence relation on any
arbitrary coordinate collection. -/
def exactSetoid (system : CoordinateSystem.{u, v} certificate Target) :
    Setoid system.Coordinate where
  r := system.ContextEquivalent
  iseqv := {
    refl := by
      intro coordinate outside
      rfl
    symm := by
      intro left right equivalent outside
      exact (equivalent outside).symm
    trans := by
      intro first second third firstSecond secondThird outside
      exact (firstSecond outside).trans (secondThird outside)
  }

/-- Canonical maximal target-complete quotient generated by exact response
equivalence.  Applications need not construct routing or quotient evidence. -/
def exactQuotient (system : CoordinateSystem.{u, v} certificate Target) :
    TargetCompleteQuotient system where
  relation := system.exactSetoid
  context_complete := fun identified => identified

@[simp] theorem exactQuotient_identified_iff
    (system : CoordinateSystem.{u, v} certificate Target)
    (left right : system.Coordinate) :
    (system.exactQuotient.Identified left right) <->
      system.ContextEquivalent left right :=
  Iff.rfl

end CoordinateSystem

/-- Exhaustive semantic classification of two coordinates in one registered
atom-response system.  The negative branch carries the literal distinguishing
outside context.  The positive branch carries identification in the canonical
exact quotient, whose relation is definitionally all-context equivalence.

This is deliberately not a finite context-table decision: it uses classical
decidability only to split the semantic proposition and never asserts that a
finite schedule enumerates `OutsideContext`. -/
inductive ContextClassification
    {object : FiniteObject.{u}}
    {atom : ProperBoundariedAtom object}
    {certificate : BoundariedAtomProfileCertificate atom}
    {Target : FiniteObject.{u} -> Prop}
    (system : CoordinateSystem.{u, v} certificate Target)
    (left right : system.Coordinate) : Type (max u v) where
  | defective
      (notEquivalent : ¬ system.ContextEquivalent left right)
      (defect : TargetDefect system left right)
  | exact
      (identified : system.exactQuotient.Identified left right)

/-- Graph-owned exhaustive split on literal all-context equivalence. -/
noncomputable def CoordinateSystem.classifyContext
    {object : FiniteObject.{u}}
    {atom : ProperBoundariedAtom object}
    {certificate : BoundariedAtomProfileCertificate atom}
    {Target : FiniteObject.{u} -> Prop}
    (system : CoordinateSystem.{u, v} certificate Target)
    (left right : system.Coordinate) :
    ContextClassification system left right := by
  classical
  by_cases equivalent : system.ContextEquivalent left right
  · exact .exact equivalent
  · exact .defective equivalent
      (targetDefect_of_not_contextEquivalent equivalent)

namespace QuerySurface

open Hypostructure.Core.Residual

universe uPrevious

variable {Previous : Sort uPrevious}
variable {object : FiniteObject.{u}}
variable {atom : ProperBoundariedAtom object}
variable {certificate : BoundariedAtomProfileCertificate atom}
variable {Target : FiniteObject.{u} -> Prop}
variable {system : CoordinateSystem.{u, v} certificate Target}

/-- Classify two coordinates read from the same literal predecessor ledger.
The resulting query preserves their dependent identity and performs the exact
semantic split only when read at that stage. -/
noncomputable def contextClassification
    (left : Query Previous (fun _ => system.Coordinate))
    (right : Query Previous (fun _ => system.Coordinate)) :
    Query Previous (fun previous =>
      ContextClassification system (left.read previous) (right.read previous)) :=
  Query.ofFunction fun previous =>
    system.classifyContext (left.read previous) (right.read previous)

end QuerySurface

end Hypostructure.Graph.AtomResponse
