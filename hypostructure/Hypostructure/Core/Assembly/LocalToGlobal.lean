import Hypostructure.Core.Assembly.AtomContext
import Hypostructure.Core.Residual.Query
import Hypostructure.Core.Strategy

/-!
# Pointwise local-to-global closure

This module deliberately has no finite-enumeration premise.  A certificate is
pointwise over the exact sites owned by one ambient object; a domain profile
states how those local facts imply its global conclusion.  Finite CTs may
construct such a certificate from an explicit schedule, while analytic users
may prove it directly on an infinite family of windows.
-/

namespace Hypostructure.Core

universe uAmbient uBranch uInterface uSite uAtom uContext uPrevious

namespace AtomContextAssembly

variable {P : Problem.{uAmbient, uBranch}} {E : SemanticEquivalence P}

/-- A property of one exact atom/context pair. -/
abbrev LocalProperty
    (A : AtomContextAssembly P E) :=
  {interface : A.Interface} -> A.Atom interface -> A.Context interface -> Prop

/-- Pointwise evidence over every site belonging to one literal object. -/
structure PointwiseCertificate
    (A : AtomContextAssembly P E)
    (Local : A.LocalProperty) (object : P.Ambient) where
  localAt : forall site : A.Site object,
    Local (A.atom object site) (A.context object site)

/-- Domain theorem translating a pointwise atom/context property into a
global property.  Core owns application and ledger registration. -/
structure LocalToGlobalProfile
    (A : AtomContextAssembly P E)
    (Local : A.LocalProperty)
    (Global : P.Ambient -> Prop) where
  close : forall object, A.PointwiseCertificate Local object -> Global object

namespace LocalToGlobalProfile

/-- Apply a registered local-to-global theorem. -/
def run {A : AtomContextAssembly P E} {Local : A.LocalProperty}
    {Global : P.Ambient -> Prop}
    (profile : A.LocalToGlobalProfile Local Global)
    (object : P.Ambient) (certificate : A.PointwiseCertificate Local object) :
    Global object :=
  profile.close object certificate

/-- Register local-to-global closure as a proposition node over the literal
predecessor ledger. -/
def node {A : AtomContextAssembly P E} {Local : A.LocalProperty}
    {Global : P.Ambient -> Prop}
    (profile : A.LocalToGlobalProfile Local Global)
    {Previous : Sort uPrevious}
    (object : Previous -> P.Ambient)
    (certificate : (previous : Previous) ->
      A.PointwiseCertificate Local (object previous)) :
    Residual.Node Previous (fun previous => Global (object previous)) :=
  Residual.Node.create fun previous =>
    profile.run (object previous) (certificate previous)

/-- Assemble a global proposition from typed reads on any active residual
stage.  `Previous` is completely polymorphic: in particular it may be the
exact live stage produced by a compiled DAG.  The operation reads the
pointwise certificate from that stage and delegates the sole ledger write to
the existing `Residual.Node.derive` API. -/
def globalize {A : AtomContextAssembly P E} {Local : A.LocalProperty}
    {Global : P.Ambient -> Prop}
    (profile : A.LocalToGlobalProfile Local Global)
    {Previous : Sort uPrevious}
    (object : Residual.Query Previous (fun _ => P.Ambient))
    (certificate : Residual.Query Previous fun previous =>
      A.PointwiseCertificate Local (object.read previous)) :
    Residual.Node Previous (fun previous => Global (object.read previous)) :=
  Residual.Node.derive certificate fun previous pointwise =>
    profile.run (object.read previous) pointwise

/-- Apply the same assembly theorem to an arbitrary live result emitted by a
framework strategy program.  The terminal family is unrestricted.  The only
semantic input is a typed query for the pointwise certificate on the exact
live stage; `OpenResult.residual_eq` transports the assembled proposition
back to the original theorem input. -/
def globalizeOpenResult
    {A : AtomContextAssembly P E} {Local : A.LocalProperty}
    {Global : P.Ambient -> Prop}
    (profile : A.LocalToGlobalProfile Local Global)
    {Stage : Type uPrevious}
    [Residual.HasResidual Stage (Strategy.ProblemInput P)]
    {TerminalResidual : Stage -> Type uPrevious}
    (certificate : Residual.Query Stage fun stage =>
      A.PointwiseCertificate Local (Residual.residualOf stage).object)
    {input : Strategy.ProblemInput P}
    (result : Strategy.HaltingProgram.OpenResult P Stage TerminalResidual input) :
    Global input.object := by
  have assembled := profile.run (Residual.residualOf result.stage).object
    (certificate.read result.stage)
  rw [result.residual_eq] at assembled
  exact assembled

end LocalToGlobalProfile

end AtomContextAssembly

end Hypostructure.Core
