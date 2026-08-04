import Hypostructure.Core.Assembly.LocalToGlobal

/-! # Pointwise local-to-global fixture -/

namespace Hypostructure.Fixtures.LocalToGlobal

open Hypostructure.Core

def problem : Core.Problem where
  Ambient := Nat
  Baseline _ := True
  BranchState _ := Unit

def semantics : Core.SemanticEquivalence problem :=
  Core.SemanticEquivalence.equality problem

def assembly : Core.AtomContextAssembly problem semantics where
  Interface := Nat
  Site _ := Unit
  interface object _ := object
  Atom interface := {value : Nat // value = interface}
  Context _ := Unit
  compatible _ _ := True
  atom object _ := ⟨object, rfl⟩
  context _ _ := ()
  assemble atom _ := atom.1
  extractedCompatible _ _ := trivial
  reconstruct _ _ := rfl

def localPair : assembly.LocalProperty :=
  fun {interface} atom _context => atom.1 = interface

def global (object : Nat) : Prop := object = object

def profile : assembly.LocalToGlobalProfile localPair global where
  close _object certificate := certificate.localAt ()

def certificate (object : Nat) : assembly.PointwiseCertificate localPair object where
  localAt _ := rfl

def root : Core.Residual.Ledger Nat :=
  Core.Residual.Ledger.initial 7

def objectQuery : Core.Residual.Query (Core.Residual.Ledger Nat)
    (fun _ => Nat) :=
  Core.Residual.Query.residual

def certificateQuery : Core.Residual.Query (Core.Residual.Ledger Nat)
    (fun previous => assembly.PointwiseCertificate localPair
      (objectQuery.read previous)) :=
  objectQuery.dependentMap fun _ object => certificate object

def globalizeNode := profile.globalize objectQuery certificateQuery

def globalizedStage := globalizeNode.run root

example : globalizedStage.previous = root := rfl

example : global root.residual := globalizedStage.added

def input : Core.Strategy.ProblemInput problem where
  object := (7 : Nat)
  baseline := trivial
  branchState := ()

def programStage : Core.Residual.Ledger (Core.Strategy.ProblemInput problem) :=
  Core.Residual.Ledger.initial input

def programCertificateQuery :
    Core.Residual.Query
      (Core.Residual.Ledger (Core.Strategy.ProblemInput problem))
      (fun stage => assembly.PointwiseCertificate localPair
        (Core.Residual.residualOf stage).object) :=
  (Core.Residual.Query.residual
    (Source := Core.Residual.Ledger (Core.Strategy.ProblemInput problem))
    (Residual := Core.Strategy.ProblemInput problem)).dependentMap
      fun _ residual => certificate residual.object

def openResult :
    Core.Strategy.HaltingProgram.OpenResult problem
      (Core.Residual.Ledger (Core.Strategy.ProblemInput problem))
      (fun _ => Unit) input where
  stage := programStage
  residual_eq := rfl
  terminal := ()

example : global input.object :=
  profile.globalizeOpenResult programCertificateQuery openResult

def closureNode := profile.node
  (fun previous : Core.Residual.Ledger Nat => previous.residual)
  (fun previous => certificate previous.residual)

def stage := closureNode.run root

example : stage.previous = root := rfl

example : global root.residual := stage.added

#print axioms Core.AtomContextAssembly.LocalToGlobalProfile.run
#print axioms Core.AtomContextAssembly.LocalToGlobalProfile.node
#print axioms Core.AtomContextAssembly.LocalToGlobalProfile.globalize
#print axioms Core.AtomContextAssembly.LocalToGlobalProfile.globalizeOpenResult
#print axioms stage

end Hypostructure.Fixtures.LocalToGlobal
