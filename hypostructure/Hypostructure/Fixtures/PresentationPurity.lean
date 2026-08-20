import Hypostructure.Core.PresentationPurity
import Hypostructure.Core.SemanticEquivalence
import Hypostructure.Core.Context
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Graph.Object
import Hypostructure.Graph.ReceiverLoad

namespace Hypostructure.Fixtures.PresentationPurity

open Hypostructure Core

/-! Positive fixtures: raw values, intrinsic indices, operators, and predicates. -/

example : PrimitiveRole.definition.presentationSafe = true := rfl
example : PrimitiveRole.operator.presentationSafe = true := rfl
example : PrimitiveRole.finiteEnumeration.presentationSafe = true := rfl
example : PrimitiveRole.decisionProcedure.presentationSafe = true := rfl
example : PrimitiveRole.semanticLaw.presentationSafe = false := rfl
example : PrimitiveRole.localCertificate.presentationSafe = false := rfl
example : PrimitiveRole.importedContract.presentationSafe = false := rfl

def defaultProblem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  BranchState := fun _ => Unit

#check_presentation_pure defaultProblem

structure ScalarPresentation where
  vertexCount : Nat
  threshold : Nat
  capacity : Nat

def scalarPresentation : ScalarPresentation := ⟨4, 3, 9⟩

#check_presentation_pure ScalarPresentation
#check_presentation_pure scalarPresentation

structure ContainerPresentation (n : Nat) where
  enabled : Bool
  focus : Fin (n + 1)
  schedule : List Nat
  fallback : Option Nat
  bounds : Nat × Nat

def containerPresentation : ContainerPresentation 2 :=
  ⟨true, 0, [0, 1, 2], some 1, (0, 2)⟩

#check_presentation_pure containerPresentation

structure ComputationalPresentation (Carrier State Input : Type) where
  test : Carrier → Bool
  relation : Carrier → Carrier → Prop
  step : State → Input → State

#check_presentation_pure ComputationalPresentation

#check_presentation_pure Graph.ReceiverLoad.LoadCapacityProfile

def installedProblem : Core.Problem :=
  Graph.problemWithPresentation (fun _ => True) (fun _ => Unit)
    ScalarPresentation scalarPresentation

#check_presentation_pure installedProblem

inductive RecursiveData where
  | nil
  | next (value : Nat) (rest : RecursiveData)

#check_presentation_pure RecursiveData

/-! Negative fixtures: each error is captured so the normal build exercises
the rejection boundary. -/

structure DirectProof where
  threshold : Nat
  threshold_pos : 0 < threshold

/--
error: public presentation is not proof-free
root: DirectProof
path: DirectProof.threshold_pos
field type: (Nat.succ 0).le self.threshold
reason: proposition-valued field supplies a proof owned by the backend
replacement: keep the raw operands in the presentation and prove this proposition in Core or the domain backend
-/
#guard_msgs (error) in
#check_presentation_pure DirectProof

structure LawPackage (Carrier : Type) where
  relation : Carrier → Carrier → Prop
  reflexive : ∀ x, relation x x

/--
error: public presentation is not proof-free
root: LawPackage
path: LawPackage.reflexive
field type: ∀ (x : ?Carrier), self.relation x x
reason: proposition-valued field supplies a proof owned by the backend
replacement: keep the raw operands in the presentation and prove this proposition in Core or the domain backend
-/
#guard_msgs (error) in
#check_presentation_pure LawPackage

structure InnerCertificate where
  count : Nat
  count_pos : 0 < count

structure NestedCertificate where
  label : String
  certificate : InnerCertificate

/--
error: public presentation is not proof-free
root: NestedCertificate
path: NestedCertificate.certificate.count_pos
field type: (Nat.succ 0).le self.count
reason: proposition-valued field supplies a proof owned by the backend
replacement: keep the raw operands in the presentation and prove this proposition in Core or the domain backend
-/
#guard_msgs (error) in
#check_presentation_pure NestedCertificate

structure ExistencePackage where
  witness : ∃ n : Nat, n > 0

/--
error: public presentation is not proof-free
root: ExistencePackage
path: ExistencePackage
field type: ExistencePackage
reason: proposition-valued field supplies a proof owned by the backend
replacement: keep the raw operands in the presentation and prove this proposition in Core or the domain backend
-/
#guard_msgs (error) in
#check_presentation_pure ExistencePackage

structure NonemptyPackage where
  Carrier : Type
  member : Nonempty Carrier

/--
error: public presentation is not proof-free
root: NonemptyPackage
path: NonemptyPackage.member
field type: Nonempty self.Carrier
reason: proposition-valued field supplies a proof owned by the backend
replacement: keep the raw operands in the presentation and prove this proposition in Core or the domain backend
-/
#guard_msgs (error) in
#check_presentation_pure NonemptyPackage

structure EquivalencePackage where
  equivalence : Nat ≃ Nat

/--
error: public presentation is not proof-free
root: EquivalencePackage
path: EquivalencePackage.equivalence
field type: ℕ ≃ ℕ
reason: proof or audit package belongs behind the presentation boundary
replacement: present the raw data or operators and construct the certificate in Core or the domain backend
-/
#guard_msgs (error) in
#check_presentation_pure EquivalencePackage

def semanticProblem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  BranchState := fun _ => Unit

structure SemanticPackage where
  semantics : Core.SemanticEquivalence semanticProblem

/--
error: public presentation is not proof-free
root: SemanticPackage
path: SemanticPackage.semantics.equivalence
field type: Equivalence self.equivalent
reason: proposition-valued field supplies a proof owned by the backend
replacement: keep the raw operands in the presentation and prove this proposition in Core or the domain backend
-/
#guard_msgs (error) in
#check_presentation_pure SemanticPackage

structure MinimalContextPackage where
  context : Core.MinimalCounterexampleContext semanticProblem
    (fun _ => False) {
      Measure := Nat
      lt := fun _ _ => False
      wellFounded := ⟨fun _ => Acc.intro _ (fun _ impossible => impossible.elim)⟩
      measure := fun _ => 0 }

/--
error: public presentation is not proof-free
root: MinimalContextPackage
path: MinimalContextPackage.context.toAvoidingContext.toBranchContext.baseline
field type: True
reason: proposition-valued field supplies a proof owned by the backend
replacement: keep the raw operands in the presentation and prove this proposition in Core or the domain backend
-/
#guard_msgs (error) in
#check_presentation_pure MinimalContextPackage

structure CompleteSchedulePackage where
  schedule : Core.Finite.CompleteEnumeration Nat

/--
error: public presentation is not proof-free
root: CompleteSchedulePackage
path: CompleteSchedulePackage.schedule.toEnumeration.nodup
field type: List.Pairwise (fun x1 x2 => x1 ≠ x2) self.values
reason: proposition-valued field supplies a proof owned by the backend
replacement: keep the raw operands in the presentation and prove this proposition in Core or the domain backend
-/
#guard_msgs (error) in
#check_presentation_pure CompleteSchedulePackage

structure SubtypePackage where
  selected : {n : Nat // n > 0}

/--
error: public presentation is not proof-free
root: SubtypePackage
path: SubtypePackage.selected
field type: { n // n > 0 }
reason: proof or audit package belongs behind the presentation boundary
replacement: present the raw data or operators and construct the certificate in Core or the domain backend
-/
#guard_msgs (error) in
#check_presentation_pure SubtypePackage

structure ProvisionPackage where
  entry : Core.Provision.Entry

/--
error: public presentation is not proof-free
root: ProvisionPackage
path: ProvisionPackage.entry
field type: Provision.Entry
reason: proof or audit package belongs behind the presentation boundary
replacement: present the raw data or operators and construct the certificate in Core or the domain backend
-/
#guard_msgs (error) in
#check_presentation_pure ProvisionPackage

opaque HiddenCarrier : Type

structure OpaquePackage where
  transform : HiddenCarrier → Nat

/--
error: public presentation is not proof-free
root: OpaquePackage
path: OpaquePackage.transform
field type: HiddenCarrier
reason: opaque type cannot be verified as proof-free
replacement: expose a proof-free data view whose fields can be inspected at the public boundary
-/
#guard_msgs (error) in
#check_presentation_pure OpaquePackage

end Hypostructure.Fixtures.PresentationPurity
