import Hypostructure.Graph.RootedReturn

/-!
# Generic terminal consumers for official Graph strategies

Only proof-carrying Graph certificates can enter these consumers.  The
interface consists solely of accepted target data and cannot provide a
classifier, closure, or arbitrary target proof.
-/

namespace Hypostructure.Graph.Strategy.Official

open Hypostructure.Graph

universe u

/-- Generic decidable cycle-length target presentation.

The target is a predicate, rather than a finite list: this is necessary for
targets such as powers of two.  The predicate is mathematical problem data;
the only executable component is its decision procedure, which can decide
membership but cannot construct a strategy terminal or choose a DAG port. -/
structure CycleTargetInterface where
  CycleLengthOK : Nat → Prop
  cycleLengthDecidable : DecidablePred CycleLengthOK

/-- Closed target families understood by the universal Graph executor.
Applications choose mathematical data, but cannot attach a theorem or
strategy-specific target consumer. -/
inductive CycleTargetSpec where
  | finiteLengths (lengths : List Nat)
  | powersOfTwoFromExponentTwo
  deriving DecidableEq, Repr

namespace CycleTargetSpec

/-- Framework interpretation of a closed target family. -/
def CycleLengthOK : CycleTargetSpec → Nat → Prop
  | .finiteLengths lengths, length => length ∈ lengths
  | .powersOfTwoFromExponentTwo, length =>
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent

/-- The target interface is reconstructed from the closed family. -/
noncomputable def interface (spec : CycleTargetSpec) : CycleTargetInterface where
  CycleLengthOK := spec.CycleLengthOK
  cycleLengthDecidable := Classical.decPred _

end CycleTargetSpec

namespace CycleTargetInterface

variable (interface : CycleTargetInterface)

def ReturnLengthOK (length : Nat) : Prop :=
  interface.CycleLengthOK (length + 1)

/-- Proof-relevant shifted target algebra used by every rooted-return
consumer.  It is derived definitionally from the single cycle predicate; an
application cannot provide a second return predicate or an inconsistent
conversion theorem. -/
structure ReturnAlgebraCertificate : Prop where
  return_iff_cycle_succ :
    ∀ length, interface.ReturnLengthOK length ↔
      interface.CycleLengthOK (length + 1)

/-- Framework-owned return algebra certificate. -/
def returnAlgebra : interface.ReturnAlgebraCertificate where
  return_iff_cycle_succ := fun _ => Iff.rfl

instance (length : Nat) : Decidable (interface.CycleLengthOK length) :=
  interface.cycleLengthDecidable length

instance (length : Nat) : Decidable (interface.ReturnLengthOK length) :=
  interface.cycleLengthDecidable (length + 1)

/-- Framework-owned terminal consumer for a genuine rooted return. -/
def consumeRootedReturn {object : FiniteObject.{u}}
    (certificate : EdgeRootedReturn object interface.ReturnLengthOK) :
    CycleCertificate object interface.CycleLengthOK where
  vertex := certificate.dart.fst
  walk := certificate.cycle
  isCycle := certificate.cycle_isCycle
  length_ok := by
    rw [certificate.cycle_length]
    exact certificate.length_ok

/-- Framework-owned terminal consumer for the generic two-path gluing
operation. -/
def consumeCommonEndpoints {object : FiniteObject.{u}}
    (pair : CommonEndpointsCycle object)
    (accepted : interface.CycleLengthOK
      (pair.forward.length + pair.backward.length)) :
    CycleCertificate object interface.CycleLengthOK :=
  pair.target interface.CycleLengthOK accepted

end CycleTargetInterface

end Hypostructure.Graph.Strategy.Official
