import Hypostructure.Graph.ResponseDelocalization
import Hypostructure.Graph.ExitFourFamily

/-!
# The failure alternatives of a trace basin

`def:typeA-trace-basin`: the trace basin `B_u` is *target-complete-minimal*
when none of four alternatives occurs.  Each alternative below is the
manuscript's own clause, stated on the declared `u`-supported coordinate
algebra `ρ_u(B_u)` of the selected basin (`PresentedEntry.ofTraceBasin`):

* (a) a trace-local quotient of `ρ_u(B_u)` is distinguished by an outside
  context — `Response.TargetDefect` of a retained reading against the basin;
* (b) a nontrivial target-complete response quotient of the declared
  trace-response state — `TraceResponseQuotient` of
  `Graph/Route8Residual.lean`;
* (c) an equality among coordinates of `ρ_u(B_u)` becomes target-complete only
  after adjoining a larger connected support `Z ⊋ B_u` — `Route8.Delocalization`
  based at the basin;
* (d) two declared outside connector configurations of `ρ_u(B_u)`, through the
  receiver's completion port, have a surviving first separator in the sense of
  `def:typeA-continuation-classes` — `DecoratedHandoff.Surviving`.

`lem:typeA-reduced-silent-residual` identifies (a)--(d) with exits (4)--(7) of
`def:typeA-saturated-exits`; the predicates here are therefore the same data the
saturated-exit decisions of the Type A branch test, read at one basin.  Nothing
here is specialized to a manuscript constant.
-/

namespace Hypostructure.Graph.Route8.TraceBasin

open Hypostructure
open Hypostructure.Graph

universe u

/-- **Alternative (a) of `def:typeA-trace-basin`.**  A trace-local quotient of
`ρ_u(B_u)` — retaining a subset of the declared family and forgetting a
coordinate with genuinely internal declared support — whose reading some
outside `∂B_u`-context distinguishes from the basin itself. -/
def TraceLocalTargetDefect (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (basin : Finset object.Vertex) : Prop :=
  ∃ retained : Finset (PresentedEntry.TraceCoordinate object support),
    retained ⊆ PresentedEntry.traceCoordinates object support threshold receiver load ∧
      (∃ changed ∈ PresentedEntry.traceCoordinates object support threshold receiver load,
        changed ∉ retained ∧
          ExitFour.TraceCoordinateInternal object support basin threshold receiver
            load changed) ∧
      Response.TargetDefect (HasCycleWithLength LengthOK)
        (PresentedEntry.retainedReading object support basin threshold LengthOK
          (PresentedEntry.retainedBaseCoordinates object support retained))
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin)

/-- **Alternative (c) of `def:typeA-trace-basin`.**  An equality among declared
coordinates of `ρ_u(B_u)` that becomes target-complete only after adjoining a
larger connected support `Z ⊋ B_u`: `Route8.Delocalization` of the basin's own
presented entry, based at the basin. -/
def TraceDelocalization (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (basin : Finset object.Vertex) : Prop :=
  Nonempty
    (Delocalization (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK)
      (PresentedEntry.ofTraceBasin object support basin threshold LengthOK receiver
        load)
      basin)

/-- **Alternative (d) of `def:typeA-trace-basin`.**  Two declared outside
connector configurations of `ρ_u(B_u)` through the receiver's completion port —
two routed loads of the finite connector family, one of them the indexed load —
separate at a first separator `z`, and the identification on the switch support
`S_z` is neither target-defective, nor target-complete, nor valid only after
enlarging: `z` is surviving. -/
def TraceSurvivingSeparator (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (_basin : Finset object.Vertex) : Prop :=
  ∃ family : ExitFour.ContinuationFamily object support threshold receiver,
    load ∈ family.loads ∧
      ∃ leftLoad rightLoad : object.Vertex,
        ∃ leftMem : leftLoad ∈ family.loads, ∃ rightMem : rightLoad ∈ family.loads,
          leftLoad ≠ rightLoad ∧
            ∃ separation : DecoratedHandoff.Separation object support receiver
                family.outside,
              separation.left.path = (family.germ leftLoad leftMem).path ∧
                separation.right.path = (family.germ rightLoad rightMem).path ∧
                ∃ reading : DecoratedHandoff.SwitchReading separation,
                  DecoratedHandoff.Surviving (HasCycleWithLength LengthOK) reading
                    (∃ representative : FiniteObject.{u},
                      representative.LexicographicallySmaller object ∧
                        MinimumDegreeAtLeast threshold representative ∧
                        (HasCycleWithLength LengthOK representative →
                          HasCycleWithLength LengthOK object))

/-- The selected basin is target-complete-minimal precisely when none of the
four trace-local failure alternatives of `def:typeA-trace-basin` occurs. -/
def TargetCompleteMinimal (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (basin : Finset object.Vertex) : Prop :=
  TraceComplete object support threshold receiver load basin ∧
    ¬ TraceLocalTargetDefect object support threshold LengthOK receiver load basin ∧
    (¬ ∃ retained,
      TraceResponseQuotient object support threshold LengthOK receiver load basin
        retained) ∧
    ¬ TraceDelocalization object support threshold LengthOK receiver load basin ∧
    ¬ TraceSurvivingSeparator object support threshold LengthOK receiver load basin

/-- The concrete route-8 entry of `def:typeA-route8-carriers` for the selected
load/basin. -/
def Route8Entry (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex) : Prop :=
  ∃ basin : Finset object.Vertex,
    select? object support threshold receiver load = some basin ∧
      TargetCompleteMinimal object support threshold LengthOK receiver load basin

end Hypostructure.Graph.Route8.TraceBasin
