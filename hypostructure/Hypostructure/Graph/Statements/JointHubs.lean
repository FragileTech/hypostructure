import Hypostructure.Graph.Statements.SparseExitResidual
import Hypostructure.Graph.JointObject
import Hypostructure.Graph.WindowChargeKinds

/-!
# Statements: hubs, cubic vertices, windows and the remainder of G

Each statement is one of G's own facts at its canonical objects: the hubs
`H = {d ≠ 3}`, the cubic vertices `L`, the big hubs `B = {d ≥ 5}`, the canonical
window packing `P₀` with its support `W` and remainder `R`, and G's canonical capacity
presentation (library: `Graph/JointSystem.lean`, `Graph/JointObject.lean`,
`Graph/DensityOverload.lean`, `Graph/WindowCombination.lean`, `Graph/RemainderPaths.lean`,
`Graph/HubWindow.lean`, `Graph/WindowChargeKinds.lean`).

* the cubic vertices and the hubs: cubic neighbours, `5|H| + σ ≤ 2n`, the parity of
  `L–L` edges on walks, hub domination and `2|B| + σ ≤ n`, the V-shape caps, and the
  high-surplus bound `24σ + 465|B| ≤ 18n + 375|B|²` with its closure `8n ≤ 32s + 125s²`;
* density in excess form and the length-3 pairs at a hub;
* at `P₀`: the hub–window budget, the remainder slack and hanging windows, the windows
  against the big hubs, paths and cycles inside `R`, the window-free geometry, and the
  attachments to induced `P13`s;
* on the strict arm of the surplus scale: the orders the closure excludes;
* at G's canonical capacity presentation: the window structure of the charge, the
  recorded activation, and the target-response obstructions.

Every registered constant is an explicit `Parameters` argument; this module imports no
strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-! ## Hubs and cubic vertices -/

/-- **Cubic neighbours**: every cubic vertex of G has a cubic neighbour and at most two hub
neighbours, and `|L| ≤ Σ_{v∈L} |N(v) ∩ L| = 2e(L)`. -/
noncomputable abbrev CubicNeighbourSupplyStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.CubicNeighbourSupply object

/-- **`5|H| + σ ≤ 2n`.** -/
noncomputable abbrev HubCountBoundStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.HubCountBound object

/-- **Parity of `L–L` edges on walks of G**: `#LL + [u∈H] + [v∈H] + |p|` is even; an odd
walk between cubic vertices uses an odd number of `L–L` edges. -/
noncomputable abbrev LowEdgeParityStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.LowEdgeParity object

/-- **Hub domination and `2|B| + σ ≤ n`.** -/
noncomputable abbrev BigHubBoundStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.BigHubBound object

/-- **V-shape caps**: `≤ 12` middles per pair of big hubs, `|X₂| ≤ 12(|B|² − |B|)`, and
`4σ + 93|B| ≤ 2n + 75|B|² + 4|H|`. -/
noncomputable abbrev BigHubVShapesStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.BigHubVShapes object

/-- **The high-surplus bound**: `24σ + 465|B| ≤ 18n + 375|B|²`, and `8n ≤ 32s + 125s²` at
`s = n − σ`. -/
noncomputable abbrev HighSurplusBoundStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.HighSurplusBound object

/-- **Length-3 pairs at the hubs of G.** -/
noncomputable abbrev HubLengthThreePairsStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.HubLengthThreePairs object

/-- **Density of G in excess form**, the two-edge cut of every nonempty proper set, and the
single-hub slack. -/
noncomputable abbrev DensityExcessStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.DensityExcess object

/-! ## The canonical packing `P₀` -/

/-- **The remainder slack of `P₀` and its hanging windows.** -/
noncomputable abbrev RemainderSlackStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.RemainderSlack object (canonicalWindowPacking data object)

/-- **The hub–window budget at `P₀`.** -/
noncomputable abbrev HubWindowBudgetStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.HubWindowBudget object (canonicalWindowPacking data object)

/-- **The windows of `P₀` against the big hubs.** -/
noncomputable abbrev WindowHubBoundsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.WindowHubBounds object (canonicalWindowPacking data object)

/-- **Paths and cycles inside the remainder `R` of `P₀`.** -/
noncomputable abbrev RemainderPathBoundsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.RemainderPathBounds object (canonicalWindowPacking data object)

/-- **The window-free geometry of `P₀`.** -/
noncomputable abbrev WindowFreeGeometryStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.WindowFreeGeometry object (canonicalWindowPacking data object)

/-- **Attachments to the induced `P13`s of G.** -/
noncomputable abbrev InducedPathAttachmentStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.JointObject.InducedPathAttachment object

/-! ## The strict arm of the surplus scale -/

/-- **The orders the high-surplus closure excludes**: with `C = C_sp`,
`8n ≤ 32(n − C⌈√n⌉ − 1) + 125(n − C⌈√n⌉ − 1)²`, and every `t` with
`125t² + 24t < 8(C² + C + 1)` has `n > C² + C + 1 + t`. -/
noncomputable abbrev HighSurplusOrderStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  8 * object.vertexCount ≤
      32 * (object.vertexCount - data.spineScale * Core.ceilSqrt object.vertexCount - 1) +
        125 * ((object.vertexCount - data.spineScale * Core.ceilSqrt object.vertexCount - 1) *
          (object.vertexCount - data.spineScale * Core.ceilSqrt object.vertexCount - 1)) ∧
    ∀ t, 125 * (t * t) + 24 * t < 8 * (data.spineScale * data.spineScale + data.spineScale + 1) →
      data.spineScale * data.spineScale + data.spineScale + 1 + t < object.vertexCount

/-! ## G's canonical capacity presentation -/

/-- **The window structure of G's canonical charge and its recorded activation**: at G's
canonical capacity presentation (the recorded activation of its active family on `P₀`), the
charge's window structure holds and the recorded activation has early-blocked same-hub
pairs and no profile obstruction. -/
noncomputable def WindowChargeKindsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (connected : object.graph.Connected),
    canonicalCapacity data object = some (explicitCapacity active avoids connected) ∧
    Graph.WindowChargeKinds.WindowChargeStructure (explicitActivation active)
      (explicitCapacity active avoids connected).carrier data.threshold
      (canonicalWindowPacking data object) ∧
    Graph.WindowChargeKinds.RecordedActivationFacts active (object.portPairSchedule data.threshold)

/-- **Every target-response obstruction of G is a residual target defect**: at G's
canonical active family, on its full pair schedule. -/
noncomputable def ResponseObstructionTargetDefectStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (connected : object.graph.Connected),
    canonicalCapacity data object = some (explicitCapacity active avoids connected) ∧
    Graph.WindowChargeKinds.ResponseObstructionsAreTargetDefects
      (LengthOK := data.LengthOK) (threshold := data.threshold)
      (Graph.pairResponseActivation active) (object.portPairSchedule data.threshold)

end Hypostructure.Graph.Strategy.Spine
