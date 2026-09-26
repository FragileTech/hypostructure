import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Strategy.ColdCorridorRows.EntryDichotomies
import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdMass
import Hypostructure.Graph.Strategy.ColdCorridorRows.ReturnCorridor
import Hypostructure.Graph.Strategy.ColdCorridorRows.CorridorState
import Hypostructure.Graph.Strategy.ColdCorridorRows.FirstFailureOccurrence
import Hypostructure.Graph.Strategy.ColdCorridorRows.FailureClauses
import Hypostructure.Graph.Strategy.ColdCorridorRows.HandoffTransfer
import Hypostructure.Graph.Strategy.ColdCorridorRows.FirstFailureRouting
import Hypostructure.Graph.Strategy.ColdCorridorRows.DenseTerminal
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermExtraction
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermCandidates
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermFamilyPositive
import Hypostructure.Graph.Strategy.ColdCorridorRows.AbsorbedGerm
import Hypostructure.Graph.Strategy.ColdCorridorRows.AbsorbedGermFanEnvelope
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermTrichotomy
import Hypostructure.Graph.Strategy.ColdCorridorRows.NeutralTerminal
import Hypostructure.Graph.Strategy.ColdCorridorRows.TwoStrand
import Hypostructure.Graph.Strategy.ColdCorridorRows.CanonicalReplacement
import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdFamilyClosure

/-!
# The cold branch, nodes `[145]`--`[154]`

Aggregator of the per-row modules under `ColdCorridorRows/`.  The modules
contain only paper-node operations on the literal current `ExactLedger`:
exclusive decisions and the atomic facts of the cold branch.  No alternate
state or detached implication is exported; the concrete germ family required
at `[153]` remains a fact of that residual.
-/
