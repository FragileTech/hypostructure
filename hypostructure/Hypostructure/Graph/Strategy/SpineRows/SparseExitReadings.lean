import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SparseExitReadings

/-!
# The edge switches of G, and the readings of the clause-(b) witness triples

Type A rows.  Each reads its prerequisites through `inputs.get` and publishes,
at G, one fact per key (contracts: `Graph/Contracts/Spine/SparseExitReadings.lean`).
No row decides or splits anything.  A row runs right after the last producer
of the keys it reads, on the shared prefix, so every branch below inherits its
facts:
- the entry prefix (`Assembly/Entry.lean`): the readings of every clause-(b)
  witness triple in G's own surroundings `G − Z` (after `[4]`);
- the top of the strict arm of `[19]` (`Assembly/Final.lean`, before `[20]`):
  where the surplus sits and the switch at every high/baseline edge.

G-only restatement (`g-repair`): the rows at `[20a]`'s canonical witness
(`sparseExitReadingsRow`, `sparseExitReadingsConsequencesRow`,
`sparseExitPrivateSwitchRow`) are removed with the `[20a]` exit, which is empty
at G.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Entry prefix, right after `[4]`'s selection: the readings of every clause-(b)
witness triple of G are negative in G's own surroundings `G − Z`. -/
@[reducible] noncomputable def everyWitnessSpectrumRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.everyWitnessSpectrum
    { Requires := [K .selection]
      Produces := [K .everyWitnessSpectrumSplit]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .everyWitnessSpectrumSplit)
        ⟨Contracts.Spine.SparseExitReadings.everyWitnessSpectrumSplit_holds
          (object := inputs.current.object) (inputs.get (K .selection)).down.1⟩
      .nil)

/-- Top of the strict arm of `[19]` (after `C + 1 ≤ ⌈√n⌉` is published): where the
surplus of G sits. -/
@[reducible] noncomputable def highSurplusConfigurationRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.highSurplusConfiguration
    { Requires := [K .cubicBaseline, K .minDegreeBaseline, K .surplusAbove,
        K .ceilSqrtAboveScale]
      Produces := [K .highSurplusConfiguration]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .highSurplusConfiguration)
        ⟨Contracts.Spine.SparseExitReadings.highSurplusConfiguration_holds
          (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .cubicBaseline)).down.2.2.1.2.2.2
          (inputs.get (K .surplusAbove)).down
          (inputs.get (K .ceilSqrtAboveScale)).down⟩
      .nil)

/-- Top of the strict arm of `[19]`: the switch at every high/baseline edge. -/
@[reducible] noncomputable def highEndpointSwitchRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.highEndpointSwitch
    { Requires := [K .slackIndependent, K .twoSwitchForcedPath, K .sameVertexSwitchForcedPath,
        K .highSurplusConfiguration]
      Produces := [K .highEndpointSwitch]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .highEndpointSwitch)
        ⟨Contracts.Spine.SparseExitReadings.highEndpointSwitch_holds
          (object := inputs.current.object)
          (inputs.get (K .slackIndependent)).down
          (inputs.get (K .twoSwitchForcedPath)).down
          (inputs.get (K .sameVertexSwitchForcedPath)).down
          (inputs.get (K .highSurplusConfiguration)).down⟩
      .nil)

end Hypostructure.Graph.Strategy.Spine
