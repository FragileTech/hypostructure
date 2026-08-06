import Hypostructure.Graph.Strategy.Route8Run

/-!
# Fixture: the route-8 carrier closure, run end to end

`Spine.runRouteEight` is quantified over the keys it consumes and produces.
This fixture installs it at the spine's *own* vocabulary, on the Type A residual
of node `[63]` that `Spine.run` already reaches -- which is where Figure 8 hands
the route-8 arm on -- and checks the three things the audit's Ledger, Transport
and Residual columns claim:

* the block elaborates against that branch cursor, with every prerequisite of a
  row discharged by resolution against the incoming index;
* the closed arm's output index is the incoming one with the three exit-absence
  facts of nodes `[101]`, `[103]` and `[105]`, the six route-8 facts, and Core's closure
  entry on top, so every earlier fact of the branch is still in the type and the
  terminal really is closed;
* the audit accounts for every fact with chronological commits and no semantic
  fact was committed twice.

Nothing here is specific to one manuscript: the run is at the framework's own
`Spine.Data`, left as a parameter.
-/

namespace Hypostructure.Fixtures.Route8Run

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- The key index of the closed route-8 terminal, over Figure 8's silent entry
into the shared exit segment. -/
abbrev closedKeys : FactKeys (Input BranchState Presentation presentation data) :=
  Hypostructure.Graph.Strategy.Spine.route8ClosedKeys
    (typeAVisibleFirstExcessKeys (BranchState := BranchState)
      (presentation := presentation) (data := data))

/-- **The route-8 block runs on node `[94]`, the silent entry of the shared exit
segment.**

Figure 8 draws one segment `[101]`--`[107]` entered from node `[99]`'s no arm
and from node `[94]`, and `lem:typeA-exit4-residual-routing` is the manuscript's
statement that the two combine.  The block is therefore asked on a cursor
carrying that lemma's hypothesis — `typeASaturatedExitEntry`, which node `[94]`
commits — and not on the bare Type A residual of node `[63]`, which is above
both entries and above node `[89]`'s saturation.

Every freshness side condition is decided on the vocabulary's own finite `Key`,
and the block's internal prerequisites -- node `[113]` after the `[109]`
collection, node `[123]` after the census, and node `[124]` after `[113]`,
`[116]`, `[123]` and the two exit absences -- are discharged by instance
resolution against the index each row is handed. -/
noncomputable def run
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAVisibleFirstExcessKeys) :
    Route8Result selected typeAVisibleFirstExcessKeys :=
  runRouteEight history (peelFresh := by simp) (noPeelFresh := by simp)
    (peeledChargeFresh := by simp) (compressionFresh := by simp)
    (traceLevelFresh := by simp) (exitFourFresh := by simp)
    (exitFourFreeFresh := by simp) (exitFiveFresh := by simp)
    (exitFiveFreeFresh := by simp) (exitSixFresh := by simp)
    (exitSixFreeFresh := by simp) (exitSixProperFresh := by simp)
    (exitSixGlobalFresh := by simp)
    (residualFresh := by simp) (freeFresh := by simp)
    (burdenFresh := by simp) (coreFresh := by simp) (censusFresh := by simp)
    (descentFresh := by simp) (closedFresh := by simp)
    (closureFresh := by simp)

/-- **The nine facts of the block are all on the ledger after it runs.**

Membership rather than position: later blocks add their own facts to the same
index, and this check is about what the route-8 block contributes. -/
theorem run_audit_contains_route8_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected closedKeys) :
    ∀ fact ∈ [(name .typeAExitFourFree),
        (name .typeAExitFiveFree),
        (name .typeAExitSixFree),
        (name .route8Residual),
        (name .route8Burden),
        (name .route8CarrierCore),
        (name .route8Census),
        (name .route8Descent),
        (name .route8Closed)],
      fact ∈ (ExactLedger.audit history).facts := by
  intro fact member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.mem_map.mpr ⟨K .typeAExitFourFree, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .typeAExitFiveFree, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .typeAExitSixFree, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .route8Residual, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .route8Burden, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .route8CarrierCore, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .route8Census, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .route8Descent, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .route8Closed, by simp, rfl⟩

/-- **Every fact of the block is accounted for by a chronological commit.** -/
theorem run_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected closedKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **No semantic fact was committed twice.** -/
theorem run_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected closedKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

end Hypostructure.Fixtures.Route8Run
