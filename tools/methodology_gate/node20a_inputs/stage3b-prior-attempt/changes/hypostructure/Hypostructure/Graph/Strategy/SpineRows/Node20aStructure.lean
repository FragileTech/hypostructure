import Hypostructure.Graph.Strategy.SpineVocabulary

namespace Hypostructure.Graph.Strategy.Spine
open Hypostructure
open Hypostructure.Core.Residual Hypostructure.Core.Strategy
open Graph.CyclePassage Graph.S1child1 Graph.S1child2 Graph.S1child3
universe u v
variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation} {data : Data.{u}}

/-- One owner-local fact-only row. Eliminate f021 here, identify the three
canonical retained witnesses here, and eliminate f118 at each original c here.
The sole production retains that exact tuple and its dependent S1--S3 proofs.
The Type A execution form is the same as `everyWitnessSpectrumRow`. -/
@[reducible] noncomputable def originalCyclePassageRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.originalCyclePassage
    { Requires := [K .sparseTargetDefectResidual, K .witnessReadingsCycleFree,
        K .witnessReadingCounts, K .positiveCyclePrivateEdge, K .tightEndpoint]
      Produces := [K .originalCyclePassage]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs => by
      refine .cons (key := K .originalCyclePassage) ⟨?_⟩ .nil
      obtain ⟨w, canonical, spec⟩ :=
        (inputs.get (K .sparseTargetDefectResidual)).down
      obtain ⟨wFree, canonicalFree, free⟩ :=
        (inputs.get (K .witnessReadingsCycleFree)).down
      have sameFree : wFree = w := Option.some.inj (canonicalFree.symm.trans canonical)
      subst wFree
      obtain ⟨wCounts, canonicalCounts, counts⟩ :=
        (inputs.get (K .witnessReadingCounts)).down
      have sameCounts : wCounts = w := Option.some.inj (canonicalCounts.symm.trans canonical)
      subst wCounts
      obtain ⟨wPrivate, canonicalPrivate, P, N, orientation, separates, privateEdge, notLe⟩ :=
        (inputs.get (K .positiveCyclePrivateEdge)).down
      have samePrivate : wPrivate = w := Option.some.inj (canonicalPrivate.symm.trans canonical)
      subst wPrivate
      have tight := (inputs.get (K .tightEndpoint)).down
      refine ⟨w, canonical, spec, P, N, orientation, separates, privateEdge, notLe, ?_⟩
      intro c
      obtain ⟨pl, pr, supplied⟩ := privateEdge c
      obtain ⟨I⟩ := retained_firstContacts w free orientation separates c pl pr
        supplied.1 supplied.2.2.2.2.2
      obtain ⟨L⟩ := restrict_interval I supplied.2.2.2.2.2
        (positive_subset_support w spec orientation)
      exact ⟨{
        pl := pl
        pr := pr
        supplied := supplied
        interval := I
        lift := L
        active := endpoints_of_lift w counts orientation I L
        private_wedge := privateWedge_of_lift w supplied I L
        tight_wedge := tightWedge_of_private w tight I L
          (privateWedge_of_lift w supplied I L)
        contacts := contacts_reachable I L
        ambient_contacts := contacts_in_positive_graph I L
      }⟩)

end Hypostructure.Graph.Strategy.Spine
