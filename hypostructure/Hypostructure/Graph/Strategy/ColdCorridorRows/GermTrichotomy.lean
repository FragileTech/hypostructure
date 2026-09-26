import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Nodes `[154]`--`[156]`, `lem:cold-bounded-germ-trichotomy` and
`lem:cold-increment-arithmetic`

Every length-changing cold bounded germ of the current residual is hit-realized
(G1, refuted by the selection's target avoidance), hit-distinguished (G2, a
target-defective identification, routed to the target-defect ledger), or silent
(G3, a target-complete compression of a proper support, refuted by
`cor:uncompressible`).  The increment arithmetic clauses are the framework's
`ColdIncrementArithmetic` lemmas.  The routed conclusion `K .coldGermRouted` is
G2 for every surviving length-changing germ. -/
@[reducible] noncomputable def coldGermTrichotomyRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermTrichotomy
    { Requires := [K .coldGermCandidates, K .selection, K .uncompressible]
      Produces := [K .coldGermRealized, K .coldGermDistinguished,
        K .coldGermSilent, K .coldGermRouted]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      let candidates := (inputs.get (K .coldGermCandidates)).down
      let selected := (inputs.get (K .selection)).down
      let uncompressible := (inputs.get (K .uncompressible)).down
      let targetInvariant : Graph.FiniteObject.IsomorphismInvariant
          (Graph.HasCycleWithLength data.LengthOK) :=
        (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
      let notRealizing : ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) inputs.current.object,
          ¬ germ.Realizing :=
        fun germ realizing =>
          selected.1 (germ.target_of_realizing targetInvariant realizing)
      let notSilent : ∀ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) inputs.current.object,
          germ.increment < 0 → ¬ germ.Neutral :=
        fun germ shorter neutral =>
          uncompressible germ.support
            (germ.compressibleSupport_of_not_distinguishing shorter neutral.2)
      .cons (key := K .coldGermRealized)
        ⟨⟨candidates, notRealizing, fun germ => germ.trichotomy⟩⟩
        (.cons (key := K .coldGermDistinguished)
          ⟨⟨candidates, fun germ Profile profile distinguishing =>
            germ.not_targetComplete_of_distinguishing profile distinguishing⟩⟩
          (.cons (key := K .coldGermSilent)
            ⟨⟨notSilent,
              fun germ => germ.not_lengthChanging_iff,
              fun increment base copies length positive overlapping lower upper
                  accepted =>
                Graph.ColdCorridor.exists_not_survivesSmear_of_mem_interval
                  positive overlapping lower upper accepted,
              fun increment base exponent residue positive small reached congruent
                  accepted =>
                Graph.ColdCorridor.exists_not_survivesSmear_of_pow_congruent
                  positive small reached congruent accepted,
              fun increment base _ wide criterion =>
                Graph.ColdCorridor.exists_hit_of_orderOf_lt (base := base) wide criterion,
              fun transient exponent odd past =>
                Graph.ColdCorridor.pow_mod_of_le past⟩⟩
            (.cons (key := K .coldGermRouted)
              ⟨⟨candidates, fun germ shorter =>
                have distinguishing :=
                  Graph.ColdCorridor.boundedGerm_not_survives notRealizing notSilent
                    germ shorter
                ⟨distinguishing,
                  fun Profile profile =>
                    germ.not_targetComplete_of_distinguishing profile distinguishing,
                  Or.inl distinguishing⟩⟩⟩
              .nil))))

/-! ## Node `[157]`, `lem:cold-same-interface-table` and
`lem:cold-short-self-return-filter`

Every row of the finite same-interface table is routed: no row is realizing, and
a row is handed off or distinguishing (a row that is neither is a compression of
its own proper support, excluded at `[14]`); the short self-return exceptions
survive their smear and are routed the same way; and the table is finite. -/
@[reducible] noncomputable def coldSameInterfaceTableRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldSameInterfaceTable
    { Requires := [K .coldGermCandidates, K .selection, K .uncompressible]
      Produces := [K .coldSameInterfaceTable]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let candidates := (inputs.get (K .coldGermCandidates)).down
      let selected := (inputs.get (K .selection)).down
      let uncompressible := (inputs.get (K .uncompressible)).down
      let targetInvariant : Graph.FiniteObject.IsomorphismInvariant
          (Graph.HasCycleWithLength data.LengthOK) :=
        (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
      .cons (key := K .coldSameInterfaceTable)
        ⟨⟨candidates, fun Handoff row =>
            Graph.ColdCorridor.row_closed targetInvariant selected.1
              uncompressible row,
          fun Handoff self =>
            Graph.ColdCorridor.selfReturn_closed targetInvariant selected.1
              uncompressible self,
          fun length failed =>
            Graph.ColdCorridor.exists_accepted_of_not_survivesSmear failed,
          rfl,
          fun Handoff row => row.increment_eq_zero⟩⟩
        .nil)

/-! ## Node `[168]`: the stub structure of the ambient-cubic cold windows

`lem:cold-window-stub-excess` counted `15` external stubs per ambient-cubic
window; here they are located: the two path endpoints carry `δ − 1` stubs each
and every interior vertex carries `δ − 2` (`Graph/WindowStubStructure.lean`).
This is what the symmetric-pair analysis of the dense residual charges: two
internally disjoint strands leaving one attachment vertex need two stubs there,
so a genuine symmetric strand pair attaches only at endpoints, a window
carries at most one, and the `(order − 2)(δ − 2)` interior stubs are asymmetric
single-stub attachments. -/
@[reducible] noncomputable def coldWindowStubStructureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldWindowStubStructure
    { Requires := [K .hotColdPartition]
      Produces := [K .coldWindowStubStructure]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let split := (inputs.get (K .hotColdPartition)).down
      .cons (key := K .coldWindowStubStructure)
        ⟨by
          classical
          intro window member
          have windowMem : window ∈ canonicalWindowPacking data.toParameters inputs.current.object :=
            Finset.sdiff_subset (Finset.mem_filter.1 member).1
          have cubic : ∀ vertex ∈ window, inputs.current.object.degree vertex = data.threshold :=
            (Finset.mem_filter.1 member).2
          have induces : inputs.current.object.InducesWindow data.windowOrder window :=
            split.1.1 window windowMem
          obtain ⟨ends, endsSubset, endsCard, interior, endpoints⟩ :=
            Graph.FiniteObject.exists_ends_externalNeighbours window
              data.three_le_windowOrder induces cubic
          exact ⟨ends, endsSubset, endsCard, interior, endpoints,
            Graph.FiniteObject.interior_stubs_le_asymmetric window
              data.three_le_windowOrder induces cubic⟩⟩
        .nil)

/-! ## Node `[169]`, `def:blocked-class`: the trivial neutral-configuration residual

*"On the trivial neutral-configuration residual, `G ∈ 𝓑(𝒫)`, and every window of `G` is
blocked at every scale."*  The row publishes exactly that: the object's own
labelled skeleton has the baseline minimum degree, contains every packed window
at its labelled position, and — the object having no accepted cycle at all
(`K .selection`) — no accepted cycle passes through a window; and the blocked
class is dominated by the skeleton budget (`lem:skeleton-dominates`,
`rem:blocked-class-checks` (a): the class is the *near-cubic* one).  Nodes
`[170]`--`[172]` (`lem:scale-additivity`, `lem:blocked-graphs-compress`,
`lem:system-increment-arithmetic`) are stated over this class. -/
@[reducible] noncomputable def blockedClassRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.blockedClassMember
    { Requires := [K .selection, K .hotColdPartition,
        K .coldCanonicalReplacementTrivial]
      Produces := [K .blockedClassMember]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let avoids := (inputs.get (K .selection)).down.1
      let split := (inputs.get (K .hotColdPartition)).down
      let _trivial :=
        (inputs.get (K .coldCanonicalReplacementTrivial)).down
      .cons (key := K .blockedClassMember)
        ⟨Graph.BlockedClass.minDegree_objectSkeleton inputs.current.object data.threshold
            inputs.current.baseline,
          Graph.BlockedClass.objectSkeleton_blocked inputs.current.object data.windowOrder
            data.LengthOK (canonicalWindowPacking data.toParameters inputs.current.object) split.1 avoids,
          Graph.BlockedClass.card_blocked_le_skeletonBudget inputs.current.object
            data.threshold data.windowOrder data.LengthOK _⟩
        .nil)

/-- **Node `[154]`, `lem:cold-bounded-germ-trichotomy`, first binary test (G1).**
Is some configuration of node `[153]`'s extracted active family hit-realized?
The no-arm is the literal negation on the same family. -/
noncomputable def coldGermRealizationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    (someFresh : K .coldGermSomeRealizing ∉ known)
    (noneFresh : K .coldGermNoneRealizing ∉ known) :
    Decision (K .coldGermSomeRealizing) (K .coldGermNoneRealizing) previous := by
  classical
  exact Decision.run previous (K .coldGermSomeRealizing) (K .coldGermNoneRealizing)
    `Hypostructure.Graph.Strategy.Spine.coldGermRealizationDichotomy
    (if hit : ColdGermSomeRealizingStatement data.toParameters current.object then
      .inl ⟨hit⟩
    else
      .inr ⟨hit⟩)
    someFresh noneFresh

/-- **Node `[154]`, second binary test on the no-G1 arm (G2).**  Is some active
configuration hit-distinguished?  The no-arm is its literal negation: every
active configuration is silent (G3 or the equal-length table, `[157]`). -/
noncomputable def coldGermDistinctionDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    (someFresh : K .coldGermSomeDistinguishing ∉ known)
    (noneFresh : K .coldGermNoneDistinguishing ∉ known) :
    Decision (K .coldGermSomeDistinguishing) (K .coldGermNoneDistinguishing)
      previous := by
  classical
  exact Decision.run previous (K .coldGermSomeDistinguishing)
    (K .coldGermNoneDistinguishing)
    `Hypostructure.Graph.Strategy.Spine.coldGermDistinctionDichotomy
    (if hit : ColdGermSomeDistinguishingStatement data.toParameters current.object then
      .inl ⟨hit⟩
    else
      .inr ⟨hit⟩)
    someFresh noneFresh

end Hypostructure.Graph.Strategy.Spine
