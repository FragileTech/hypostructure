import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdGermRouting

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
      let avoids := (inputs.get (K .selection)).down.1
      let uncompressible := (inputs.get (K .uncompressible)).down
      .cons (key := K .coldGermRealized)
        ⟨Contracts.Spine.coldGermRealized_of_avoids data.toParameters
          inputs.current.object avoids⟩
        (.cons (key := K .coldGermDistinguished)
          ⟨Contracts.Spine.coldGermDistinguished_holds data.toParameters
            inputs.current.object⟩
          (.cons (key := K .coldGermSilent)
            ⟨Contracts.Spine.coldGermSilent_of_uncompressible data.toParameters
              inputs.current.object uncompressible⟩
            (.cons (key := K .coldGermRouted)
              ⟨Contracts.Spine.coldGermRouted_of_uncompressible data.toParameters
                inputs.current.object avoids uncompressible⟩
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
      .cons (key := K .coldSameInterfaceTable)
        ⟨Contracts.Spine.coldSameInterfaceTable_of_uncompressible
          data.toParameters inputs.current.object
          (inputs.get (K .selection)).down.1
          (inputs.get (K .uncompressible)).down⟩
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
      .cons (key := K .coldWindowStubStructure)
        ⟨Contracts.Spine.coldWindowStubStructure_of_split data.toParameters
          inputs.current.object data.three_le_windowOrder
          (inputs.get (K .hotColdPartition)).down⟩
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
    { Requires := [K .selection, K .hotColdPartition]
      Produces := [K .blockedClassMember]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .blockedClassMember)
        ⟨Contracts.Spine.blockedClassMember_of_split data.toParameters
          inputs.current.object inputs.current.baseline
          (inputs.get (K .selection)).down.1
          (inputs.get (K .hotColdPartition)).down⟩
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
