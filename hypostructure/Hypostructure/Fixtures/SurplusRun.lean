import Hypostructure.Graph.Strategy.SpineContinuationRun

/-!
# Fixture: the sparse surplus activation block, run end to end

`Spine.runSparseActivation` is quantified over the keys it consumes and
produces.  This fixture installs it at the spine's *own* vocabulary, on the
literal exit ledger of node `[19]`'s above arm that `Spine.runChapterOne`
reaches, and checks the three things the audit's Ledger, Transport and Residual
columns claim:

* the block elaborates against that branch cursor, with both prerequisites --
  the node-`[1]`--`[4]` selection entry and node `[10]`'s slack independence --
  discharged by resolution against the incoming index;
* the output index is the incoming one with the seven activation facts on top,
  so every earlier fact of the branch is still in the type;
* the audit accounts for every fact with chronological commits and no semantic
  fact was committed twice.

Nothing here is specific to one manuscript: the run is at the framework's own
`Spine.Data`, left as a parameter.
-/

namespace Hypostructure.Fixtures.SurplusRun

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- The key index the branch carries after the block, over node `[19]`'s above
arm. -/
abbrev activatedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  Hypostructure.Graph.Strategy.Spine.sparseActivationKeys
    (surplusAboveKeys (BranchState := BranchState)
      (presentation := presentation) (data := data))

/-- **The block is entered by the entry spine, not merely runnable on its
cursor.**

`Spine.runChapterOne` calls `Spine.runCore` once and continues node `[19]`'s
above arm through `[125]`--`[144]` before exposing a continuation.  This is the
check that the branch is attached to the one graph. -/
noncomputable def attached
    (T : Core.Target (problem BranchState Presentation presentation data))
    (targetPredicate : T.Predicate = Graph.HasCycleWithLength data.LengthOK)
    (opened : OpenedScope
      (P := problem BranchState Presentation presentation data) (K .selection))
    (sufficientlyLarge :
      Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
        data.dischargeScale data.windowOrder data.windowRate data.spineScale
        opened.selected.object.vertexCount) :
    ChapterOneContinuation opened.selected :=
  runChapterOne T targetPredicate opened sufficientlyLarge

/-- **The block runs on the accumulated surplus/package residual reaching
node `[125]`.** -/
noncomputable def run
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected surplusAbovePackageKeys) :
    SurplusResult selected surplusAbovePackageKeys :=
  runSurplusBranch history

/-- **The seven facts of the block are all on the ledger after it runs.**

Membership rather than position: later blocks add their own facts to the same
index, and this check is about what the activation block contributes. -/
theorem run_audit_contains_activation_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected activatedKeys) :
    ∀ fact ∈ [(name .sparseSlackSurplus),
        (name .activeSurplusFamily),
        (name .sparsePortActivation),
        (name .baselineSpineDemand),
        (name .canonicalPairLedger),
        (name .sparseUpperEnvelope),
        (name .capacityTokenLedger)],
      fact ∈ (ExactLedger.audit history).facts := by
  intro fact member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.mem_map.mpr ⟨K .sparseSlackSurplus, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .activeSurplusFamily, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .sparsePortActivation, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .baselineSpineDemand, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .canonicalPairLedger, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .sparseUpperEnvelope, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .capacityTokenLedger, by simp, rfl⟩

/-- **Each geometric arm carries its own class verdict and its own audit.**

`[140]`'s arm carries the window-incidence verdict and audit, `[142]`'s the
remainder-surplus pair, and `[143]`'s the primitive-carrier pair together with
the two negative verdicts it was derived from.  The checks are membership in the
arm's own key index, which is what makes a cross-arm read fail to elaborate. -/
theorem window_arm_carries_its_audit
    {known : FactKeys (Input BranchState Presentation presentation data)} :
    K (data := data) .windowClassOverload ∈
        Hypostructure.Graph.Strategy.Spine.windowAuditKeys known ∧
      K (data := data) .windowIncidenceAudit ∈
        Hypostructure.Graph.Strategy.Spine.windowAuditKeys known ∧
      K (data := data) .quantitativeOverload ∈
        Hypostructure.Graph.Strategy.Spine.windowAuditKeys known := by
  refine ⟨by simp, by simp, by simp⟩

theorem remainder_arm_carries_its_audit
    {known : FactKeys (Input BranchState Presentation presentation data)} :
    K (data := data) .windowClassAbsent ∈
        Hypostructure.Graph.Strategy.Spine.remainderAuditKeys known ∧
      K (data := data) .remainderClassOverload ∈
        Hypostructure.Graph.Strategy.Spine.remainderAuditKeys known ∧
      K (data := data) .remainderSurplusAudit ∈
        Hypostructure.Graph.Strategy.Spine.remainderAuditKeys known := by
  refine ⟨by simp, by simp, by simp⟩

theorem primitive_arm_carries_its_audit
    {known : FactKeys (Input BranchState Presentation presentation data)} :
    K (data := data) .windowClassAbsent ∈
        Hypostructure.Graph.Strategy.Spine.primitiveAuditKeys known ∧
      K (data := data) .remainderClassAbsent ∈
        Hypostructure.Graph.Strategy.Spine.primitiveAuditKeys known ∧
      K (data := data) .primitiveClassOverload ∈
        Hypostructure.Graph.Strategy.Spine.primitiveAuditKeys known ∧
      K (data := data) .primitiveCarrierAudit ∈
        Hypostructure.Graph.Strategy.Spine.primitiveAuditKeys known := by
  refine ⟨by simp, by simp, by simp, by simp⟩

/-- **No arm can read another arm's audit.**  The window arm's index does not
contain the remainder-surplus or primitive-carrier audits, so the cross-arm read
is not a missing hypothesis but a type error. -/
theorem window_arm_omits_the_other_audits
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (fresh : K (data := data) .remainderSurplusAudit ∉ known)
    (freshPrimitive : K (data := data) .primitiveCarrierAudit ∉ known) :
    K (data := data) .remainderSurplusAudit ∉
        Hypostructure.Graph.Strategy.Spine.windowAuditKeys known ∧
      K (data := data) .primitiveCarrierAudit ∉
        Hypostructure.Graph.Strategy.Spine.windowAuditKeys known := by
  refine ⟨by simp [fresh], by simp [freshPrimitive]⟩

/-- **Node `[144]` closes each geometric arm two ways, and the two are
disjoint.**

The caps arm carries `homogeneousCapsHold` and the near-cubic close; the
bottleneck arm carries `homogeneousBottleneckPattern` and neither of them.  A
consumer of one cannot read the other: it is not in its type. -/
theorem caps_arm_and_bottleneck_arm_are_disjoint
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (capsFresh : K (data := data) .homogeneousCapsHold ∉ known)
    (closeFresh : K (data := data) .homogeneousBottleneck ∉ known)
    (patternFresh : K (data := data) .homogeneousBottleneckPattern ∉ known) :
    (K (data := data) .homogeneousCapsHold ∈
        Hypostructure.Graph.Strategy.Spine.capsClosedKeys
          (Hypostructure.Graph.Strategy.Spine.windowAuditKeys known) ∧
      K (data := data) .homogeneousBottleneck ∈
        Hypostructure.Graph.Strategy.Spine.capsClosedKeys
          (Hypostructure.Graph.Strategy.Spine.windowAuditKeys known)) ∧
    (K (data := data) .homogeneousBottleneckPattern ∈
        Hypostructure.Graph.Strategy.Spine.bottleneckKeys
          (Hypostructure.Graph.Strategy.Spine.windowAuditKeys known) ∧
      K (data := data) .homogeneousBottleneck ∉
        Hypostructure.Graph.Strategy.Spine.bottleneckKeys
          (Hypostructure.Graph.Strategy.Spine.windowAuditKeys known) ∧
      K (data := data) .homogeneousCapsHold ∉
        Hypostructure.Graph.Strategy.Spine.bottleneckKeys
          (Hypostructure.Graph.Strategy.Spine.windowAuditKeys known)) := by
  refine ⟨⟨by simp, by simp⟩, by simp, by simp [closeFresh], by simp [capsFresh]⟩

/-- **Every fact of the block is accounted for by a chronological commit.** -/
theorem run_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected activatedKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **No semantic fact was committed twice.** -/
theorem run_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected activatedKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

/-- **No commit is empty.** -/
theorem run_audit_commits_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected activatedKeys) :
    ((ExactLedger.audit history).commits.Forall
      fun record => record.produced ≠ []) :=
  ExactLedger.audit_commits_nonempty history

end Hypostructure.Fixtures.SurplusRun
