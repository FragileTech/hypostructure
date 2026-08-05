import Hypostructure.Core.Minimality

/-!
# Critical atomic-modification structure

This domain-neutral composition reads a minimal-counterexample context and
its no-subobject certificate from the literal incoming stage.  It appends
universal atomic criticality and then tight/slack incompatibility.  Every
subobject and certificate remains indexed by the exact context returned by
the incoming typed query.
-/

namespace Hypostructure.Core.Strategy.CriticalModificationStructure

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.Residual

universe uAmbient uPrevious uBranch uMeasure uSubobject

/-- Primitive domain semantics.  The context is an inherited ledger query,
not a detached or globally fixed value. -/
structure Semantics
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject}
    (Previous : Type uPrevious) where
  context :
    Query Previous (fun _ =>
      Core.MinimalCounterexampleContext P Target progress)
  Atomic : Previous → Type uPrevious
  Tight : Previous → Type uPrevious
  Slack : Previous → Type uPrevious
  Related : (previous : Previous) →
    Tight previous → Slack previous → Prop
  Critical : (previous : Previous) → Atomic previous → Prop
  subobject : (previous : Previous) →
    Atomic previous → Subobject (context previous).G
  baseline_of_not_critical :
    ∀ (previous : Previous) (modification : Atomic previous),
      ¬ Critical previous modification →
        P.Baseline
          (profile.toAmbient (subobject previous modification))
  atomic_of_related :
    ∀ (previous : Previous) (tight : Tight previous)
      (slack : Slack previous),
      Related previous tight slack → Atomic previous
  noncritical_of_related :
    ∀ (previous : Previous) (tight : Tight previous)
      (slack : Slack previous) (related : Related previous tight slack),
        ¬ Critical previous
          (atomic_of_related previous tight slack related)

/-- The no-subobject certificate query required by this composition. -/
abbrev NoSubobjectQuery
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject}
    {Previous : Type uPrevious}
    (semantics : Semantics
      (P := P) (Target := Target) (progress := progress)
      (Subobject := Subobject) (profile := profile) Previous) :=
  Query Previous (fun previous =>
    Core.Minimality.NoSubobjectBaselineCertificate profile
      (semantics.context previous))

/-- First appended output: every incoming-stage atomic modification is
critical. -/
structure CriticalityLedger
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject}
    {Previous : Type uPrevious}
    (semantics : Semantics
      (P := P) (Target := Target) (progress := progress)
      (Subobject := Subobject) (profile := profile) Previous)
    (previous : Previous) : Type uPrevious where
  critical :
    ∀ modification : semantics.Atomic previous,
      semantics.Critical previous modification

/-- Second appended output: the incoming-stage tight and slack carriers are
incompatible under the supplied relation. -/
structure SlackIncompatibilityLedger
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject}
    {Previous : Type uPrevious}
    (semantics : Semantics
      (P := P) (Target := Target) (progress := progress)
      (Subobject := Subobject) (profile := profile) Previous)
    (previous : Previous) : Type uPrevious where
  incompatible :
    ∀ (tight : semantics.Tight previous)
      (slack : semantics.Slack previous),
      ¬ semantics.Related previous tight slack

/-- Read the context and matching no-subobject certificate from the same
literal predecessor, then derive universal atomic criticality. -/
def criticalityNode
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject}
    {Previous : Type uPrevious}
    (semantics : Semantics
      (P := P) (Target := Target) (progress := progress)
      (Subobject := Subobject) (profile := profile) Previous)
    (noSubobject : NoSubobjectQuery semantics) :
    StageNode Previous (CriticalityLedger semantics) :=
  StageNode.derive (semantics.context.and noSubobject)
    fun previous inherited =>
      {
        critical := by
          intro modification
          by_contra noncritical
          exact inherited.snd.excludes
            (semantics.subobject previous modification)
            (semantics.baseline_of_not_critical
              previous modification noncritical)
      }

/-- Exact ledger shape after criticality has been appended. -/
abbrev CriticalityStage
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject}
    {Previous : Type uPrevious}
    (semantics : Semantics
      (P := P) (Target := Target) (progress := progress)
      (Subobject := Subobject) (profile := profile) Previous)
    (_noSubobject : NoSubobjectQuery semantics) :=
  Ledger.Extension Previous
    (CriticalityLedger semantics)

/-- Query the criticality value added by the first adapter. -/
def criticalityQuery
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject}
    {Previous : Type uPrevious}
    (semantics : Semantics
      (P := P) (Target := Target) (progress := progress)
      (Subobject := Subobject) (profile := profile) Previous)
    (noSubobject : NoSubobjectQuery semantics) :
    Query (CriticalityStage semantics noSubobject)
      (fun stage => CriticalityLedger semantics stage.previous) :=
  Query.latest

/-- Preserve the inherited context query through the first extension. -/
def contextAfterCriticality
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject}
    {Previous : Type uPrevious}
    (semantics : Semantics
      (P := P) (Target := Target) (progress := progress)
      (Subobject := Subobject) (profile := profile) Previous)
    (noSubobject : NoSubobjectQuery semantics) :
    Query (CriticalityStage semantics noSubobject)
      (fun _stage =>
        Core.MinimalCounterexampleContext P Target progress) :=
  semantics.context.preserve

/-- Derive relation incompatibility from the criticality value already
stored in the exact predecessor extension. -/
def slackIncompatibilityNode
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject}
    {Previous : Type uPrevious}
    (semantics : Semantics
      (P := P) (Target := Target) (progress := progress)
      (Subobject := Subobject) (profile := profile) Previous)
    (noSubobject : NoSubobjectQuery semantics) :
    StageNode (CriticalityStage semantics noSubobject)
      (fun stage =>
        SlackIncompatibilityLedger semantics stage.previous) :=
  StageNode.derive
    ((contextAfterCriticality semantics noSubobject).and
      (criticalityQuery semantics noSubobject))
    fun stage inherited =>
      {
        incompatible := by
          intro tight slack related
          exact
            (semantics.noncritical_of_related
              stage.previous tight slack related)
            (inherited.snd.critical
              (semantics.atomic_of_related
                stage.previous tight slack related))
      }

/-- Exact final ledger shape after both theorem nodes. -/
abbrev Stage
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject}
    {Previous : Type uPrevious}
    (semantics : Semantics
      (P := P) (Target := Target) (progress := progress)
      (Subobject := Subobject) (profile := profile) Previous)
    (noSubobject : NoSubobjectQuery semantics) :=
  Ledger.Extension (CriticalityStage semantics noSubobject)
    (fun stage => SlackIncompatibilityLedger semantics stage.previous)

/-- Execute both stages and retain the complete predecessor chain. -/
def run
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    {profile :
      Core.Minimality.SubobjectMinimalityProfile
        (P := P) Target progress Subobject}
    {Previous : Type uPrevious}
    (semantics : Semantics
      (P := P) (Target := Target) (progress := progress)
      (Subobject := Subobject) (profile := profile) Previous)
    (noSubobject : NoSubobjectQuery semantics)
    (previous : Previous) : Stage semantics noSubobject :=
  let criticality :=
    (criticalityNode semantics noSubobject).run previous
  (slackIncompatibilityNode semantics noSubobject).run criticality

end Hypostructure.Core.Strategy.CriticalModificationStructure
