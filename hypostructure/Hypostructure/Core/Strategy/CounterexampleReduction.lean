import Hypostructure.Core.Strategy.Data
import Hypostructure.Core.Strategy.TargetAlgebraReduction
import Hypostructure.Core.Strategy.MinimalSubobjectExclusion
import Hypostructure.Core.Strategy.CriticalModificationStructure

/-!
# Standard structural continuation of a minimal counterexample

This module only concatenates the three sealed, domain-neutral Strategies.
Every inherited fact is read through a typed query and every new fact is
appended to the literal predecessor ledger.
-/

namespace Hypostructure.Core.Strategy.CounterexampleReduction

open Hypostructure
open Hypostructure.Core.Residual

universe uAmbient uBranch uData

variable {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}

/-- CT1 target encoding pulled back to the exact selected context. -/
noncomputable def targetContract
    (data : Core.CounterexampleReductionData.{uAmbient, uBranch, uData} P T)
    {Previous : Type (max uAmbient uBranch uData)}
    (context : Query Previous fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        data.selection.progress) :
    TargetAlgebraReduction.Contract Previous where
  PublicTarget := fun previous =>
    T.Predicate (context previous).G
  encoding := {
    Code := fun previous => data.Code (context previous).G
    Accepts := fun previous code =>
      data.Accepts (context previous).G code
    encode := fun {previous} target =>
      (data.target_iff_code (context previous).G).mp target
    decode := fun {previous code} accepted =>
      (data.target_iff_code (context previous).G).mpr
        ⟨code, accepted⟩
    acceptsDecidable := fun previous code =>
      data.acceptsDecidable (context previous).G code
  }
  avoids :=  fun previous =>
    (context previous).avoids

abbrev TargetStage
    (data : Core.CounterexampleReductionData.{uAmbient, uBranch, uData} P T)
    {Previous : Type (max uAmbient uBranch uData)}
    (context : Query Previous fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        data.selection.progress) :=
  (targetContract data context).Stage

/-- Preserve the selected context through CT1's decision and avoiding
extensions. -/
def contextAfterTarget
    (data : Core.CounterexampleReductionData.{uAmbient, uBranch, uData} P T)
    {Previous : Type (max uAmbient uBranch uData)}
    (context : Query Previous fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        data.selection.progress) :
    Query (TargetStage data context) fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        data.selection.progress :=
  context.preserve.preserve

abbrev MinimalStage
    (data : Core.CounterexampleReductionData.{uAmbient, uBranch, uData} P T)
    {Previous : Type (max uAmbient uBranch uData)}
    (context : Query Previous fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        data.selection.progress) :=
  MinimalSubobjectExclusion.DirectStage data.subobjectProfile
    (contextAfterTarget data context)

/-- Preserve the selected context through the minimal-subobject extension. -/
def contextAfterMinimal
    (data : Core.CounterexampleReductionData.{uAmbient, uBranch, uData} P T)
    {Previous : Type (max uAmbient uBranch uData)}
    (context : Query Previous fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        data.selection.progress) :
    Query (MinimalStage data context) fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        data.selection.progress :=
  (contextAfterTarget data context).preserve

/-- Instantiate the generic atomic-modification Strategy from residual-owned
problem semantics. -/
def criticalSemantics
    (data : Core.CounterexampleReductionData.{uAmbient, uBranch, uData} P T)
    {Previous : Type (max uAmbient uBranch uData)}
    (context : Query Previous fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        data.selection.progress) :
    CriticalModificationStructure.Semantics
      (P := P) (Target := T.Predicate)
      (progress := data.selection.progress)
      (Subobject := data.Subobject)
      (profile := data.subobjectProfile) Previous where
  context := context
  Atomic := fun previous =>
    ULift.{max uAmbient uBranch uData, uAmbient}
      (data.Atomic (context previous).G)
  Tight := fun previous =>
    ULift.{max uAmbient uBranch uData, uAmbient}
      (data.Carrier (context previous).G)
  Slack := fun previous =>
    ULift.{max uAmbient uBranch uData, uAmbient}
      (data.Carrier (context previous).G)
  Related := fun previous =>
    fun left right =>
      data.Related (context previous).G left.down right.down
  Critical := fun previous =>
    fun atomic => data.Critical (context previous).G atomic.down
  subobject := fun _previous =>
    fun atomic => data.atomicSubobject atomic.down
  baseline_of_not_critical := fun previous atomic noncritical =>
    data.baseline_of_not_critical
      (context previous).baseline atomic.down noncritical
  atomic_of_related := fun _previous =>
    fun left right related =>
      ULift.up (data.atomic_of_related left.down right.down related)
  noncritical_of_related := fun _previous =>
    fun left right related =>
      data.noncritical_of_related left.down right.down related

def noSubobjectQuery
    (data : Core.CounterexampleReductionData.{uAmbient, uBranch, uData} P T)
    {Previous : Type (max uAmbient uBranch uData)}
    (context : Query Previous fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        data.selection.progress) :
    CriticalModificationStructure.NoSubobjectQuery
      (criticalSemantics data (contextAfterMinimal data context)) :=
  MinimalSubobjectExclusion.directCertificateQuery
    data.subobjectProfile (contextAfterTarget data context)

abbrev FinalStage
    (data : Core.CounterexampleReductionData.{uAmbient, uBranch, uData} P T)
    {Previous : Type (max uAmbient uBranch uData)}
    (context : Query Previous fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        data.selection.progress) :=
  let semantics := criticalSemantics data (contextAfterMinimal data context)
  let noSubobject := noSubobjectQuery data context
  CriticalModificationStructure.Stage semantics noSubobject

/-- Execute all three Strategies in order on the literal selected stage. -/
noncomputable def execute
    (data : Core.CounterexampleReductionData.{uAmbient, uBranch, uData} P T)
    {Previous : Type (max uAmbient uBranch uData)}
    (context : Query Previous fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        data.selection.progress)
    (previous : Previous) : FinalStage data context :=
  let targetStage := (targetContract data context).execute previous
  let minimalContext := contextAfterTarget data context
  let minimalStage :=
    MinimalSubobjectExclusion.executeDirect data.subobjectProfile
      minimalContext targetStage
  let inheritedContext := contextAfterMinimal data context
  let semantics := criticalSemantics data inheritedContext
  let noSubobject := noSubobjectQuery data context
  CriticalModificationStructure.run semantics noSubobject minimalStage

def contextAfterCritical
    (data : Core.CounterexampleReductionData.{uAmbient, uBranch, uData} P T)
    {Previous : Type (max uAmbient uBranch uData)}
    (context : Query Previous fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        data.selection.progress) :
    Query (FinalStage data context) fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate
        data.selection.progress :=
  (contextAfterMinimal data context).preserve.preserve

end Hypostructure.Core.Strategy.CounterexampleReduction
