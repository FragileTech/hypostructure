import Hypostructure.CT7.Automation
import Hypostructure.PDE.Model
import Hypostructure.Core.Residual.Query

/-!
# PDE specialization of CT7

The PDE adapter interprets representatives as local terms and semantic
contexts as compatible tails assembled by addition.  It introduces no PDE
search, classifier, route, or generated output.
-/

namespace Hypostructure.PDE.CT7

universe uPrevious u uContext uCoordinate

/-- Exact Boolean target responses for additive local/tail assembly. -/
noncomputable abbrev targetSystem
    (M : LocalModel.{u}) [Add M.problem.Ambient]
    (Target : M.problem.Ambient -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (tail : Context -> M.problem.Ambient)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context) :
    Core.Response.System M.problem.Ambient :=
  Core.Response.System.ofDecodedContexts Context Coordinate Bool
    (fun atom context =>
      @decide (Target (atom + tail context))
        (decideTarget (atom + tail context)))
    decode

/-- Exact target meaning of the additive Boolean response. -/
noncomputable def targetSemantics
    (M : LocalModel.{u}) [Add M.problem.Ambient]
    (Target : M.problem.Ambient -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (tail : Context -> M.problem.Ambient)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context) :
    Core.Response.TargetSemantics
      (targetSystem M Target decideTarget Context tail Coordinate decode) where
  TargetResponse := fun atom context => Target (atom + tail context)
  Accepts := fun response => response = true
  target_iff_accepts := by
    intro atom context
    change Target (atom + tail context) ↔
      @decide (Target (atom + tail context))
        (decideTarget (atom + tail context)) = true
    exact decide_eq_true_iff.symm

/-- Interpret CT7 realization as reaching the PDE target after exact additive
local/tail assembly. -/
noncomputable abbrev targetSpec
    (Previous : Type uPrevious)
    (M : LocalModel.{u}) [Add M.problem.Ambient]
    (Target : M.problem.Ambient -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (tail : Context -> M.problem.Ambient)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context) :
    _root_.Hypostructure.CT7.Spec Previous where
  Representative := M.problem.Ambient
  system := targetSystem M Target decideTarget Context tail Coordinate decode
  Realizes := fun _previous atom context => Target (atom + tail context)

/-- Build the complete CT7 capability from a residual-owned exact context
schedule. -/
noncomputable def targetCapabilityOfExactContexts
    {Previous : Type uPrevious}
    (M : LocalModel.{u}) [Add M.problem.Ambient]
    {Target : M.problem.Ambient -> Prop}
    (decideTarget : forall object, Decidable (Target object))
    {Context : Type uContext}
    {tail : Context -> M.problem.Ambient}
    {Coordinate : Type uCoordinate}
    {decode : Coordinate -> Context}
    (representatives : Core.Residual.Query Previous fun _previous =>
      Core.Response.Representatives M.problem.Ambient)
    (contexts : Core.Residual.Query Previous fun _previous =>
      Core.Finite.Enumeration Coordinate)
    (complete : (previous : Previous) -> (context : Context) ->
      Exists fun index : Fin (contexts previous).card =>
        context = decode ((contexts previous).get index)) :
    _root_.Hypostructure.CT7.Capability
      (targetSpec Previous M Target decideTarget Context tail Coordinate
        decode) :=
  _root_.Hypostructure.CT7.Capability.ofExactContexts representatives contexts
    (by
      change DecidableEq Bool
      infer_instance)
    (fun previous coordinate =>
      decideTarget ((representatives previous).source +
        tail (decode coordinate)))
    complete

/--
Build the existing CT7 local-context capability from a represented
equation-state query.  The wrapper only maps that query to CT7
representatives; all response classification, replacement semantics, and
routing remain in CT7/Core.
-/
noncomputable def targetCapabilityOfEquationState
    {Previous : Type uPrevious}
    (M : LocalModel.{u}) [Add M.problem.Ambient]
    (window : Previous → M.atlas.Window)
    (state : Core.Residual.Query Previous fun previous =>
      EquationState M.equation (window previous))
    {Target : M.problem.Ambient → Prop}
    (decideTarget : ∀ object, Decidable (Target object))
    {Context : Type uContext}
    {tail : Context → M.problem.Ambient}
    {Coordinate : Type uCoordinate}
    {decode : Coordinate → Context}
    (representatives :
      (previous : Previous) →
        EquationState M.equation (window previous) →
          Core.Response.Representatives M.problem.Ambient)
    (contexts : Core.Residual.Query Previous fun _ =>
      Core.Finite.Enumeration Coordinate)
    (complete : (previous : Previous) → (context : Context) →
      ∃ index : Fin (contexts previous).card,
        context = decode ((contexts previous).get index)) :
    _root_.Hypostructure.CT7.Capability
      (targetSpec Previous M Target decideTarget Context tail Coordinate
        decode) :=
  targetCapabilityOfExactContexts M decideTarget
    (state.map fun previous equationState =>
      representatives previous equationState)
    contexts complete

section TerminalSemantics

variable {Previous : Type uPrevious}
  {M : LocalModel.{u}} [Add M.problem.Ambient]
  {Target : M.problem.Ambient -> Prop}
  {decideTarget : forall object, Decidable (Target object)}
  {Context : Type uContext}
  {tail : Context -> M.problem.Ambient}
  {Coordinate : Type uCoordinate}
  {decode : Coordinate -> Context}

local notation "pdeSpec" =>
  targetSpec Previous M Target decideTarget Context tail Coordinate decode

/-- A PDE CT7 realization certificate reaches the target in its selected
local/tail context. -/
theorem realization_target
    {capability : _root_.Hypostructure.CT7.Capability pdeSpec}
    {previous : Previous}
    (certificate : _root_.Hypostructure.CT7.RealizationCertificate capability
      previous) :
    Target ((capability.representativesAt previous).source +
      tail certificate.context) :=
  certificate.realizes

/-- A PDE CT7 neutral certificate transports the target through every exact
additive tail context. -/
theorem neutrality_target_iff
    {capability : _root_.Hypostructure.CT7.Capability pdeSpec}
    {previous : Previous}
    (certificate : _root_.Hypostructure.CT7.NeutralityCertificate capability
      previous)
    (context : Context) :
    Target ((capability.representativesAt previous).source + tail context) ↔
      Target ((capability.representativesAt previous).replacement +
        tail context) := by
  change
    (targetSemantics M Target decideTarget Context tail Coordinate decode).TargetResponse
        (capability.representativesAt previous).source context ↔
      (targetSemantics M Target decideTarget Context tail Coordinate decode).TargetResponse
        (capability.representativesAt previous).replacement context
  exact certificate.target_iff
    (targetSemantics M Target decideTarget Context tail Coordinate decode)
    context

end TerminalSemantics

end Hypostructure.PDE.CT7
