import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Nodes `[13]`--`[14]`: interface replacement

`lem:replacement` and `cor:uncompressible`.  A target-complete compression of a
proper atom would produce a strictly smaller baseline object whose obstruction
profile is contained in the original's; minimality gives that object the target,
context-universality carries the target back through the shared outside
context, and the reconstruction is isomorphic to the selected object, which
avoids the target.

Node `[13]` records the one-way replacement exclusion itself.  Its proof is
performed at the literal residual: the four represented replacement hypotheses
construct the replacement, and the selection fact supplies precisely
minimality and target avoidance.

The node `[13]` executor spells out its argument locally and reads nothing but
the selected context's `avoids` and `target_of_smaller`.  It therefore consumes
the selection fact and nothing else; no closure record, registration, or
payload stands between the fact and its consequence. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def replacementExclusionRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.replacementExclusion
    { Requires := [K .selection]
      Produces := [K .replacementExclusion]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let fact := inputs.get (K .selection)
      let context :
          Core.MinimalCounterexampleContext
            (problem BranchState Presentation presentation data)
            (Graph.HasCycleWithLength data.LengthOK)
            (progress BranchState Presentation presentation data) :=
        { G := inputs.current.object
          baseline := inputs.current.baseline
          state := inputs.current.branchState
          avoids := fact.down.1
          minimal := fact.down.2.sizeMinimal }
      let targetInvariant : Core.TargetInvariant
          (Graph.isomorphismEquivalenceWithPresentation
            (Graph.MinimumDegreeAtLeast data.threshold) BranchState
            Presentation presentation
            (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold))
          (Graph.HasCycleWithLength data.LengthOK) := by
        simpa [Graph.minimumDegreeIsomorphismSemantics] using
          (Graph.minimumDegreeCycleTargetInvariant data.threshold BranchState
            Presentation presentation data.LengthOK)
      let profile :=
        Graph.Strategy.InterfaceReplacement.profileWithPresentation
          (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
          (BranchState := BranchState)
          (baselineInvariant :=
            Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
          Presentation presentation
          (T := Core.Target.ofPredicate _
            (Graph.HasCycleWithLength data.LengthOK)) targetInvariant
      .cons (key := K .replacementExclusion)
        (show Value BranchState Presentation presentation data
            .replacementExclusion inputs.current from
          ⟨fun support replacementSupport => by
            rcases replacementSupport with
              ⟨connected, proper, replacement, signatureEq, baseline, smaller,
                obstructionLE⟩
            let site :=
              Graph.Strategy.InterfaceReplacement.SupportAtom.properAtom
                context.G support connected proper
            let replacement' : profile.assembly.Replacement context.G site :=
              { atom := replacement
                compatible := trivial }
            let strictReplacement : profile.StrictReplacement context site :=
              { replacement := replacement'
                signature_eq := congrArg ULift.up signatureEq
                obstruction_le := by
                  intro outside _ _ replacementTarget
                  exact obstructionLE outside replacementTarget
                baseline := baseline
                smaller := smaller }
            have replacementTarget : Graph.HasCycleWithLength data.LengthOK
                (profile.assembly.replace strictReplacement.replacement) :=
              context.target_of_smaller strictReplacement.smaller
                strictReplacement.baseline
            have sourceTarget : Graph.HasCycleWithLength data.LengthOK
                (profile.assembly.assemble
                  (profile.assembly.atom context.G site)
                  (profile.assembly.context context.G site)) :=
              strictReplacement.obstruction_le
                (profile.assembly.context context.G site)
                (profile.assembly.extractedCompatible context.G site)
                strictReplacement.replacement.compatible replacementTarget
            exact context.avoids
              ((profile.targetInvariant.target_iff
                (profile.assembly.reconstruct context.G site)).mp sourceTarget)⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
