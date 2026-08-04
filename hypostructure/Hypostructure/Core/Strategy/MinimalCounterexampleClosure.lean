import Hypostructure.Core.Strategy.Data
import Hypostructure.Core.Context

/-!
# Domain-neutral minimal-counterexample closure

This module abstracts the *other* recurring proof pattern behind
well-founded compression arguments: "assume `G` is *the* lexicographically
minimal counterexample; [some case analysis]; each case either exhibits a
strictly smaller admissible replacement (contradicting minimality directly)
or is impossible outright." Every one of the paper's own minimal-
counterexample lemmas (`lem:no-silent-global-smearing` and its kin) is
stated exactly this way: about the *selected* minimal object, never about
an arbitrary "stuck" configuration reachable partway through some induction.

`Core.Strategy.WellFoundedCompression.CompressionClosure`'s `baseCase`
instead demands a proof for *every* input where no compression is found,
which is a strictly stronger (and often much harder to discharge)
obligation than what these lemmas actually prove. This module closes that
gap: given a well-founded `progress` measure (already domain-neutral, used
identically by `Hypostructure.Graph.Minimality` and any PDE analogue) and a
"replacement" step compatible with it, Core derives the *entire* well-
ordering selection, the compression-found contradiction, and the assembled
`forall input, Target input.object` theorem automatically. The only content
a caller ever supplies is `noStuckMinimalCounterexample`: a proof that the
*selected* minimal counterexample cannot be stuck (no replacement
available) -- the exact shape of the paper's own arguments, and nothing
more. -/

namespace Hypostructure.Core.Strategy

universe uAmbient uBranch uMeasure

open Hypostructure.Core

/-- A replacement step compatible with a registered well-founded `progress`
measure: given a certificate, the replacement is strictly smaller in
`progress`'s own order (not a separate `Nat` measure that a caller must
show agrees with it), so a certificate found at the minimal counterexample
contradicts minimality directly and generically. -/
structure ProgressCompressionStep
    (P : Core.Problem.{uAmbient, uBranch})
    (progress : Progress.{uAmbient, uBranch, uMeasure} P) where
  Certificate : ProblemInput P -> Type
  /-- The preceding CT pipeline's exhaustive result, if it found a
  compressing certificate. -/
  search : (input : ProblemInput P) -> Option (Certificate input)
  /-- The smaller/simpler residual represented by the certificate. -/
  replacement : (input : ProblemInput P) -> Certificate input -> ProblemInput P
  smaller : (input : ProblemInput P) -> (certificate : Certificate input) ->
    progress.Smaller (replacement input certificate).object input.object

/-- The minimal-counterexample closure: `noStuckMinimalCounterexample` is
the only genuinely problem-specific content, applying only to the object
`progress`'s well-ordering actually selects as minimal -- not to every
input a caller's own recursion might otherwise have to handle. -/
structure MinimalCounterexampleClosure
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (progress : Progress.{uAmbient, uBranch, uMeasure} P) where
  step : ProgressCompressionStep P progress
  /-- Transport a target certificate across one certified replacement. -/
  transport : (input : ProblemInput P) ->
    (certificate : step.Certificate input) ->
    T.Predicate (step.replacement input certificate).object ->
    T.Predicate input.object
  stateOf : (G : P.Ambient) -> P.BranchState G
  /-- The paper's own genuine content: the *selected* minimal counterexample
  cannot be stuck (no replacement certificate available). This is exactly
  the shape of "let `G` be the lexicographically minimal counterexample;
  [derive a contradiction from the case where the descent step is
  unavailable]" -- not a claim about any other configuration. -/
  noStuckMinimalCounterexample :
    (ctx : MinimalCounterexampleContext P T.Predicate progress) ->
    step.search ⟨ctx.G, ctx.baseline, ctx.state⟩ = none -> False

/-- The total target consumer: Core selects the minimal counterexample via
well-ordering, automatically derives a contradiction whenever a replacement
certificate is found there (via `smaller` + `transport`, generically, for
every problem), and otherwise defers to the caller's
`noStuckMinimalCounterexample`. No induction, termination measure, or
recursive descent is exposed to the caller -- the well-ordering selection
already is the only "recursion" this pattern needs. -/
noncomputable def MinimalCounterexampleClosure.close
    (closure : MinimalCounterexampleClosure P T progress) :
    (input : ProblemInput P) -> T.Predicate input.object := by
  intro input
  by_contra hAvoids
  have avoidCtx : AvoidingContext P T.Predicate :=
    AvoidingContext.ofBranch
      { G := input.object, baseline := input.baseline, state := input.branchState }
      hAvoids
  obtain ⟨ctx⟩ :=
    AvoidingContext.exists_minimalCounterexample avoidCtx progress closure.stateOf
  match hsearch : closure.step.search ⟨ctx.G, ctx.baseline, ctx.state⟩ with
  | none => exact closure.noStuckMinimalCounterexample ctx hsearch
  | some certificate =>
    have hNotTarget :
        ¬ T.Predicate
          (closure.step.replacement ⟨ctx.G, ctx.baseline, ctx.state⟩ certificate).object := by
      intro hTarget
      exact ctx.avoids
        (closure.transport ⟨ctx.G, ctx.baseline, ctx.state⟩ certificate hTarget)
    exact ctx.contradiction_of_smaller
      (AvoidingContext.ofBranch
        { G := (closure.step.replacement ⟨ctx.G, ctx.baseline, ctx.state⟩ certificate).object
          baseline :=
            (closure.step.replacement ⟨ctx.G, ctx.baseline, ctx.state⟩ certificate).baseline
          state :=
            (closure.step.replacement ⟨ctx.G, ctx.baseline, ctx.state⟩ certificate).branchState }
        hNotTarget)
      (closure.step.smaller ⟨ctx.G, ctx.baseline, ctx.state⟩ certificate)

end Hypostructure.Core.Strategy
