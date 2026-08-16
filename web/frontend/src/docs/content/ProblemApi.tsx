import { L } from "../LeanCode";
import { ApiReference, ReferenceLegend, type ApiModule } from "./ApiReference";

const KERNEL: ApiModule = {
  title: "Hypostructure.Core — problem, target, progress, contexts",
  paths: [
    "hypostructure/Hypostructure/Core/Problem.lean",
    "hypostructure/Hypostructure/Core/Progress.lean",
    "hypostructure/Hypostructure/Core/Context.lean",
  ],
  intro:
    "The problem kernel an application registers, and the contexts and minimality principle Core derives from it.",
  entries: [
    {
      name: "Problem",
      kind: "structure",
      audience: "application",
      signature: `
        structure Problem where
          Ambient : Type
          Baseline : Ambient -> Prop
          BranchState : Ambient -> Type
          Presentation : Type := PUnit
          presentation : Option Presentation := none`,
      note: "Irreducible data shared by every tactic in one proof program. Only the first three fields are mandatory.",
    },
    {
      name: "Target",
      kind: "structure",
      audience: "application",
      signature: `
        structure Target (P : Problem) where
          Predicate : P.Ambient -> Prop
          Statement : Prop
          statement_to_target :
            Statement -> forall object, P.Baseline object -> Predicate object
          target_to_statement :
            (forall object, P.Baseline object -> Predicate object) -> Statement`,
      note: "The theorem being proved, kept separate from the problem. The two bridge fields are formulation laws, not proof content.",
    },
    {
      name: "Target.ofPredicate",
      kind: "def",
      audience: "application",
      signature: `
        def Target.ofPredicate (P : Problem) (Predicate : P.Ambient -> Prop) : Target P`,
      note: "The target whose statement is exactly the closure of its predicate; both bridges are the identity.",
    },
    {
      name: "Progress",
      kind: "structure",
      audience: "application",
      signature: `
        structure Progress (P : Problem) where
          Measure : Type
          lt : Measure -> Measure -> Prop
          wellFounded : WellFounded lt
          measure : P.Ambient -> Measure`,
      note: "A well-founded measure available to steps that require strict progress. An explicit capability, not part of Problem.",
    },
    {
      name: "Progress.Smaller",
      kind: "def",
      audience: "application",
      signature: `
        def Progress.Smaller (progress : Progress P) (G H : P.Ambient) : Prop :=
          progress.lt (progress.measure G) (progress.measure H)`,
      note: "The strict ambient-object relation induced by a progress profile.",
    },
    {
      name: "Progress.wellFounded_smaller",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem Progress.wellFounded_smaller (progress : Progress P) :
            WellFounded progress.Smaller`,
      note: "Pulling back a well-founded measure relation remains well-founded.",
    },
    {
      name: "Progress.not_smaller_self",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem Progress.not_smaller_self (progress : Progress P) (G : P.Ambient) :
            Not (progress.Smaller G G)`,
      note: "No ambient object is strictly smaller than itself.",
    },
    {
      name: "Progress.not_smaller_of_measure_eq",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem Progress.not_smaller_of_measure_eq (progress : Progress P)
            {G H : P.Ambient} (measure_eq : progress.measure G = progress.measure H) :
            Not (progress.Smaller G H)`,
      note: "Equal measures cannot certify a strict replacement.",
    },
    {
      name: "Progress.ofAmbientEq",
      kind: "def",
      audience: "application",
      signature: `
        def Progress.ofAmbientEq {P Q : Problem}
            (h : Q.Ambient = P.Ambient) (progress : Progress P) : Progress Q`,
      note: "Transport a progress profile between any two problems with the same Ambient type; Progress depends on nothing else about its problem.",
    },
    {
      name: "BranchContext",
      kind: "structure",
      audience: "application",
      signature: `
        structure BranchContext (P : Problem) where
          G : P.Ambient
          baseline : P.Baseline G
          state : P.BranchState G`,
      note: "The inherited state of one branch.",
    },
    {
      name: "AvoidingContext",
      kind: "structure",
      audience: "application",
      signature: `
        structure AvoidingContext (P : Problem) (Target : P.Ambient -> Prop)
            extends BranchContext P where
          avoids : Not (Target G)`,
      note: "A branch context on which the external target has not been realized.",
    },
    {
      name: "AvoidingContext.ofBranch",
      kind: "def",
      audience: "application",
      signature: `
        def AvoidingContext.ofBranch {Target : P.Ambient -> Prop} (ctx : BranchContext P)
            (avoids : Not (Target ctx.G)) : AvoidingContext P Target`,
      note: "Extend an existing branch context by its target-avoidance proof.",
    },
    {
      name: "MinimalityKernel",
      kind: "def",
      audience: "application",
      signature: `
        def MinimalityKernel (P : Problem) (Target : P.Ambient -> Prop)
            (progress : Progress P) (ctx : BranchContext P) : Prop :=
          forall H : P.Ambient,
            progress.Smaller H ctx.G -> P.Baseline H -> Target H`,
      note: "Every strictly smaller baseline object satisfies the target.",
    },
    {
      name: "MinimalCounterexampleContext",
      kind: "structure",
      audience: "application",
      signature: `
        structure MinimalCounterexampleContext (P : Problem) (Target : P.Ambient -> Prop)
            (progress : Progress P) extends AvoidingContext P Target where
          minimal : MinimalityKernel P Target progress toBranchContext`,
      note: "A target-avoiding branch equipped with a minimal-counterexample principle for one explicit progress profile.",
    },
    {
      name: "AvoidingContext.exists_minimalCounterexample",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem AvoidingContext.exists_minimalCounterexample
            {P : Problem} {Target : P.Ambient -> Prop}
            (ctx : AvoidingContext P Target)
            (progress : Progress P)
            (stateOf : (G : P.Ambient) -> P.BranchState G) :
            Nonempty (MinimalCounterexampleContext P Target progress)`,
      note: "Select a minimal target-avoiding baseline object using only the registered well-founded progress relation and a branch-state initializer.",
    },
    {
      name: "MinimalCounterexampleContext.ofAvoiding",
      kind: "def",
      audience: "application",
      signature: `
        def MinimalCounterexampleContext.ofAvoiding
            (ctx : AvoidingContext P Target)
            (minimal : MinimalityKernel P Target progress ctx.toBranchContext) :
            MinimalCounterexampleContext P Target progress`,
      note: "Build a minimal context from an avoiding context and its proved minimality kernel.",
    },
    {
      name: "MinimalCounterexampleContext.target_of_smaller",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem MinimalCounterexampleContext.target_of_smaller
            (ctx : MinimalCounterexampleContext P Target progress) {H : P.Ambient}
            (smaller : progress.Smaller H ctx.G) (baseline : P.Baseline H) :
            Target H`,
      note: "The target consequence for any strictly smaller baseline object.",
    },
    {
      name: "MinimalCounterexampleContext.contradiction_of_smaller",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem MinimalCounterexampleContext.contradiction_of_smaller
            (ctx : MinimalCounterexampleContext P Target progress)
            (candidate : AvoidingContext P Target)
            (smaller : progress.Smaller candidate.G ctx.G) : False`,
      note: "A strictly smaller avoiding branch contradicts minimality.",
    },
  ],
};

const RESIDUAL: ApiModule = {
  title: "Hypostructure.Core.Strategy — the problem-input residual",
  paths: [
    "hypostructure/Hypostructure/Core/Strategy/ProblemInput.lean",
    "hypostructure/Hypostructure/Core/Strategy/ProblemResidual.lean",
  ],
  intro:
    "The residual every assembly argues about, its refinement relation, and the vocabulary from which Core builds the domain's fact system.",
  entries: [
    {
      name: "ProblemInput",
      kind: "structure",
      audience: "application",
      signature: `
        structure ProblemInput (P : Core.Problem) where
          object : P.Ambient
          baseline : P.Baseline object
          branchState : P.BranchState object`,
      note: "One ambient object together with the baseline theorem and branch state registered by its problem. The residual type of every ledger in a proof.",
    },
    {
      name: "problemInputRefinement",
      kind: "instance",
      audience: "application",
      signature: `
        instance problemInputRefinement (P : Core.Problem) :
            RefinementSystem (Strategy.ProblemInput P) where
          Subject := P.Ambient
          subject input := input.object
          Refines new old := new.object = old.object
          refl _ := rfl
          trans new_middle middle_old := new_middle.trans middle_old
          subject_eq refinement := refinement`,
      note: "Object equality is the refinement relation of the problem-input domain. Fact-only steps are refl.",
    },
    {
      name: "FactVocabulary",
      kind: "structure",
      audience: "application",
      signature: `
        structure FactVocabulary (P : Core.Problem) where
          Key : Type
          keyDecidableEq : DecidableEq Key
          name : Key → Lean.Name
          name_injective : Function.Injective name
          name_ne_closure : ∀ key, name key ≠ Core.Residual.closureFactName
          Value : Key → Strategy.ProblemInput P → Sort _
          value_subsingleton : ∀ (key : Key) (input : Strategy.ProblemInput P),
            Subsingleton (Value key input)
          transport : {key : Key} → {new old : Strategy.ProblemInput P} →
            new.object = old.object → Value key old → Value key new`,
      note: "The semantic facts of one problem, excluding the closure key Core adds. The one problem-specific fact declaration.",
    },
    {
      name: "FactVocabulary.WithClosure",
      kind: "inductive",
      audience: "application",
      signature: `
        inductive FactVocabulary.WithClosure (vocabulary : FactVocabulary P) where
          | fact (key : vocabulary.Key)
          | closed`,
      note: "Core's fact keys: the vocabulary's keys plus the reserved closure key. Application keys are spelled WithClosure.fact k. Has DecidableEq.",
    },
    {
      name: "problemInputFactSystem",
      kind: "def",
      audience: "application",
      signature: `
        @[reducible] def problemInputFactSystem (vocabulary : FactVocabulary P) :
            FactSystem (Strategy.ProblemInput P)`,
      note: "The sole FactSystem of the problem-input domain, built from one vocabulary; installed once as an instance.",
    },
  ],
};

const SCOPE: ApiModule = {
  title: "Hypostructure.Core.Strategy — opening the scope",
  paths: ["hypostructure/Hypostructure/Core/Strategy/MinimalCounterexampleScope.lean"],
  intro:
    "Selecting a minimal counterexample and committing the selection as a branch's first fact. Assumes a FactSystem instance on ProblemInput P.",
  entries: [
    {
      name: "selectedInput",
      kind: "def",
      audience: "application",
      signature: `
        def selectedInput {Target : P.Ambient → Prop} {progress : Core.Progress P}
            (context : Core.MinimalCounterexampleContext P Target progress) :
            Strategy.ProblemInput P`,
      note: "The problem input carried by a selected minimal-counterexample context.",
    },
    {
      name: "OpenedScope",
      kind: "structure",
      audience: "application",
      signature: `
        structure OpenedScope (key : FactKey (Strategy.ProblemInput P)) where
          selected : Strategy.ProblemInput P
          history : ExactLedger (Strategy.ProblemInput P) selected [key]`,
      note: "The result of opening the scope: the selected residual together with the canonical history whose sole fact is the selection.",
    },
    {
      name: "openMinimalCounterexampleScope",
      kind: "def",
      audience: "application",
      signature: `
        noncomputable def openMinimalCounterexampleScope
            (T : Core.Target P)
            (progress : Core.Progress P)
            (stateOf : (G : P.Ambient) → P.BranchState G)
            (key : FactKey (Strategy.ProblemInput P))
            (encode : (context :
                Core.MinimalCounterexampleContext P T.Predicate progress) →
              key.At (selectedInput context))
            (input : Strategy.ProblemInput P)
            (avoids : ¬ T.Predicate input.object) :
            OpenedScope key`,
      note: "From any input that avoids the target, select a minimal counterexample and open the branch scope on it, committing the selection as the first fact. The framework-owned root and initializeScope calls happen inside it, so this is the one entry point through which a proof obtains its first ledger.",
    },
  ],
};

const MODULES = [KERNEL, RESIDUAL, SCOPE];

export function ProblemApiPage() {
  return (
    <>
      <header className="docs-header">
        <p className="hero-eyebrow">Reference</p>
        <h1>Problem API</h1>
        <p className="docs-lead">
          Every public declaration of the problem kernel, the problem-input
          residual and the scope opener, as it stands in the live sources.
          Universe annotations and the repeated{" "}
          <L>{"{P : Core.Problem}"}</L> binder are left out; everything else is
          verbatim.
        </p>
        <ReferenceLegend />
      </header>
      <ApiReference modules={MODULES} />
    </>
  );
}
