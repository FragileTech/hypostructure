import { Link } from "react-router-dom";

import { L, LeanCode } from "../LeanCode";

export function ScopePage() {
  return (
    <>
      <header className="docs-header">
        <p className="hero-eyebrow">Defining a problem</p>
        <h1>Vocabulary and the opening scope</h1>
        <p className="docs-lead">
          Two derived pieces connect a problem to the ledger. The{" "}
          <em>fact vocabulary</em> is the closed set of facts an argument
          proves, from which Core builds the residual domain's one{" "}
          <L>FactSystem</L>. The <em>opening scope</em> selects a minimal
          counterexample and commits that selection as a branch's first fact —
          the only step that ever replaces the object under discussion.
        </p>
      </header>

      <section>
        <h2>The fact vocabulary</h2>
        <p>
          A vocabulary is the closed set of semantic keys one argument proves,
          together with the value schema of each key and its transport along a
          refinement. An assembly quantifies over its keys instead of
          naming a fixed enumeration; a problem instantiates the vocabulary
          with exactly the facts its argument establishes.
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/ProblemResidual.lean">{`
          /-- The semantic facts of one problem, excluding the closure key Core adds. -/
          structure FactVocabulary (P : Core.Problem) where
            Key : Type
            keyDecidableEq : DecidableEq Key
            /-- Audit names.  They are diagnostics; routing always compares keys. -/
            name : Key → Lean.Name
            name_injective : Function.Injective name
            /-- No vocabulary key may impersonate the reserved closure name. -/
            name_ne_closure : ∀ key, name key ≠ Core.Residual.closureFactName
            Value : Key → Strategy.ProblemInput P → Sort _
            /-- A fact value carries no data; see \`FactSystem.value_subsingleton\`.  A
            vocabulary states what its facts *mean*, and the residual carries what they
            are about. -/
            value_subsingleton : ∀ (key : Key) (input : Strategy.ProblemInput P),
              Subsingleton (Value key input)
            /-- Every fact stays applicable on a descendant residual.  Functoriality is
            free from \`value_subsingleton\`, so it is not asked for here. -/
            transport : {key : Key} → {new old : Strategy.ProblemInput P} →
              new.object = old.object → Value key old → Value key new
        `}</LeanCode>
        <p>
          Compare this with the{" "}
          <Link to="/lean/ledger">
            <L>FactSystem</L> class
          </Link>
          : a vocabulary is the same contract restricted to what a problem
          must say. <L>Value key input</L> is the statement <L>key</L> makes
          about the residual <L>input</L>; it must be a subsingleton, so a fact
          is evidence that a statement holds and nothing more. <L>transport</L>{" "}
          only has to move a value between two inputs with the same object —
          usually a rewrite along the equality — because object equality is the
          refinement relation of this domain. And no key may take the reserved
          closure name, so the closed-branch marker cannot be spoofed.
        </p>
      </section>

      <section>
        <h2>Core adds the closure key</h2>
        <p>
          The framework owns the distinguished closure key, so no vocabulary can
          forget it or give it a second schema. Core's key type is the
          vocabulary's keys plus one:
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/ProblemResidual.lean">{`
          /-- Core's fact keys: the problem's own vocabulary plus the reserved closure
          key.  Adding the closure key here, rather than asking a vocabulary to carry it,
          is what makes \`closureFactName\` unforgeable by an application. -/
          inductive FactVocabulary.WithClosure where
            | fact (key : vocabulary.Key)
            | closed

          /-- The sole \`FactSystem\` of the problem-input domain, built from one
          problem's vocabulary. -/
          @[reducible] def problemInputFactSystem (vocabulary : FactVocabulary P) :
              FactSystem (Strategy.ProblemInput P) where
            Key := vocabulary.WithClosure
            keyDecidableEq := inferInstance
            name
              | .fact key => vocabulary.name key
              | .closed => Core.Residual.closureFactName
            name_injective := ...
            Value
              | .fact key, input => vocabulary.Value key input
              | .closed, _ => ULift ClosureEvidence
            value_subsingleton := ...
            transport := ...
            closureKey := .closed
            closure_name := rfl
            closureValue _ evidence := ULift.up evidence
            closureEvidence _ value := value.down
        `}</LeanCode>
        <p>
          An application installs its domain's fact system in one line and
          then names its keys through <L>WithClosure.fact</L>:
        </p>
        <LeanCode>{`
          noncomputable instance : FactSystem (ProblemInput problem) :=
            problemInputFactSystem vocabulary

          def someFact : FactKey (ProblemInput problem) :=
            FactVocabulary.WithClosure.fact Key.someFact
        `}</LeanCode>
        <p>
          From here on the ledger pages apply unchanged: <L>FactKey</L>,{" "}
          <L>key.At input</L>, manifests, <L>factOnly</L>, <L>AtomicCT.run</L>,{" "}
          <L>Decision.run</L> and <L>ExactLedger.get</L> all work over{" "}
          <L>ProblemInput P</L> with this fact system.
        </p>
      </section>

      <section>
        <h2>Opening the scope</h2>
        <p>
          A proof by minimal counterexample assumes a counterexample exists,
          chooses one minimal for the registered well-founded order, and argues
          about that fixed object from then on. This is the one step of an assembly
          that <em>replaces</em> the object under discussion, so it is the one
          step the canonical ledger admits only through framework-owned
          first-scope initialization: it consumes a history whose fact index is
          exactly empty and is therefore unusable once any fact exists.
          Everything after it is a proved refinement, so no fact committed here
          can be archived, rebased or dropped.
        </p>
        <p>
          <L>AvoidingContext.exists_minimalCounterexample</L> owns the
          selection. This module only opens the scope and commits the selected
          context as the branch's first fact.
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/MinimalCounterexampleScope.lean">{`
          /-- The problem input carried by a selected minimal-counterexample context. -/
          def selectedInput {Target : P.Ambient → Prop} {progress : Core.Progress P}
              (context : Core.MinimalCounterexampleContext P Target progress) :
              Strategy.ProblemInput P where
            object := context.G
            baseline := context.baseline
            branchState := context.state

          /-- The result of opening the scope: the selected residual together with the
          canonical history whose sole fact is the selection. -/
          structure OpenedScope (key : FactKey (Strategy.ProblemInput P)) where
            selected : Strategy.ProblemInput P
            history : ExactLedger (Strategy.ProblemInput P) selected [key]

          /-- From any input that avoids the target, select a counterexample minimal
          for the registered progress order and open the branch scope on it,
          committing the selected context as the first fact. -/
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
              OpenedScope key
        `}</LeanCode>
        <p>The arguments are the whole problem-specific contribution to the scope:</p>
        <ul>
          <li>
            <L>T</L> and <L>progress</L> — the registered target and progress
            profile;
          </li>
          <li>
            <L>stateOf</L> — how to initialize branch state for whichever
            object is selected;
          </li>
          <li>
            <L>key</L> — the vocabulary key under which the selection is
            recorded, and <L>encode</L> — how the selected context becomes that
            key's value at the selected input. Typically the key's value{" "}
            <em>is</em> the selection statement (the object avoids the target,
            and every strictly smaller baseline object satisfies it), so{" "}
            <L>encode</L> just repackages <L>context.avoids</L> and{" "}
            <L>context.minimal</L>;
          </li>
          <li>
            <L>input</L> and <L>avoids</L> — the branch's own hypothesis that
            some counterexample exists. The arm in which the target holds is
            closed by the caller before this point.
          </li>
        </ul>
        <p>What comes back is an <L>OpenedScope key</L>:</p>
        <ul>
          <li>
            <L>selected</L> — the chosen minimal counterexample as a{" "}
            <L>ProblemInput</L>; and
          </li>
          <li>
            <L>history</L> — the ledger, an{" "}
            <L>ExactLedger (ProblemInput P) selected [key]</L>: residual index
            the selected input, fact index exactly the one selection key, and
            one commit in the audit trail (producer{" "}
            <L>`Hypostructure.Core.Strategy.minimalCounterexampleScope</L>).
          </li>
        </ul>
        <p>
          Internally the opener builds an <L>AvoidingContext</L> from the
          input, chooses a minimal context with{" "}
          <L>exists_minimalCounterexample</L>, and calls{" "}
          <L>ExactLedger.initializeScope</L> on <L>ExactLedger.root input</L>.
          Both of those ledger operations take the framework token, and the
          opener is where that token is spent, so this is the one entry point
          through which a proof obtains its first ledger: an application calls
          it, receives an <L>OpenedScope</L>, and continues from its{" "}
          <L>history</L> by running steps.
        </p>
      </section>

      <section>
        <h2>A complete small problem</h2>
        <p>
          The framework's own fixture defines a problem end to end. Ambient
          objects are natural numbers, every object satisfies the baseline,
          there is no branch state, and the target is "the object is zero" —
          so a counterexample is a nonzero object and the minimal counterexample
          is 1. It is a toy, but every piece an application supplies is present.
        </p>
        <LeanCode source="Hypostructure/Fixtures/MinimalCounterexampleScope.lean">{`
          /-- Ambient objects are naturals; every object satisfies the baseline. -/
          abbrev problem : Core.Problem where
            Ambient := Nat
            Baseline := fun _ => True
            BranchState := fun _ => Unit

          /-- The target is "the object is zero", so a counterexample is a nonzero
          object and the minimal counterexample is \`1\`. -/
          abbrev target : Core.Target problem where
            Predicate := fun object => object = 0
            Statement := ∀ object : Nat, True → object = 0
            statement_to_target := fun statement object baseline => statement object baseline
            target_to_statement := fun proof => proof

          abbrev progress : Core.Progress problem where
            Measure := Nat
            lt := (· < ·)
            wellFounded := Nat.lt_wfRel.wf
            measure := id
        `}</LeanCode>
        <p>
          The vocabulary has one key. Its value <em>is</em> the selection
          statement — the residual object is a counterexample and every
          strictly smaller baseline object is not — stated directly, not
          paraphrased:
        </p>
        <LeanCode source="Hypostructure/Fixtures/MinimalCounterexampleScope.lean">{`
          inductive Key where
            | selection
            deriving DecidableEq

          abbrev vocabulary : FactVocabulary problem where
            Key := Key
            keyDecidableEq := inferInstance
            name := fun _ => \`MinimalCounterexampleScopeFixture.selection
            name_injective := by intro left right _; cases left; cases right; rfl
            name_ne_closure := by intro key; cases key; decide
            Value := fun _ input =>
              PLift (input.object ≠ 0 ∧ ∀ smaller, smaller < input.object → smaller = 0)
            value_subsingleton := fun _ _ => ⟨fun left right => by
              cases left; cases right; rfl⟩
            transport := by
              intro _ new old refinement value
              exact ⟨refinement ▸ value.down⟩

          noncomputable instance : FactSystem (Core.Strategy.ProblemInput problem) :=
            problemInputFactSystem vocabulary

          /-- The exact semantic key, as callers name it. -/
          def selection : FactKey (Core.Strategy.ProblemInput problem) :=
            FactVocabulary.WithClosure.fact Key.selection
        `}</LeanCode>
        <p>
          Opening the scope from the counterexample 7: <L>encode</L> assembles
          the key's value from <L>context.avoids</L> and{" "}
          <L>context.minimal</L>, and the branch hypothesis <L>avoids</L> is
          decided.
        </p>
        <LeanCode source="Hypostructure/Fixtures/MinimalCounterexampleScope.lean">{`
          /-- The scope opened from the counterexample \`7\`. -/
          noncomputable def opened :
              OpenedScope (P := problem) selection :=
            openMinimalCounterexampleScope target progress (fun _ => ())
              selection
              (fun context => ⟨context.avoids, fun smaller below =>
                context.minimal smaller below trivial⟩)
              { object := 7, baseline := trivial, branchState := () }
              (by decide)
        `}</LeanCode>
        <p>
          And what the fixture then proves about the opened scope is exactly
          what a proof relies on:
        </p>
        <LeanCode source="Hypostructure/Fixtures/MinimalCounterexampleScope.lean">{`
          /-- **The committed fact is retrievable by its exact key.**  No producer, row,
          predecessor depth, or display name is named. -/
          theorem selection_fact_retrievable :
              (ExactLedger.currentOf opened.history).object ≠ 0 ∧
                ∀ smaller, smaller < (ExactLedger.currentOf opened.history).object →
                  smaller = 0 :=
            (ExactLedger.get opened.history selection).down

          /-- **The residual moved to the selected object**, and the selected object is
          the one the fact speaks about. -/
          theorem residual_is_selected :
              ExactLedger.currentOf opened.history = opened.selected := rfl

          /-- **The scope is the branch's first and only commit**, so nothing was
          archived or rebased to make room for it. -/
          theorem audit_is_exactly_the_selection :
              (ExactLedger.audit opened.history).facts =
                [\`MinimalCounterexampleScopeFixture.selection] := rfl

          /-- Every fact is accounted for by a chronological commit. -/
          theorem audit_accounts_for_every_fact :
              (ExactLedger.audit opened.history).facts =
                (ExactLedger.audit opened.history).commits.reverse.flatMap
                  (fun record => record.produced) :=
            ExactLedger.audit_complete opened.history
        `}</LeanCode>
        <p>
          From <L>opened.history</L> a proof proceeds exactly as on the{" "}
          <Link to="/lean/writing-facts">writing facts</Link> page: steps built
          with <L>factOnly</L> declare the selection key in their{" "}
          <L>Requires</L>, read it with <L>inputs.get selection</L>, and are
          run against the history; dichotomies use <L>Decision.run</L>. The
          problem is never mentioned again except through its vocabulary keys.
          How those pieces compose into the public theorem is on{" "}
          <Link to="/lean/assembly">From steps to the theorem</Link>.
        </p>
      </section>
    </>
  );
}
