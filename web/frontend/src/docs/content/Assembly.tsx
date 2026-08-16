import { Link } from "react-router-dom";

import { L, LeanCode } from "../LeanCode";

export function AssemblyPage() {
  return (
    <>
      <header className="docs-header">
        <p className="hero-eyebrow">Assembling a proof</p>
        <h1>From steps to the theorem</h1>
        <p className="docs-lead">
          A proof is not interpreted by a program: it is plain Lean composition
          of the pieces on the previous pages. Steps are run one after another,
          decisions split the branch, every leaf ends in <L>False</L>, and the
          root closure is bridged to the public statement through the target.
          This page collects the shapes that verified proofs use. All snippets
          are shapes over a made-up vocabulary, not compilable modules.
        </p>
      </header>

      <section>
        <h2>What an assembly is</h2>
        <p>
          The application authors one <L>noncomputable def</L> or{" "}
          <L>theorem</L> per branch, each typed by the exact ledger index it
          expects. There is no callback, no route table, no result carrier: a
          branch function receives an <L>ExactLedger (ProblemInput P) selected
          [keys…]</L>, extends it with <L>AtomicCT.run</L>, splits it with{" "}
          <L>Decision.run</L>, and either returns the extended ledger or returns{" "}
          <L>False</L>. Every intermediate type spells the full list of facts
          the branch has established — which is why the assembly can be read as
          the audit.
        </p>
      </section>

      <section>
        <h2>Straight-line prefixes</h2>
        <LeanCode>{`
          -- shape, not a compilable module
          /-- The entry prefix, run on the selected ledger. -/
          noncomputable def entryPrefix
              {selected : ProblemInput P}
              (history : ExactLedger (ProblemInput P) selected [key .selection]) :
              ExactLedger (ProblemInput P) selected
                [key .c, key .b, key .a, key .selection] := by
            let h1 := stepA.run history (by simp [stepA, key_eq_iff])
            let h2 := stepB.run h1 (by simp [stepB, stepA, key_eq_iff])
            exact stepC.run h2 (by simp [stepC, stepB, stepA, key_eq_iff])
        `}</LeanCode>
        <p>
          Each <L>.run</L> is checked for readiness (
          <L>FactKeys.Available Requires known</L>) and freshness, and its
          output index is definitionally <L>Produces ++ known</L>, so the
          declared result type is the newest fact first and the selection last.
          If a step's manifest is not satisfied by the ledger it is handed, the
          definition fails to elaborate at that line.
        </p>
      </section>

      <section>
        <h2>Discharging freshness</h2>
        <p>
          <L>AtomicCT.run</L> asks for <L>List.Disjoint ct.manifest.Produces
          known</L>; <L>Decision.run</L> and the closers ask for a key not in{" "}
          <L>known</L>. On closed literal lists the default <L>by decide</L>{" "}
          works. When keys are spelled through the vocabulary's constructor,
          give <L>simp</L> the injectivity of that constructor and unfold the
          steps so it can see their <L>Produces</L>:
        </p>
        <LeanCode>{`
          -- shape: one lemma per application, next to its vocabulary
          @[simp] theorem key_eq_iff (left right : Key) :
              (key left = key right) ↔ left = right := by
            constructor
            · intro same; exact FactVocabulary.WithClosure.fact.inj same
            · intro same; cases same; rfl

          @[simp] theorem closureKey_eq_closed :
              (FactSystem.closureKey : FactKey (ProblemInput P)) = .closed := rfl
        `}</LeanCode>
        <p>
          With those in the simp set, freshness proofs are uniform:{" "}
          <L>by simp [key_eq_iff]</L> when nothing needs unfolding,{" "}
          <L>by simp [stepB, stepA, key_eq_iff]</L> after steps have been run on
          the branch. Steps are <L>@[reducible]</L> precisely so this unfolding
          is available.
        </p>
      </section>

      <section>
        <h2>Dichotomies</h2>
        <p>
          A two-way split is <L>Decision.run</L> on the current ledger, followed
          by a <L>match</L> whose arms continue with differently indexed
          ledgers. Nesting is ordinary nesting.
        </p>
        <LeanCode>{`
          -- shape, not a compilable module
          noncomputable def afterSplit
              {selected : ProblemInput P}
              (history : ExactLedger (ProblemInput P) selected [key .a, key .selection]) :
              False := by
            match Decision.run history (key .above) (key .atOrBelow) \`Proof.split
                (if h : threshold < measure selected.object then .inl ⟨h⟩
                 else .inr ⟨Nat.le_of_not_lt h⟩) with
            | .left aboveHistory =>
                -- aboveHistory : ExactLedger _ selected [key .above, key .a, key .selection]
                exact aboveBranch aboveHistory
            | .right belowHistory =>
                -- belowHistory : ExactLedger _ selected [key .atOrBelow, key .a, key .selection]
                exact belowBranch belowHistory
        `}</LeanCode>
        <p>
          The <L>alternatives</L> argument is where the mathematics of the
          split lives: an exhaustive case analysis on the current object,
          returning a value of one arm's key. Whichever arm is returned is the
          fact that gets committed; the other never enters that branch's index.
        </p>
        <h3>Reusable dichotomies</h3>
        <p>
          A dichotomy that several assemblies need is written once as a function
          over any ledger whose index contains its prerequisite. The
          prerequisite is an explicit <L>FactKeys.Has</L> instance argument and
          the fresh arms are membership negations, so the precondition is stated
          in the type and satisfied by the caller at the call site:
        </p>
        <LeanCode>{`
          -- shape, not a compilable module
          noncomputable def contextValidityDichotomy
              {current : ProblemInput P} {known : FactKeys (ProblemInput P)}
              (previous : ExactLedger (ProblemInput P) current known)
              [FactKeys.Has (key .dependence) known]
              (defectFresh : ¬ List.Mem (key .defect) known)
              (universalFresh : ¬ List.Mem (key .universal) known) :
              Decision (key .defect) (key .universal) previous :=
            Decision.run previous (key .defect) (key .universal) \`Proof.contextValidity
              (decideFrom (previous.get (key .dependence)).down) defectFresh universalFresh
        `}</LeanCode>
        <p>
          Such a function is position-independent in the same sense a step is:
          it runs after any branch that has the required key, and it can be
          called from any branch.
        </p>
      </section>

      <section>
        <h2>Closing arms</h2>
        <p>
          Every leaf is a function to <L>False</L>. It closes either by a
          registered rule — <L>closeImpossible</L> / <L>closeIncompatible</L>{" "}
          followed by <L>elimClosed</L> — or directly, by reading facts with{" "}
          <L>ExactLedger.get</L> and contradicting them. Both are on{" "}
          <Link to="/lean/closing">Closing a branch</Link>. A nested example
          with three decisions and four leaves:
        </p>
        <LeanCode>{`
          -- shape, not a compilable module
          noncomputable def rankDropCloses {selected : ProblemInput P}
              (history : ExactLedger (ProblemInput P) selected [/- … -/ key .selection]) : False := by
            let afterDependence := dependenceStep.run history (by simp [dependenceStep, key_eq_iff])
            match contextValidityDichotomy afterDependence
                (by simp [dependenceStep, key_eq_iff]) (by simp [dependenceStep, key_eq_iff]) with
            | .left defectHistory =>
                let closed := closeImpossible defectHistory (key .defect) (by simp [dependenceStep, key_eq_iff])
                exact closed.elimClosed (by infer_instance)
            | .right universalHistory =>
                match overlapDichotomy universalHistory (by simp [dependenceStep, key_eq_iff])
                    (by simp [dependenceStep, key_eq_iff]) with
                | .left overlapHistory =>
                    let closed := closeIncompatible overlapHistory (key .selection) (key .overlap)
                      (by simp [dependenceStep, key_eq_iff])
                    exact closed.elimClosed (by infer_instance)
                | .right delocalizedHistory =>
                    let afterRepair := repairStep.run delocalizedHistory (by simp [repairStep, dependenceStep, key_eq_iff])
                    let closed := closeIncompatible afterRepair (key .selection) (key .globalBarrier)
                      (by simp [repairStep, dependenceStep, key_eq_iff])
                    exact closed.elimClosed (by infer_instance)
        `}</LeanCode>
      </section>

      <section>
        <h2>Using minimality inside a step</h2>
        <p>
          The selection fact committed by the opening scope carries the two
          components of minimality: the object avoids the target, and every
          strictly smaller baseline object satisfies it. A step that needs
          minimality does not re-select or re-quantify; it reads the fact and
          rebuilds a <L>Core.MinimalCounterexampleContext</L> from it and the
          current input:
        </p>
        <LeanCode>{`
          -- shape, not a compilable module
          /-- The reading of one ledger entry; nothing is proved here. -/
          def contextOfSelection (input : ProblemInput P)
              (avoids : ¬ T.Predicate input.object)
              (minimal : ∀ smaller, progress.Smaller smaller input.object →
                P.Baseline smaller → T.Predicate smaller) :
              Core.MinimalCounterexampleContext P T.Predicate progress where
            G := input.object
            baseline := input.baseline
            state := input.branchState
            avoids := avoids
            minimal := minimal

          -- inside a factOnly derivation:
          (fun inputs =>
            let selection := (inputs.get (key .selection)).down
            let context := contextOfSelection inputs.current selection.1 selection.2
            .cons (key := key .exclusion) ⟨fun candidate smaller baseline =>
              context.target_of_smaller smaller baseline⟩ .nil)
        `}</LeanCode>
        <p>
          From the context, <L>target_of_smaller</L> and{" "}
          <L>contradiction_of_smaller</L> (see{" "}
          <Link to="/lean/problem">the problem page</Link>) are the whole
          minimality principle; <Link to="/lean/replacement">interface
          replacement</Link> is the reusable theorem built on top of them.
        </p>
      </section>

      <section>
        <h2>The endpoint</h2>
        <p>
          The root of the assembly is a closure of the selected ledger: from a
          ledger whose only fact is the selection, <L>False</L>. Bridging that
          to the public statement uses only the target's own formulation law.
        </p>
        <LeanCode>{`
          -- shape, not a compilable module
          /-- Selected-root closure, assembled directly from the steps. -/
          theorem selectedLedgerClosure {selected : ProblemInput P}
              (history : ExactLedger (ProblemInput P) selected [key .selection]) : False := by
            match rootDichotomy history with
            | .left h => exact leftBranch h
            | .right h => exact rightBranch h

          /-- A closed selected residual proves the target on every baseline object. -/
          theorem target_closure_of_selectedLedgerClosure
              (closure : ∀ {selected : ProblemInput P},
                ExactLedger (ProblemInput P) selected [key .selection] → False) :
              ∀ object, P.Baseline object → T.Predicate object := by
            intro object baseline
            by_cases hasTarget : T.Predicate object
            · exact hasTarget
            · let opened := openMinimalCounterexampleScope T progress stateOf (key .selection)
                encode { object, baseline, branchState := stateOf object } hasTarget
              exact (closure opened.history).elim

          /-- The public theorem. -/
          theorem statement : T.Statement :=
            T.target_to_statement
              (target_closure_of_selectedLedgerClosure fun {selected} h => selectedLedgerClosure h)
        `}</LeanCode>
        <p>
          Read it bottom-up: <L>T.target_to_statement</L> needs "every baseline
          object satisfies the predicate"; for an object that does not, the
          scope opener produces a selected minimal counterexample and its
          ledger, and the root closure refutes it. Nothing else — no
          extra bridge, no closure decoder — stands between the ledger and the
          statement.
        </p>
      </section>

      <section>
        <h2>Pinning the problem</h2>
        <p>
          The application's topology file authors composition only; it should
          not grow named helper lemmas. The convention is to pin the identities
          the framework relies on as <L>example</L>s that reduce by <L>rfl</L>:
        </p>
        <LeanCode>{`
          -- shape, not a compilable module
          /-- The problem the assembly argues about is this problem. -/
          example : problem = Generic.problem BranchState presentation data := rfl

          /-- The public target's predicate is the assembly's accepted predicate. -/
          example : target.Predicate = Generic.acceptedPredicate data := rfl
        `}</LeanCode>
        <p>
          If the two ever drift, the <L>rfl</L> stops closing and the file
          stops building — which is the point.
        </p>
      </section>

      <section>
        <h2>Checklist</h2>
        <ul>
          <li>
            One step is one manifest and one derivation from{" "}
            <L>inputs.current</L> and <L>inputs.get</L>; steps never construct
            residuals or read undeclared facts.
          </li>
          <li>
            The only writes are <L>AtomicCT.run</L>, <L>Decision.run</L>,{" "}
            <L>closeImpossible</L> and <L>closeIncompatible</L>.
          </li>
          <li>
            Every branch function's type spells its literal key index; every
            leaf returns <L>False</L>.
          </li>
          <li>
            No branch reads a sibling's fact; no ledger is merged, reset or
            rebased.
          </li>
          <li>
            The statement is reached through <L>openMinimalCounterexampleScope</L>{" "}
            and <L>Target.target_to_statement</L>, and through nothing else.
          </li>
        </ul>
      </section>
    </>
  );
}
