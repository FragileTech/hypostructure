import { Link } from "react-router-dom";

import { L, LeanCode } from "../LeanCode";

export function ClosingPage() {
  return (
    <>
      <header className="docs-header">
        <p className="hero-eyebrow">The ledger</p>
        <h1>Closing a branch</h1>
        <p className="docs-lead">
          A branch closes when its ledger carries the domain's reserved closure
          key. Two registered rules publish that key from facts already on the
          branch — one impossible fact, or two incompatible ones — and one
          theorem turns a closed ledger into <L>False</L>. Nothing is
          recomputed, and no second proof carrier appears.
        </p>
      </header>

      <section>
        <h2>A closed branch is a fact</h2>
        <p>
          Every <L>FactSystem</L> has a <L>closureKey</L> whose value is a{" "}
          <L>ClosureEvidence</L>: a reason and a proof of <L>False</L>. A ledger
          whose fact index contains that key is therefore uninhabited, and Core
          exposes exactly that:
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/ExactExecution.lean">{`
          /-- Eliminate a history carrying the domain's distinguished closure fact.

          The contradiction is the evidence stored by the unique \`FactSystem\`; this
          does not recompute a closing argument and does not introduce a second proof
          carrier. -/
          theorem ExactLedger.elimClosed
              {current : Residual} {known : FactKeys Residual}
              (history : ExactLedger Residual current known)
              (present : FactKeys.Has system.closureKey known) : False
        `}</LeanCode>
        <p>
          The <L>present</L> argument is the usual availability witness; at a
          call site it is <L>(by infer_instance)</L> because the closure key is
          literally the head of the index after a closing step.
        </p>
      </section>

      <section>
        <h2>Registered closure: Impossible and Incompatible</h2>
        <p>
          A branch test must offer every alternative its domain admits, and
          some of those alternatives are realized by no object at all. The
          application registers such knowledge once, as an instance, and the
          framework uses it to close arms the moment they are taken.
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/ExactExecution.lean">{`
          /-- Registered semantic incompatibility. -/
          class Incompatible (Residual : Type) [RefinementSystem Residual] [FactSystem Residual]
              (left right : FactKey Residual) where
            contradiction : (residual : Residual) ->
              left.At residual -> right.At residual -> False

          /-- Registered semantic impossibility of a single fact.

          A branch test must offer every alternative its domain admits, and some of those
          alternatives are realized by no object at all.  A branch that commits such a
          fact is uninhabited, and that is exactly what a closed terminal is.  Unlike
          \`Incompatible\`, the contradiction is carried by one fact, so no second fact
          has to be manufactured to record it. -/
          class Impossible (Residual : Type) [RefinementSystem Residual] [FactSystem Residual]
              (key : FactKey Residual) where
            contradiction : (residual : Residual) -> key.At residual -> False
        `}</LeanCode>
        <p>
          An instance is a theorem about the domain, stated on the values of
          the keys. From the framework's own fixture, whose subject has two
          mutually exclusive properties:
        </p>
        <LeanCode source="Hypostructure/Fixtures/AutomaticLedgerClosure.lean">{`
          instance : Incompatible Residual coldFact hotFact where
            contradiction residual cold hot :=
              residual.subject.exclusive cold.down hot.down

          /-- A fact no residual of this domain can carry: it asserts both halves of the
          subject's own exclusion. -/
          def bothFact : FactKey Residual := .both

          instance : Impossible Residual bothFact where
            contradiction residual value :=
              residual.subject.exclusive value.down.1 value.down.2
        `}</LeanCode>
      </section>

      <section>
        <h2>closeImpossible and closeIncompatible</h2>
        <LeanCode source="Hypostructure/Core/Strategy/ExactExecution.lean">{`
          /-- Close from one impossible fact visible on this branch. -/
          noncomputable def closeImpossible
              {current : Residual} {known : FactKeys Residual}
              (previous : ExactLedger Residual current known)
              (key : FactKey Residual)
              [FactKeys.Has key known]
              [Impossible Residual key]
              (fresh : system.closureKey ∉ known := by decide) :
              ExactLedger Residual current (system.closureKey :: known)

          /-- Close from two incompatible facts visible on this branch. -/
          noncomputable def closeIncompatible
              {current : Residual} {known : FactKeys Residual}
              (previous : ExactLedger Residual current known)
              (left right : FactKey Residual)
              [FactKeys.Has left known]
              [FactKeys.Has right known]
              [Incompatible Residual left right]
              (fresh : system.closureKey ∉ known := by decide) :
              ExactLedger Residual current (system.closureKey :: known)
        `}</LeanCode>
        <p>Each needs three things, and each is checked at elaboration:</p>
        <ul>
          <li>
            the offending key(s) must be on the branch — <L>FactKeys.Has</L>{" "}
            instances, found by instance search on the literal index;
          </li>
          <li>
            the registered <L>Impossible</L> / <L>Incompatible</L> instance;
          </li>
          <li>
            freshness of the closure key — the branch is not already closed.
          </li>
        </ul>
        <p>
          What they publish is one fact: the closure key, whose{" "}
          <L>ClosureEvidence</L> records the reason (
          <L>AutomaticClosureReason.impossibleFact key.name</L> or{" "}
          <L>incompatibleFacts left.name right.name</L>) and the contradiction
          obtained by reading the facts with <L>ExactLedger.get</L> and applying
          the instance. The audit records the producer as{" "}
          <L>`Hypostructure.Core.Strategy.autoclose.impossible</L> /{" "}
          <L>autoclose.incompatible</L>. The residual is unchanged and every
          earlier fact remains retrievable — a closure is a commit like any
          other, not a reset.
        </p>
        <p>The fixture pins all of that:</p>
        <LeanCode source="Hypostructure/Fixtures/AutomaticLedgerClosure.lean">{`
          noncomputable def impossibleHistory (subject : Subject)
              (cold : subject.Cold) (both : subject.Cold ∧ subject.Hot) :=
            closeImpossible
              (ExactLedger.publishFact exactLedgerInternal% (coldHistory subject cold)
                bothFact ⟨both⟩ (by simp [bothFact, coldFact]))
              bothFact (by simp [bothFact, coldFact])

          /-- **Predecessor preservation.**  The fact committed before the closure is
          still retrievable by exact key afterwards. -/
          theorem cold_remains_retrievable_after_impossible (subject : Subject)
              (cold : subject.Cold) (both : subject.Cold ∧ subject.Hot) :
              (ExactLedger.currentOf (impossibleHistory subject cold both)).subject.Cold :=
            (ExactLedger.get (impossibleHistory subject cold both) coldFact).down

          /-- **Residual behaviour.**  A single-fact closure changes no residual: the
          subject the branch argues about is the one it started with. -/
          theorem subject_unchanged_after_impossible (subject : Subject)
              (cold : subject.Cold) (both : subject.Cold ∧ subject.Hot) :
              (ExactLedger.currentOf (impossibleHistory subject cold both)).subject =
                subject := rfl

          /-- **The advertised theorem.**  The branch is closed. -/
          theorem impossible_branch_is_closed (subject : Subject)
              (cold : subject.Cold) (both : subject.Cold ∧ subject.Hot) : False :=
            (ExactLedger.get (impossibleHistory subject cold both)
              (FactSystem.closureKey (Residual := Residual))).contradiction

          /-- **Ledger availability.**  The closure entry names the impossible fact, and
          \`AutomaticClosureReason.impossibleFact\` is what distinguishes it from a
          two-fact incompatibility. -/
          theorem impossible_closure_names_the_fact (subject : Subject)
              (cold : subject.Cold) (both : subject.Cold ∧ subject.Hot) :
              (ExactLedger.get (impossibleHistory subject cold both)
                (FactSystem.closureKey (Residual := Residual))).reason =
                .impossibleFact (FactSystem.name bothFact) := rfl
        `}</LeanCode>
      </section>

      <section>
        <h2>The idiom</h2>
        <p>
          In an assembled proof a closing arm is two lines: publish the closure,
          then eliminate. The freshness proof unfolds whichever steps were run on
          the arm so <L>simp</L> can see the literal index.
        </p>
        <LeanCode>{`
          -- shape, not a compilable module
          | .left overlapHistory =>
              let closedHistory :=
                closeIncompatible overlapHistory (key .selection) (key .overlap)
                  (by simp [stepsRunOnThisArm, key_eq_iff])
              exact closedHistory.elimClosed (by infer_instance)
        `}</LeanCode>
        <p>
          Registered closure is preferable whenever the contradiction is a
          reusable statement about the domain: it is declared once, named in
          the audit, and any branch that ever carries the offending facts can
          close the same way.
        </p>
      </section>

      <section>
        <h2>Direct closure</h2>
        <p>
          A branch function is typed <L>… → False</L>. It may also close by
          reading facts and contradicting them on the spot, without publishing
          a closure fact — the contradiction is then local to that leaf rather
          than registered on the domain.
        </p>
        <LeanCode>{`
          -- shape, not a compilable module
          noncomputable def leafCloses {selected : ProblemInput P}
              (history : ExactLedger (ProblemInput P) selected
                [key .exitTaken, key .survivor, /- … -/ key .selection]) : False := by
            -- one fact's value is the negation of the other's
            exact (history.get (key .survivor)).down (history.get (key .exitTaken)).down

          noncomputable def leafClosesByArithmetic {selected : ProblemInput P}
              (history : ExactLedger (ProblemInput P) selected [/- … -/]) : False := by
            have lower : threshold < measure selected.object :=
              (history.get (key .above)).down
            have upper : measure selected.object ≤ threshold :=
              (history.get (key .estimate)).down
            exact Nat.not_lt_of_ge upper lower
        `}</LeanCode>
        <p>
          Both shapes read only through <L>ExactLedger.get</L> at a closure
          boundary; neither constructs a residual, calls a callback, or reaches
          into another branch. Which to use is a matter of reuse: a
          contradiction that recurs belongs in an <L>Impossible</L> /{" "}
          <L>Incompatible</L> instance.
        </p>
      </section>

      <section>
        <h2>Branches never leak</h2>
        <p>
          The two arms of a decision are separate ledgers on one immutable
          prefix. Everything proved before the decision is visible on both; a
          fact committed on one arm is absent from the other's type, so it
          cannot even be named there.
        </p>
        <LeanCode source="Hypostructure/Fixtures/BranchScopedExactLedger.lean">{`
          def rootHistory := ExactLedger.root exactLedgerInternal% ({ value := 4 } : Residual)
          def sharedPrefix := ExactLedger.publishFact exactLedgerInternal% rootHistory upstream ⟨Nat.le_refl 4⟩

          /-- Both branches extend the same immutable canonical prefix. -/
          def leftCursor := ExactLedger.publishFact exactLedgerInternal% sharedPrefix leftOnly ()
          def rightCursor := ExactLedger.publishFact exactLedgerInternal% sharedPrefix rightOnly ()

          theorem upstream_visible_on_left :
              (ExactLedger.currentOf leftCursor).value ≤ 4 :=
            (ExactLedger.get leftCursor upstream).down

          theorem upstream_visible_on_right :
              (ExactLedger.currentOf rightCursor).value ≤ 4 :=
            (ExactLedger.get rightCursor upstream).down

          /--
          error: failed to synthesize instance of type class
            FactKeys.Has leftOnly [rightOnly, upstream]
          -/
          #guard_msgs (error) in
          example : leftOnly.At (ExactLedger.currentOf rightCursor) :=
            ExactLedger.get rightCursor leftOnly
        `}</LeanCode>
        <p>
          This is why an assembly never merges sibling ledgers or flattens them
          into a global store: there is nothing to merge, and the type checker
          would reject the read. How dichotomies and closures compose into a
          whole proof is the subject of{" "}
          <Link to="/lean/assembly">From steps to the theorem</Link>.
        </p>
      </section>
    </>
  );
}
