import { Link } from "react-router-dom";

import { L, LeanCode } from "../LeanCode";

export function WritingFactsPage() {
  return (
    <>
      <header className="docs-header">
        <p className="hero-eyebrow">Core API</p>
        <h1>Writing facts</h1>
        <p className="docs-lead">
          A step writes facts by declaring them in a manifest, deriving their
          values inside a sealed executor, and being <em>run</em> against a
          ledger. Running appends the declared keys to the ledger's index; there
          is no other way a fact enters a branch.
        </p>
      </header>

      <section>
        <h2>The manifest: what a step needs and what it adds</h2>
        <LeanCode source="Hypostructure/Core/Strategy/FactManifest.lean">{`
          /-- Closed prerequisite contract shared by atomic CTs and exhaustive
          decisions. -/
          structure FactRequirements (Residual : Type) [RefinementSystem Residual] [FactSystem Residual] where
            Requires : FactKeys Residual
            requiresUnique : Requires.Nodup

          /-- Closed input/output contract for one CT or Strategy.  Every execution must
          append at least one fact, and neither side may name a key twice. -/
          structure FactManifest (Residual : Type) [RefinementSystem Residual] [FactSystem Residual]
              extends FactRequirements Residual where
            Produces : FactKeys Residual
            producesUnique : Produces.Nodup
            producesNonempty : Produces ≠ []
        `}</LeanCode>
        <p>
          A manifest carries key schemas, never payloads or a parallel store.
          The uniqueness and non-emptiness proofs are usually <L>by simp</L>{" "}
          over the literal lists:
        </p>
        <LeanCode source="Hypostructure/Fixtures/ExactExecution.lean">{`
          abbrev ctManifest : FactManifest Residual where
            Requires := []
            Produces := [atMostTwo]
            requiresUnique := by simp
            producesUnique := by simp
            producesNonempty := by simp
        `}</LeanCode>
      </section>

      <section>
        <h2>The value bundle: FactKeys.Values</h2>
        <p>
          The values a step commits are typed by exactly the keys it produces.
          <L>FactKeys.Values residual keys</L> is a heterogeneous list: one value
          of type <L>key.At residual</L> per key, in order.
        </p>
        <LeanCode source="Hypostructure/Core/Residual/ExactLedger.lean">{`
          /-- Values for exactly the keys in a fact index. -/
          inductive FactKeys.Values (residual : Residual) : FactKeys Residual -> Type _ where
            | nil : Values residual []
            | cons {key : FactKey Residual} {tail : FactKeys Residual}
                (value : key.At residual) (rest : Values residual tail) :
                Values residual (key :: tail)
        `}</LeanCode>
        <p>
          A one-fact bundle is written <L>.cons (key := k) ⟨proof⟩ .nil</L>. The
          named argument fixes which key the value is for; Lean then checks the
          proof against <L>k.At residual</L>. Because <L>Values</L> is indexed by
          the key list, a bundle with the wrong number of facts, or the wrong
          keys, is a type error against <L>manifest.Produces</L>.
        </p>
      </section>

      <section>
        <h2>The executor: AtomicCT</h2>
        <p>
          A step is a value of <L>AtomicCT</L>: a sealed record with a name, a
          manifest, and three private functions from the sealed inputs. (The
          framework also names this type <L>AtomicStrategy</L>; the two are
          definitionally the same, a leftover of an older distinction between
          "CTs" and "Strategies" that the ledger has erased. These pages say{" "}
          <em>step</em> throughout.)
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/ExactExecution.lean">{`
          /-- Complete indivisible output of one atomic executor. -/
          structure AtomicResult (manifest : FactManifest Residual) (next : Residual) where
            facts : FactKeys.Values next manifest.Produces
            checks : Nat := 0
            work : Nat := 0

          /-- A sealed atomic CT.  Its implementation sees only the current residual
          and the facts listed in \`Requires\`. -/
          structure AtomicCT (Residual : Type) [RefinementSystem Residual] [FactSystem Residual] where
            private mk ::
            id : Lean.Name
            manifest : FactManifest Residual
            private next : FactInputs manifest.toFactRequirements -> Residual
            private refines : (inputs : FactInputs manifest.toFactRequirements) ->
              RefinementSystem.Refines (next inputs) inputs.current
            private execute : (inputs : FactInputs manifest.toFactRequirements) ->
              AtomicResult manifest (next inputs)

          /-- Strategies and CTs deliberately share one sealed executor and one exact
          ledger output. -/
          abbrev AtomicStrategy (Residual : Type) [RefinementSystem Residual] [FactSystem Residual] :=
            AtomicCT Residual
        `}</LeanCode>
        <p>The three functions are the whole content of a step:</p>
        <ul>
          <li>
            <L>next</L> — the residual after the step, computed from the inputs;
          </li>
          <li>
            <L>refines</L> — a proof that <L>next inputs</L> refines{" "}
            <L>inputs.current</L>, so the change is a restriction and every
            inherited fact transports;
          </li>
          <li>
            <L>execute</L> — the value bundle for <L>manifest.Produces</L> at
            the new residual, plus optional <L>checks</L>/<L>work</L> counters
            that end up in the audit.
          </li>
        </ul>
        <p>
          The constructor is private and <L>AtomicCT.create</L> takes the
          framework token, so an application builds steps only through the
          registered combinators below.
        </p>
      </section>

      <section>
        <h2>The common step: factOnly</h2>
        <p>
          Most steps of an assembly prove new theorems about the object they
          were handed and change nothing else. <L>factOnly</L> is that step: its{" "}
          <L>next</L> is the identity and its <L>refines</L> is{" "}
          <L>RefinementSystem.refl</L>, so the author supplies only the
          derivation.
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/FactOnlyStrategy.lean">{`
          /-- A Strategy that preserves the residual and commits exactly the facts it
          derives from its declared prerequisites. -/
          @[reducible] noncomputable def factOnly
              (id : Lean.Name) (manifest : FactManifest Residual)
              (derive : (inputs : FactInputs manifest.toFactRequirements) →
                FactKeys.Values inputs.current manifest.Produces)
              (checks : Nat := 0) (work : Nat := 0) :
              AtomicStrategy Residual
        `}</LeanCode>
        <p>
          A step is therefore: a name, a manifest, and a function from the sealed
          inputs to the produced bundle. Inside <L>derive</L> the only sources
          are <L>inputs.current</L> and <L>inputs.get k</L> for declared{" "}
          <L>k</L>.
        </p>
        <LeanCode>{`
          @[reducible] noncomputable def boundRow : AtomicStrategy Residual :=
            factOnly \`Example.boundRow
              { Requires := [atMostTwo]
                Produces := [atMostThree]
                requiresUnique := by simp
                producesUnique := by simp
                producesNonempty := by simp }
              (fun inputs =>
                .cons (key := atMostThree)
                  ⟨Nat.le_trans (inputs.get atMostTwo).down (by decide)⟩ .nil)
        `}</LeanCode>
      </section>

      <section>
        <h2>A step that refines the residual</h2>
        <p>
          When a step also restricts the residual it supplies the three functions
          explicitly. This framework fixture clamps the residual to at most 2 and
          records that bound as a fact:
        </p>
        <LeanCode source="Hypostructure/Fixtures/ExactExecution.lean">{`
          abbrev ct : AtomicCT Residual :=
            AtomicCT.create exactLedgerInternal% \`ExactExecutionFixture.ct ctManifest
              (fun inputs => { value := min inputs.current.value 2 })   -- next
              (fun inputs => Nat.min_le_left inputs.current.value 2)     -- Refines next current
              (fun inputs => {                                            -- execute
                facts := .cons (key := atMostTwo)
                  ⟨Nat.min_le_right inputs.current.value 2⟩ .nil
                checks := 1
                work := 1 })
        `}</LeanCode>
        <p>
          The <L>Refines</L> proof is what the ledger will use to transport every
          inherited fact to the clamped residual when a later step reads it.
        </p>
      </section>

      <section>
        <h2>Running a step: AtomicCT.run</h2>
        <p>
          Running is the only write. It takes the executor and a ledger, checks
          at elaboration that every required key is present, and returns a
          ledger whose index is definitionally the produced keys in front of the
          inherited ones.
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/ExactExecution.lean">{`
          /-- Run and atomically append a CT.  Missing requirements fail during
          elaboration.  The result index contains every produced fact followed by every
          inherited fact, making history loss unrepresentable. -/
          noncomputable def AtomicCT.run
              {current : Residual} {known : FactKeys Residual}
              (ct : AtomicCT Residual)
              [FactKeys.Available ct.manifest.Requires known]
              (previous : ExactLedger Residual current known)
              (fresh : List.Disjoint ct.manifest.Produces known := by decide) :
              ExactLedger Residual (ct.outputResidual previous)
                (ct.manifest.Produces ++ known)
        `}</LeanCode>
        <ul>
          <li>
            <L>FactKeys.Available Requires known</L> is the readiness check: an
            instance exists exactly when every required key has a{" "}
            <L>FactKeys.Has</L> instance in <L>known</L>. It is what builds the
            sealed <L>FactInputs</L> the executor sees.
          </li>
          <li>
            <L>fresh</L> proves that no produced key is already on the branch.
            The default <L>by decide</L> works for concrete literal lists; when
            keys are defined by name, <L>by simp [k₁, k₂]</L> unfolds them
            first.
          </li>
          <li>
            <L>ct.outputResidual previous</L> is the residual the step
            chose, exposed as a projection so the output type can mention it
            without exposing the executor.
          </li>
        </ul>
        <LeanCode source="Hypostructure/Fixtures/ExactExecution.lean">{`
          def rootHistory := ExactLedger.root exactLedgerInternal% ({ value := 3 } : Residual)

          noncomputable def afterCT := ct.run rootHistory (by simp)
          -- afterCT : ExactLedger Residual (ct.outputResidual rootHistory) [atMostTwo]

          noncomputable def afterStrategy := AtomicCT.run strategy afterCT (by
            simp [atMostThree, atMostTwo])
          -- afterStrategy : ExactLedger Residual _ [atMostThree, atMostTwo]

          theorem no_fact_was_dropped :
              (ExactLedger.currentOf afterStrategy).value ≤ 2 :=
            (ExactLedger.get afterStrategy atMostTwo).down
        `}</LeanCode>
        <p>
          A step has no predecessor parameter, so the same value runs after any
          branch that is ready for it. The fixture runs <L>ct</L> both on the
          bare root and after an unrelated fact:
        </p>
        <LeanCode source="Hypostructure/Fixtures/ExactExecution.lean">{`
          def taggedRoot := ExactLedger.publishFact exactLedgerInternal% rootHistory auditTag ()

          /-- The same CT runs after an unrelated fact whenever its exact manifest is
          ready. -/
          noncomputable def afterTagThenCT := ct.run taggedRoot (by
            simp [atMostTwo, auditTag])

          theorem order_independent_run_preserves_unrelated_fact :
              ExactLedger.get afterTagThenCT auditTag = () := rfl
        `}</LeanCode>
        <p>
          A straight-line assembly is then a chain of <L>.run</L> calls, each
          applied to the previous ledger, with the result type spelled as the
          literal list of keys the branch has established.
        </p>
      </section>

      <section>
        <h2>Two-way decisions</h2>
        <p>
          A dichotomy is not a payload or a routing token: each arm is a
          distinct fact, and the arm a branch did not take is absent from that
          branch's index. <L>Decision</L> is the result type that makes this so.
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/FactOnlyStrategy.lean">{`
          /-- The outcome of a two-way decision.  The two constructors carry *different*
          key indices, so a consumer of one arm cannot read the other arm's fact: it is
          not in its type. -/
          inductive Decision {current : Residual} {known : FactKeys Residual}
              (left right : FactKey Residual)
              (_previous : ExactLedger Residual current known) where
            | left (history : ExactLedger Residual current (left :: known))
            | right (history : ExactLedger Residual current (right :: known))

          noncomputable def Decision.run
              {current : Residual} {known : FactKeys Residual}
              (previous : ExactLedger Residual current known)
              (left right : FactKey Residual)
              (id : Lean.Name)
              (alternatives : Sum (left.At current) (right.At current))
              (leftFresh : left ∉ known := by decide)
              (rightFresh : right ∉ known := by decide) :
              Decision left right previous
        `}</LeanCode>
        <p>
          The caller supplies the exhaustive alternative as a <L>Sum</L> of the
          two arms' values; whichever arm it returns is the fact that gets
          committed. Both arms commit against the same immutable prefix, so
          every fact proved before the decision is visible on both. How an
          arm is then closed — <L>Impossible</L>, <L>Incompatible</L>,{" "}
          <L>closeImpossible</L>, <L>closeIncompatible</L> and{" "}
          <L>ExactLedger.elimClosed</L> — is the subject of{" "}
          <Link to="/lean/closing">Closing a branch</Link>.
        </p>
      </section>

      <section>
        <h2>The framework's own writers</h2>
        <p>
          Underneath <L>run</L> and <L>Decision.run</L> sit the primitive
          writers. They take a <L>FrameworkToken</L> and are therefore callable
          only from <L>Hypostructure.*</L> modules; they are documented so the
          types can be read, not so applications can call them.
        </p>
        <LeanCode source="Hypostructure/Core/Residual/ExactLedger.lean">{`
          def ExactLedger.root (_authority : FrameworkToken) (residual : Residual) :
              ExactLedger Residual residual []

          /-- Publish one fact while preserving the residual definitionally. -/
          def ExactLedger.publishFact {current : Residual} {known : FactKeys Residual}
              (_authority : FrameworkToken)
              (previous : ExactLedger Residual current known)
              (key : FactKey Residual) (value : key.At current)
              (fresh : key ∉ known := by decide)
              (producer : Lean.Name := key.name) :
              ExactLedger Residual current (key :: known)

          /-- Framework commit.  Its result index is definitionally the new facts
          followed by every inherited fact, so dropping history is unrepresentable. -/
          def ExactLedger.append
              {previousResidual : Residual} {known produced : FactKeys Residual}
              (_authority : FrameworkToken)
              (previous : ExactLedger Residual previousResidual known)
              (next : Residual)
              (refinement : RefinementSystem.Refines next previousResidual)
              (facts : FactKeys.Values next produced)
              (producedNonempty : produced ≠ [])
              (producedUnique : produced.Nodup)
              (fresh : List.Disjoint produced known)
              (info : CommitInfo) :
              ExactLedger Residual next (produced ++ known)

          /-- Reindex the one canonical history through a proved refinement.  This is
          not a commit and cannot publish a theorem. -/
          noncomputable def ExactLedger.refine
              {current next : Residual} {known : FactKeys Residual}
              (_authority : FrameworkToken)
              (history : ExactLedger Residual current known)
              (refinement : RefinementSystem.Refines next current) :
              ExactLedger Residual next known

          /-- Initialize the first fact-bearing residual scope while retaining the
          literal empty predecessor.  Requiring an exactly empty input history makes
          this operation unusable after any fact has been proved. -/
          def ExactLedger.initializeScope
              {previousResidual : Residual} {produced : FactKeys Residual}
              (_authority : FrameworkToken)
              (previous : ExactLedger Residual previousResidual [])
              (next : Residual)
              (facts : FactKeys.Values next produced)
              (producedNonempty : produced ≠ [])
              (producedUnique : produced.Nodup)
              (info : CommitInfo) :
              ExactLedger Residual next produced
        `}</LeanCode>
        <p>
          <L>initializeScope</L> is the sole exception to "every transition is a
          refinement": it accepts only a ledger with an empty index, publishes
          the first nonempty bundle, and is therefore impossible after any fact
          or commit exists. Never archive, deactivate, reset or rebase an
          existing fact — the types do not permit it.
        </p>
      </section>

      <section>
        <h2>What the compiler rejects</h2>
        <LeanCode source="Hypostructure/Fixtures/ExactLedgerDuplicateFact.lean">{`
          def once := ExactLedger.publishFact exactLedgerInternal% rootHistory bound ⟨by decide⟩

          /--
          error: could not synthesize default value for parameter 'fresh' using tactics
          ---
          error: Tactic \`decide\` proved that the proposition
            bound ∉ [bound]
          is false
          -/
          #guard_msgs (error) in
          def duplicate := ExactLedger.publishFact exactLedgerInternal% once bound ⟨by decide⟩
        `}</LeanCode>
        <p>
          Likewise, running a step whose <L>Requires</L> is not on the branch
          fails to find <L>FactKeys.Available</L>, and an executor whose bundle
          does not match its <L>Produces</L> fails against{" "}
          <L>AtomicResult</L>. Each of these is a compile error in the proof
          module, before anything is checked by hand.
        </p>
      </section>
    </>
  );
}
