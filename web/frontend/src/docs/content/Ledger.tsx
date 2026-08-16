import { L, LeanCode } from "../LeanCode";

export function LedgerPage() {
  return (
    <>
      <header className="docs-header">
        <p className="hero-eyebrow">Core API</p>
        <h1>The ExactLedger</h1>
        <p className="docs-lead">
          <L>ExactLedger</L> is the only residual and proof-history carrier. It
          is one indexed type: the current residual and the complete branch-local
          fact set are part of its type, and every commit retains its literal
          predecessor. A commit can only refine the residual and prepend a
          nonempty, duplicate-free bundle of facts to the inherited index.
        </p>
      </header>

      <section>
        <h2>The type and its two indices</h2>
        <LeanCode source="Hypostructure/Core/Residual/ExactLedger.lean">{`
          inductive ExactLedger
              (Residual : Type) [RefinementSystem Residual] [FactSystem Residual] :
              Residual -> FactKeys Residual -> Type where
            | private seed  ...   -- the root: a residual and no facts
            | private step  ...   -- a commit: refine the residual, prepend facts
            | private scope ...   -- the one first-scope initialization
        `}</LeanCode>
        <p>
          A value of <L>ExactLedger Residual current known</L> is a branch whose
          active residual is <L>current</L> and on which exactly the facts named
          in <L>known</L> have been established. Both are type indices, not
          fields: to know what a branch has proved you read its type, and to
          extend a branch you must produce a value of a type whose index is the
          old one with something in front of it.
        </p>
        <p>
          All three constructors are private. Nothing outside the framework can
          build a ledger by hand, and nothing can pattern-match on one: a
          consumer sees only the public accessors on the next pages, and never a
          predecessor, a fact bundle, or a proof term.
        </p>
      </section>

      <section>
        <h2>The residual domain: RefinementSystem</h2>
        <p>
          A ledger is generic over the <em>residual domain</em> — the type of
          the problem state a branch argues about. The domain supplies the laws
          of restriction through one class:
        </p>
        <LeanCode source="Hypostructure/Core/Residual/ExactLedger.lean">{`
          /-- Domain-independent laws for residual restriction.  The orientation is
          \`Refines next previous\`: execution may preserve or restrict a residual, never
          replace it by an unrelated state. -/
          class RefinementSystem (Residual : Type) where
            Subject : Type
            subject : Residual -> Subject
            Refines : Residual -> Residual -> Prop
            refl : (residual : Residual) -> Refines residual residual
            trans : {new middle old : Residual} ->
              Refines new middle -> Refines middle old -> Refines new old
            subject_eq : {new old : Residual} -> Refines new old ->
              subject new = subject old
        `}</LeanCode>
        <p>
          <L>Refines new old</L> is the only way a residual is allowed to change
          along a branch. It is reflexive and transitive, and it fixes the{" "}
          <L>Subject</L> — the object the whole branch is about — so a step may
          narrow what is known of the object but never swap the object out.
        </p>
      </section>

      <section>
        <h2>The fact vocabulary: FactSystem</h2>
        <p>
          Each residual domain has exactly one <L>FactSystem</L>. It is a closed
          vocabulary of <em>keys</em>; each key names one statement schema, one
          audit name and one way of transporting its proof along a refinement.
        </p>
        <LeanCode source="Hypostructure/Core/Residual/ExactLedger.lean">{`
          class FactSystem (Residual : Type) [RefinementSystem Residual] where
            Key : Type
            keyDecidableEq : DecidableEq Key
            name : Key -> Lean.Name
            name_injective : Function.Injective name
            Value : Key -> Residual -> Sort _
            /-- A fact value carries no data. -/
            value_subsingleton : (key : Key) -> (residual : Residual) ->
              Subsingleton (Value key residual)
            transport : {key : Key} -> {new old : Residual} ->
              RefinementSystem.Refines new old -> Value key old -> Value key new
            closureKey : Key
            closure_name : name closureKey = closureFactName
            closureValue : (residual : Residual) ->
              ClosureEvidence -> Value closureKey residual
            closureEvidence : (residual : Residual) ->
              Value closureKey residual -> ClosureEvidence
        `}</LeanCode>
        <ul>
          <li>
            <strong>Keys, not names, are the identity.</strong> <L>Key</L> has
            decidable equality and routing tests the exact semantic key.{" "}
            <L>name</L> is injective and serves diagnostics and the audit view;
            it is never a type cast, so two unrelated facts cannot impersonate
            one another by sharing a display name.
          </li>
          <li>
            <strong>A fact value carries no data.</strong>{" "}
            <L>value_subsingleton</L> makes every <L>Value key residual</L> have
            at most one inhabitant. Holding a fact tells a consumer that the
            statement is established, and nothing else: there is no component
            to read back and no choice a producer could encode into one. A
            record with an <em>origin</em>, a <em>payload</em> or a{" "}
            <em>summary</em> is not a subsingleton, so it cannot be installed as
            a fact vocabulary at all — a parallel carrier fails to elaborate
            instead of quietly coexisting with the ledger.
          </li>
          <li>
            <strong>Facts survive refinement.</strong> <L>transport</L> carries
            a value from the old residual to the refined one. A fact that is not
            refinement-stable cannot be a ledger fact.
          </li>
          <li>
            <strong>Every domain has a closure key.</strong> <L>closureKey</L>{" "}
            is the one reserved key that marks a closed branch; its value is a{" "}
            <L>ClosureEvidence</L>, which contains a proof of <L>False</L>.
          </li>
        </ul>
        <p>
          Two convenient names sit on top of the class. <L>FactKey Residual</L>{" "}
          is the domain's key type, and <L>key.At residual</L> is the value type{" "}
          <L>system.Value key residual</L> — "the statement <L>key</L> makes
          about <L>residual</L>". <L>FactKeys Residual</L> is a list of keys: the
          shape of the ledger's second index.
        </p>
      </section>

      <section>
        <h2>No fact is a side channel</h2>
        <p>
          Because values are subsingletons, transport is automatically a
          homomorphism (<L>FactSystem.transport_refl</L>,{" "}
          <L>FactSystem.transport_trans</L>) and, more importantly, nothing a
          consumer computes from a fact can depend on which proof it was handed:
        </p>
        <LeanCode source="Hypostructure/Core/Residual/ExactLedger.lean">{`
          /-- **No fact is a side channel.**  Every reading of a fact value is constant
          in that value, so nothing a consumer computes from a fact depends on *which*
          proof it was handed -- only on the key and the residual, both of which are
          already public. -/
          theorem FactKey.no_data_channel
              {Observation : Sort w} {key : FactKey Residual} {residual : Residual}
              (read : key.At residual -> Observation) (left right : key.At residual) :
              read left = read right :=
            congrArg read (Subsingleton.elim left right)
        `}</LeanCode>
        <p>
          This is the formal content of "the canonical ledger is the single
          source of truth", and it holds in every domain by construction. The
          only thing that flows from step to step is the residual, and the only
          way it flows is <L>Refines</L>.
        </p>
      </section>

      <section>
        <h2>What a commit must satisfy</h2>
        <p>
          Every commit that extends a ledger from index <L>known</L> to{" "}
          <L>produced ++ known</L> carries, in its type, four obligations:
        </p>
        <ol>
          <li>
            a proof of <L>RefinementSystem.Refines next previous</L> for the
            residual change (the identity refinement <L>refl</L> when a step only
            adds facts);
          </li>
          <li>
            <L>produced ≠ []</L> — a commit that publishes nothing is not a
            commit;
          </li>
          <li>
            <L>produced.Nodup</L> — no key is published twice in one bundle;
          </li>
          <li>
            <L>List.Disjoint produced known</L> — no key already on the branch is
            published again.
          </li>
        </ol>
        <p>
          The result index is definitionally the new keys followed by every
          inherited key, so dropping, archiving or rebasing history is not
          something one refrains from doing: it is unrepresentable.
        </p>
      </section>

      <section>
        <h2>Framework authority</h2>
        <p>
          The constructors of the ledger, and of steps, are not an
          application API. They take a <L>FrameworkToken</L>, whose only
          constructor and only value are private. A term elaborator emits that
          value only while compiling a framework module:
        </p>
        <LeanCode source="Hypostructure/Core/Residual/ExactLedger.lean">{`
          /-- Unforgeable authority required by framework-only construction
          operations.  Its sole constructor and sole value are private. -/
          structure FrameworkToken where
            private mk ::

          /-- Internal term emitted only inside framework-owned modules. -/
          syntax (name := exactLedgerInternalToken) "exactLedgerInternal%" : term

          elab_rules : term
            | \`(exactLedgerInternal%) => do
                let moduleName := (← getEnv).mainModule.toString
                unless moduleName.startsWith "Hypostructure." do
                  throwError "the canonical ledger construction token is internal to framework modules"
                pure (mkConst \`\`frameworkToken)
        `}</LeanCode>
        <p>
          In practice this means an application proof (a module outside{" "}
          <L>Hypostructure.*</L>) cannot call <L>ExactLedger.root</L>,{" "}
          <L>ExactLedger.append</L>, <L>ExactLedger.publishFact</L>,{" "}
          <L>ExactLedger.refine</L>, <L>ExactLedger.initializeScope</L>,{" "}
          <L>FactInputs.ofLedger</L> or <L>AtomicCT.create</L>. It receives a
          ledger from a framework-owned scope, reads it through the sealed
          accessors, and extends it only by running executors built from the
          registered combinators. Restarting or rescoping an active residual is
          history loss, and the type system refuses it.
        </p>
      </section>

      <section>
        <h2>A complete small domain</h2>
        <p>
          The framework's own fixture is the shortest full example. The residual
          is a natural number, refinement is "at most", and the vocabulary has
          two bounds plus the mandatory closure key.
        </p>
        <LeanCode source="Hypostructure/Fixtures/ExactLedger.lean">{`
          structure Residual where value : Nat

          instance : RefinementSystem Residual where
            Subject := Unit
            subject := fun _ => ()
            Refines new old := new.value ≤ old.value
            refl := fun _ => Nat.le_refl _
            trans := Nat.le_trans
            subject_eq := fun _ => rfl

          inductive Key where
            | upperFive
            | upperThree
            | contradiction
            deriving DecidableEq

          instance : FactSystem Residual where
            Key := Key
            keyDecidableEq := inferInstance
            name
              | .upperFive => \`UpperFive
              | .upperThree => \`UpperThree
              | .contradiction => closureFactName
            name_injective := by
              intro left right same
              cases left <;> cases right <;> simp_all [closureFactName]
            Value
              | .upperFive, residual => PLift (residual.value ≤ 5)
              | .upperThree, residual => PLift (residual.value ≤ 3)
              | .contradiction, _ => ClosureEvidence
            value_subsingleton := by
              intro key residual
              cases key <;>
                exact ⟨fun left right => by
                  first
                    | exact left.contradiction.elim
                    | (cases left; cases right; rfl)⟩
            transport := by
              intro key new old refinement value
              cases key with
              | upperFive => exact ⟨refinement.trans value.down⟩
              | upperThree => exact ⟨refinement.trans value.down⟩
              | contradiction => exact value
            closureKey := .contradiction
            closure_name := rfl
            closureValue _ evidence := evidence
            closureEvidence _ evidence := evidence

          def upperFive : FactKey Residual := .upperFive
          def upperThree : FactKey Residual := .upperThree
        `}</LeanCode>
        <p>
          Note the shape of a value: a proposition wrapped in <L>PLift</L> so it
          lives in <L>Type</L>, which is trivially a subsingleton. The{" "}
          <L>transport</L> for <L>upperFive</L> is the observation that if{" "}
          <L>new.value ≤ old.value</L> and <L>old.value ≤ 5</L> then{" "}
          <L>new.value ≤ 5</L>: exactly the refinement-stability the ledger asks
          for.
        </p>
        <p>
          With the domain in place, a framework module can build a branch. Here
          the root has residual 5, one fact is published, and one commit refines
          the residual to 3 while adding a second fact:
        </p>
        <LeanCode source="Hypostructure/Fixtures/ExactLedger.lean">{`
          def rootHistory := ExactLedger.root exactLedgerInternal% ({ value := 5 } : Residual)

          def withBound := ExactLedger.publishFact exactLedgerInternal% rootHistory upperFive ⟨by decide⟩

          def advanced :
              ExactLedger Residual ({ value := 3 } : Residual)
                [upperThree, upperFive] :=
            ExactLedger.append exactLedgerInternal% withBound { value := 3 } (by
                change (3 : Nat) ≤ 5
                decide)
              (.cons (key := upperThree) ⟨Nat.le_refl 3⟩ .nil)
              (by simp) (by simp) (by simp [upperThree, upperFive])
              { producer := \`ExactLedgerFixture.advance }
        `}</LeanCode>
        <p>
          Read the type of <L>advanced</L> back: the branch is at residual 3 and
          has established <L>upperThree</L> and, still, <L>upperFive</L>. The
          next page shows how those facts are read.
        </p>
      </section>
    </>
  );
}
