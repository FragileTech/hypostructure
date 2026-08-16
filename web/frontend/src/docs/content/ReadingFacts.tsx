import { L, LeanCode } from "../LeanCode";

export function ReadingFactsPage() {
  return (
    <>
      <header className="docs-header">
        <p className="hero-eyebrow">Core API</p>
        <h1>Reading facts</h1>
        <p className="docs-lead">
          A fact is read by its exact key, never by who produced it, in which
          step, or how far back. Whether the key is available on the branch is a
          type-class question the elaborator answers; a missing fact is a
          compile error, not a runtime lookup failure.
        </p>
      </header>

      <section>
        <h2>Availability is a type-class check</h2>
        <p>
          The ledger's second index, <L>known : FactKeys Residual</L>, is a
          list of keys. Membership in it is witnessed structurally:
        </p>
        <LeanCode source="Hypostructure/Core/Residual/ExactLedger.lean">{`
          /-- A structural position of one exact key in a fact list. -/
          inductive FactKeys.Member (key : FactKey Residual) : FactKeys Residual -> Type _ where
            | head : Member key (key :: tail)
            | tail : Member key tail -> Member key (other :: tail)

          class FactKeys.Has (key : FactKey Residual) (keys : FactKeys Residual) where
            member : Member key keys
        `}</LeanCode>
        <p>
          <L>FactKeys.Has key known</L> is found automatically by instance
          search: there are instances for the head of a cons, for the tail of a
          cons, and for either side of an append. When a proof writes{" "}
          <L>ExactLedger.get history key</L>, Lean searches <L>known</L> for{" "}
          <L>key</L> at elaboration time. If it is there, the read type-checks;
          if not, the instance is not found and the file does not compile.
        </p>
        <p>
          <L>FactKeys.Member.ofMem</L> converts an ordinary proposition{" "}
          <L>key ∈ keys</L> into the structural witness, for callers whose
          readiness check already yields a membership proof.
        </p>
      </section>

      <section>
        <h2>Reading from a ledger</h2>
        <p>
          At a framework-owned closure boundary — where a whole ledger is in
          hand — three accessors read it:
        </p>
        <LeanCode source="Hypostructure/Core/Residual/ExactLedger.lean">{`
          /-- The active residual is an index, not a value travelling beside history. -/
          def ExactLedger.currentOf {current : Residual} {known : FactKeys Residual}
              (_history : ExactLedger Residual current known) : Residual :=
            current

          /-- Retrieve a fact without naming its producer, row, or predecessor depth. -/
          noncomputable def ExactLedger.get {current : Residual} {known : FactKeys Residual}
              (history : ExactLedger Residual current known)
              (key : FactKey Residual) [FactKeys.Has key known] : key.At current

          /-- Retrieve a fact from a proposition-level readiness proof.  The semantic
          key still determines the value schema, and absence is an elaboration error
          because callers must supply \`key ∈ known\`. -/
          noncomputable def ExactLedger.getPresent {current : Residual} {known : FactKeys Residual}
              (history : ExactLedger Residual current known)
              (key : FactKey Residual) (present : key ∈ known) : key.At current
        `}</LeanCode>
        <p>
          The result type of <L>get</L> is <L>key.At current</L>: the statement
          the key makes, <em>at the active residual</em>. A fact that was
          committed several refinements ago is handed back already transported to
          the current residual — the ledger materializes every inherited value
          through the <L>Refines</L> proofs stored in its commits, so the reader
          never sees or supplies a transport.
        </p>
        <p>Continuing the domain from the previous page:</p>
        <LeanCode source="Hypostructure/Fixtures/ExactLedger.lean">{`
          -- advanced : ExactLedger Residual { value := 3 } [upperThree, upperFive]

          noncomputable def inheritedBound : upperFive.At (ExactLedger.currentOf advanced) :=
            ExactLedger.get advanced upperFive

          theorem transition_fact_is_indexed :
              (ExactLedger.currentOf advanced).value ≤ 3 :=
            (ExactLedger.get advanced upperThree).down

          theorem prior_fact_is_found_without_a_path :
              (ExactLedger.currentOf advanced).value ≤ 5 :=
            inheritedBound.down
        `}</LeanCode>
        <p>
          <L>upperFive</L> was published when the residual was 5; it is read at
          residual 3 with no mention of the commit that produced it or of the
          refinement in between.
        </p>
      </section>

      <section>
        <h2>Reading inside an executor: FactInputs</h2>
        <p>
          A step never holds the ledger. Its executor receives a sealed{" "}
          <L>FactInputs</L> view: the current residual and exactly the facts it
          declared in its manifest's <L>Requires</L>. It holds no ledger,
          no predecessor path, and no way to reach a fact it did not declare.
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/FactManifest.lean">{`
          /-- The complete view supplied to an atomic executor.  It contains no ledger
          cursor and exposes no predecessor path. -/
          structure FactInputs (requirements : FactRequirements Residual) where
            private mk ::
            current : Residual
            private facts : FactKeys.Values current requirements.Requires

          /-- Read one declared prerequisite.  Undeclared keys are rejected during
          elaboration. -/
          noncomputable def FactInputs.get
              {requirements : FactRequirements Residual} (inputs : FactInputs requirements)
              (key : FactKey Residual)
              [FactKeys.Has key requirements.Requires] :
              key.At inputs.current
        `}</LeanCode>
        <p>
          The instance argument is <L>Has key requirements.Requires</L>, not{" "}
          <L>Has key known</L>: the executor can read only what it declared,
          even if the branch happens to know more. This is what makes a step
          position-independent — its meaning depends on its manifest alone, so
          it can run after any branch whose ledger satisfies that manifest.
        </p>
        <LeanCode source="Hypostructure/Fixtures/ExactExecution.lean">{`
          abbrev strategyManifest : FactManifest Residual where
            Requires := [atMostTwo]
            Produces := [atMostThree]
            requiresUnique := by simp
            producesUnique := by simp
            producesNonempty := by simp

          -- inside the executor: read the declared prerequisite and use it
          (fun inputs => {
            facts := .cons (key := atMostThree) ⟨by
              exact Nat.le_trans (inputs.get atMostTwo).down (by decide)⟩ .nil })
        `}</LeanCode>
        <p>
          <L>inputs.current</L> is the residual the step was handed. It is the
          only thing besides declared facts that an executor can inspect.
        </p>
      </section>

      <section>
        <h2>What the compiler rejects</h2>
        <p>
          The framework's negative fixtures pin the exact errors. Reading a fact
          that is not on the branch:
        </p>
        <LeanCode source="Hypostructure/Fixtures/ExactLedgerMissingFact.lean">{`
          def history := ExactLedger.root exactLedgerInternal% ({ value := 1 } : Residual)

          /--
          error: failed to synthesize instance of type class
            FactKeys.Has missing []
          -/
          #guard_msgs (error) in
          example : missing.At (ExactLedger.currentOf history) :=
            ExactLedger.get history missing
        `}</LeanCode>
        <p>Reading a fact an executor did not declare, even though the branch has other facts:</p>
        <LeanCode source="Hypostructure/Fixtures/LedgerAutorouting.lean">{`
          -- inputs : FactInputs requiresA.toFactRequirements, where Requires := [factA]

          /--
          error: failed to synthesize instance of type class
            FactKeys.Has factB requiresA.Requires
          -/
          #guard_msgs (error) in
          example : factB.At (ExactLedger.currentOf history) :=
            inputs.get factB
        `}</LeanCode>
      </section>

      <section>
        <h2>Reading the proof history: audit</h2>
        <p>
          Besides facts, a ledger can be asked what happened on the branch. The
          audit view is proof-free: names and counts, never proof terms or fact
          bundles.
        </p>
        <LeanCode source="Hypostructure/Core/Residual/ExactLedger.lean">{`
          /-- Proof-free audit coordinates retained for every commit. -/
          structure CommitInfo where
            producer : Lean.Name
            checks : Nat := 0
            work : Nat := 0

          /-- Public, proof-free record of one atomic commit.  \`produced\` lists the exact
          semantic keys appended by that commit; it contains no theorem payload. -/
          structure CommitRecord where
            produced : List Lean.Name
            info : CommitInfo

          /-- Complete proof-free audit view of one branch.  Facts are newest-first and
          commits are chronological from the root. -/
          structure AuditSnapshot where
            facts : List Lean.Name
            commits : List CommitRecord

          /-- Inspect the complete proof history without exposing constructors, fact
          bundles, predecessor cursors, or proof terms. -/
          def ExactLedger.audit (history : ExactLedger Residual current known) : AuditSnapshot

          /-- The newest audit record, absent only at the root. -/
          def ExactLedger.latestInfo? (history : ExactLedger Residual current known) : Option CommitInfo
        `}</LeanCode>
        <p>Three theorems certify that this view is faithful to the type:</p>
        <LeanCode source="Hypostructure/Core/Residual/ExactLedger.lean">{`
          /-- Every fact is accounted for by exactly one chronological commit. -/
          theorem ExactLedger.audit_complete (history : ExactLedger Residual current known) :
              (audit history).facts =
                (audit history).commits.reverse.flatMap (fun record => record.produced)

          /-- No semantic fact occurs twice in an exact ledger. -/
          theorem ExactLedger.audit_facts_unique (history : ExactLedger Residual current known) :
              (audit history).facts.Nodup

          /-- Every audit commit contributes at least one semantic fact. -/
          theorem ExactLedger.audit_commits_nonempty (history : ExactLedger Residual current known) :
              (audit history).commits.Forall fun record => record.produced ≠ []
        `}</LeanCode>
        <p>On the fixture branch, both views are decidable by <L>rfl</L>:</p>
        <LeanCode source="Hypostructure/Fixtures/ExactLedger.lean">{`
          theorem audit_lists_every_available_fact :
              (ExactLedger.audit advanced).facts = [\`UpperThree, \`UpperFive] :=
            rfl

          theorem audit_retains_every_commit_in_root_order :
              (ExactLedger.audit advanced).commits.map (fun record => record.info.producer) =
                [\`UpperFive, \`ExactLedgerFixture.advance] :=
            rfl
        `}</LeanCode>
        <p>
          The audit is for reporting. Mathematical facts are retrieved only with{" "}
          <L>FactInputs.get</L> inside an executor or <L>ExactLedger.get</L> at a
          framework-owned closure boundary; the audit's names are never a lookup
          key.
        </p>
      </section>
    </>
  );
}
