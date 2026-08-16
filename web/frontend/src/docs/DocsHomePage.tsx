import { Link } from "react-router-dom";

import { L, LeanCode } from "./LeanCode";
import { DOCS_GROUPS, DOCS_PAGES, docsPath } from "./registry";

/** The front page of the Lean Framework section. */
export function DocsHomePage() {
  return (
    <article className="docs-article docs-home">
      <header className="hero hero-compact">
        <p className="hero-eyebrow">Lean Framework</p>
        <h1>The hypostructure framework</h1>
        <p className="hero-lead">
          Hypostructure is a Lean 4 library for writing structural exhaustion
          proofs so that the proof <em>is</em> the audit. A branch of an argument
          is one value of one indexed type, and everything a referee would want
          to check — which facts a step may use, that no fact is ever dropped,
          that nothing travels between steps except through the residual — is
          decided by the type checker rather than by inspection.
        </p>
      </header>

      <section>
        <h2>One carrier</h2>
        <p>
          The state of a branch is carried by a single type, indexed by the
          active residual problem and by the complete list of facts established
          on the branch:
        </p>
        <LeanCode>{`
          ExactLedger Residual current known
          --          ^        ^       ^
          --          |        |       the exact keys of every fact on the branch
          --          |        the active residual
          --          the residual domain, with one RefinementSystem and one FactSystem
        `}</LeanCode>
        <p>
          Putting the residual and the fact index into the type is what gives
          the framework its properties.
        </p>
        <dl className="docs-properties">
          <div>
            <dt>Availability</dt>
            <dd>
              A step declares its hypotheses in a <L>FactManifest</L>; those keys
              are matched against the ledger's index when the file elaborates.
              Running a step on a branch that has not established its hypotheses
              is a type error, not an omission for a referee to notice.
            </dd>
          </div>
          <div>
            <dt>Retention</dt>
            <dd>
              Commits prepend to the index. Every predecessor fact remains present
              and queryable at the refined residual, because each transition
              carries a <L>RefinementSystem.Refines</L> proof that transports it.
            </dd>
          </div>
          <div>
            <dt>No side channels</dt>
            <dd>
              Each residual domain has one <L>FactSystem</L>, and{" "}
              <L>FactSystem.value_subsingleton</L> makes every fact value
              proof-irrelevant. Data cannot ride between steps inside a fact:
              whatever a later step uses is an observable of the object or a
              declared production of an earlier step.
            </dd>
          </div>
          <div>
            <dt>Position independence</dt>
            <dd>
              An <L>AtomicCT</L> takes no predecessor. It runs after any branch
              branch whose ledger contains its requirements, so a proof cannot
              encode an authored order and then rely on it.
            </dd>
          </div>
          <div>
            <dt>Auditability</dt>
            <dd>
              <L>ExactLedger.audit</L> reports the fact names and the
              chronological commits without exposing proof terms, and three
              theorems certify that this view accounts for the same append-only
              history the type does.
            </dd>
          </div>
        </dl>
        <p>
          The constraint is exclusive rather than preferential: <L>ExactLedger</L>{" "}
          is the only carrier of residual state, proof history and facts, and no
          second carrier is permitted under any name.
        </p>
      </section>

      <section>
        <h2>What is documented</h2>
        <p>
          Four groups, in reading order. <strong>The ledger</strong> is the
          core: what the ledger is, how a step reads facts, how it writes them,
          and how a branch closes. <strong>Defining a problem</strong> is the
          one problem-specific input and what Core derives from it.{" "}
          <strong>Assembling a proof</strong> is how steps, decisions and closures
          compose into the public theorem, plus the reusable replacement
          exclusion. <strong>Reference</strong> lists every public declaration
          with its verbatim signature.
        </p>
        {DOCS_GROUPS.map((group) => (
          <div key={group.id} className="docs-card-group">
            <h3>{group.title}</h3>
            <ul className="docs-cards">
              {DOCS_PAGES.filter((page) => page.group === group.id).map((page) => (
                <li key={page.slug}>
                  <Link to={docsPath(page)}>
                    <h4>{page.title}</h4>
                    <p>{page.summary}</p>
                  </Link>
                </li>
              ))}
            </ul>
          </div>
        ))}
      </section>

      <section>
        <h2>Vocabulary</h2>
        <p>
          The pages use one word per concept, matched to the Lean names in
          parentheses.
        </p>
        <dl className="docs-properties docs-vocabulary">
          <div>
            <dt>Ledger</dt>
            <dd>
              A value of <L>ExactLedger Residual current known</L>: the active
              residual and every fact on the branch, as type indices. In
              signatures the ledger argument is conventionally called{" "}
              <L>history</L>.
            </dd>
          </div>
          <div>
            <dt>Fact, key</dt>
            <dd>
              A key (<L>FactKey</L>) is a name from the domain's vocabulary; a
              fact is the key established on a branch, with value{" "}
              <L>key.At residual</L>. Facts carry no data.
            </dd>
          </div>
          <div>
            <dt>Step</dt>
            <dd>
              One atomic unit of a proof: a manifest of what it requires and
              produces, and a sealed derivation (<L>AtomicCT</L>; its synonym{" "}
              <L>AtomicStrategy</L> is a leftover of an older CT/Strategy
              distinction). Fact-only steps are built with <L>factOnly</L>. A
              step is <em>run</em> against a ledger with <L>AtomicCT.run</L>.
            </dd>
          </div>
          <div>
            <dt>Executor</dt>
            <dd>
              The sealed function inside a step that receives{" "}
              <L>FactInputs</L> — the current residual and exactly the declared
              facts — and returns the produced bundle.
            </dd>
          </div>
          <div>
            <dt>Commit</dt>
            <dd>
              One entry of the proof history: a run step, a decided arm, or a
              closure, as the audit records it (<L>CommitRecord</L>).
            </dd>
          </div>
          <div>
            <dt>Branch, arm, leaf</dt>
            <dd>
              A branch is one case of the argument, identified with its ledger.
              A decision (<L>Decision.run</L>) splits a branch into two arms. A
              leaf is a branch that closes — returns <L>False</L>.
            </dd>
          </div>
          <div>
            <dt>Assembly</dt>
            <dd>
              The composed proof of one problem: steps run in sequence,
              decisions, and closed leaves, ending in the public statement.
            </dd>
          </div>
        </dl>
      </section>

      <section>
        <h2>How to read this reference</h2>
        <p>
          The ledger lives in <L>Hypostructure.Core.Residual</L>; manifests,
          executors and decisions in <L>Hypostructure.Core.Strategy</L>. Both
          namespaces are opened in every example. Signatures are quoted from the
          live sources under <code>hypostructure/Hypostructure/Core/</code>, with
          the universe annotations left out.
        </p>
        <p>
          A few operations take a <L>FrameworkToken</L>. That token is emitted by
          the <L>exactLedgerInternal%</L> elaborator only while compiling a{" "}
          <L>Hypostructure.*</L> module, so those operations are the framework's
          own construction boundary: an application proof reads and extends the
          ledger only through the sealed executors described here. Each entry of
          the reference is marked <span className="docs-badge">application</span>{" "}
          or <span className="docs-badge is-framework">framework-only</span>{" "}
          accordingly.
        </p>
      </section>
    </article>
  );
}
