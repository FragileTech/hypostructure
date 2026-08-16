import { Link } from "react-router-dom";

import { Latex, MathProvider, createReferenceResolver, indexDocument } from "../graph-explorer";
import { useProof } from "../hooks/useProof";
import { useProofDocument } from "../hooks/useProofDocument";
import { ErrorPanel, LoadingPanel } from "../components/RequestPanels";
import { NotFoundPage } from "./NotFoundPage";

export function NotationPage() {
  const proof = useProof();
  const request = useProofDocument(proof?.slug ?? "");

  if (!proof) return <NotFoundPage />;
  if (request.status === "loading") return <LoadingPanel />;
  if (request.status === "error") return <ErrorPanel error={request.error} />;

  const { document } = request;
  const index = indexDocument(document);
  const references = createReferenceResolver(document, index);
  // Some papers tabulate numerical constants, others a glossary of symbols.
  const numeric = document.constants.some((constant) => constant.value.trim());

  return (
    <MathProvider macros={document.macros} resolveReference={references.resolve}>
      <div className="page page-notation">
        <header className="hero hero-compact">
          <h1>Notation and standing constraints</h1>
          <p className="hero-lead">
            The {numeric ? "numbers" : "objects"} the proof depends on, and the
            conditions it forces to hold from one step to the next.
          </p>
        </header>

        <section className="panel">
          <h2>{numeric ? "Constants" : "Symbols"}</h2>
          <p className="panel-lead">
            {numeric
              ? "Each is a finite computation. The proof closes because a few of these values sit on the correct side of an inequality — and not by much."
              : "The recurring objects the argument names, and what each one measures."}
          </p>
          <table className="data-table">
            <thead>
              <tr>
                <th>Symbol</th>
                {numeric ? <th>Value</th> : null}
                <th>What it measures</th>
              </tr>
            </thead>
            <tbody>
              {document.constants.map((constant) => (
                <tr key={constant.symbol}>
                  <th scope="row">
                    <Latex value={constant.symbol} />
                  </th>
                  {numeric ? (
                    <td className="numeric">
                      <Latex value={constant.value} />
                    </td>
                  ) : null}
                  <td>
                    <Latex value={constant.meaning} />
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </section>

        <section className="panel">
          <h2>Standing constraints</h2>
          <p className="panel-lead">
            Once established, each of these holds for the rest of the argument.
            The step column links to where it is first tracked.
          </p>
          <table className="data-table">
            <thead>
              <tr>
                <th>#</th>
                <th>Constraint</th>
                <th>What it says</th>
                <th>First tracked at</th>
              </tr>
            </thead>
            <tbody>
              {document.invariants.map((invariant) => (
                <tr key={invariant.id}>
                  <th scope="row">
                    {invariant.number}
                    {document.chapters ? (
                      <small className="row-chapter">
                        {index.chapterById.get(invariant.chapter ?? "")?.shortTitle}
                      </small>
                    ) : null}
                  </th>
                  <td>
                    <Latex value={invariant.name} />
                  </td>
                  <td>
                    <Latex value={invariant.constraint} />
                  </td>
                  <td className="step-links">
                    {invariant.nodes.length
                      ? invariant.nodes.map((id) => (
                          <Link
                            key={id}
                            className="chip chip-node"
                            to={`/${proof.slug}/explore?step=${id}`}
                          >
                            {id}
                          </Link>
                        ))
                      : "—"}
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </section>

        <section className="panel">
          <h2>Results by kind</h2>
          <p className="panel-lead">
            The papers state {document.items.length} named results. Open any step
            in the explorer to read the ones behind it; the rest are reachable
            from the references inside those statements and proofs.
          </p>
          <dl className="stat-row">
            {(["theorem", "proposition", "lemma", "corollary", "definition"] as const).map(
              (kind) => (
                <div key={kind}>
                  <dt>{kind}s</dt>
                  <dd>{document.items.filter((item) => item.kind === kind).length}</dd>
                </div>
              ),
            )}
            <div>
              <dt>steps with results</dt>
              <dd>{document.nodes.filter((node) => node.itemRefs.length).length}</dd>
            </div>
          </dl>
        </section>
      </div>
    </MathProvider>
  );
}
