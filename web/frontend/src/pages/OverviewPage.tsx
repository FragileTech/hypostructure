import { Link } from "react-router-dom";

import { Latex, MathProvider, createReferenceResolver, indexDocument } from "../graph-explorer";
import { useProof } from "../hooks/useProof";
import { useProofDocument } from "../hooks/useProofDocument";
import { ErrorPanel, LoadingPanel } from "../components/RequestPanels";
import { EGStructuralSurvey } from "../structural-survey/EGStructuralSurvey";
import { NotFoundPage } from "./NotFoundPage";

export function OverviewPage() {
  const proof = useProof();
  const request = useProofDocument(proof?.slug ?? "");

  if (!proof) return <NotFoundPage />;
  if (request.status === "loading") return <LoadingPanel />;
  if (request.status === "error") return <ErrorPanel error={request.error} />;

  const { document } = request;
  const terminals = document.nodes.filter((node) => node.shape === "terminal").length;
  const decisions = document.nodes.filter((node) => node.shape === "decision").length;
  const chapters = document.chapters ?? [];
  // Names the panels and results a caption points at, instead of printing keys.
  const references = createReferenceResolver(document, indexDocument(document));

  return (
    <MathProvider macros={document.macros} resolveReference={references.resolve}>
      <div className="page page-overview">
        <header className="hero">
          <p className="hero-eyebrow">{proof.name}</p>
          <h1>{proof.question}</h1>
          <p className="hero-lead">{proof.overview[0]}</p>
          <p className="hero-actions">
            <Link className="button" to={`/${proof.slug}/explore?step=${document.nodes[0].id}`}>
              Start at the first step
            </Link>
            <Link className="button button-quiet" to={`/${proof.slug}/explore`}>
              Open the whole diagram
            </Link>
          </p>
        </header>

        <section className="panel">
          <h2>How the argument is shaped</h2>
          {proof.overview.slice(1).map((paragraph) => (
            <p key={paragraph.slice(0, 40)}>
              <Latex value={paragraph} />
            </p>
          ))}
          <dl className="stat-row">
            <div>
              <dt>steps in the diagram</dt>
              <dd>{document.nodes.length}</dd>
            </div>
            <div>
              <dt>branch tests</dt>
              <dd>{decisions}</dd>
            </div>
            <div>
              <dt>branches that close</dt>
              <dd>{terminals}</dd>
            </div>
            <div>
              <dt>named results</dt>
              <dd>{document.items.length}</dd>
            </div>
          </dl>
        </section>

        {chapters.map((chapter) => {
          const panels = document.groups.filter((group) => group.chapter === chapter.id);
          const members = document.nodes.filter((node) => node.chapter === chapter.id);
          return (
            <section className="panel" key={chapter.id}>
              <h2>
                {chapter.title}{" "}
                <span className="panel-count">
                  {members[0].id}–{members[members.length - 1].id}
                </span>
              </h2>
              <p className="panel-lead">{chapter.description}</p>
              <PanelGrid slug={proof.slug} groups={panels} document={document} />
            </section>
          );
        })}

        {chapters.length === 0 ? (
          <section className="panel">
            <h2>The {document.groups.length} panels</h2>
            <p className="panel-lead">
              The paper draws its dependency diagram across several figures. They
              form one connected argument: each panel opens the explorer focused
              on that stretch of it.
            </p>
            <PanelGrid slug={proof.slug} groups={document.groups} document={document} />
          </section>
        ) : null}

        <EGStructuralSurvey document={document} />

        <footer className="page-footer">
          Every statement, branch label and constant on this site is read directly
          from the source of {document.source.files.map((file) => <code key={file}>{file}</code>)}.
        </footer>
      </div>
    </MathProvider>
  );
}

/**
 * How many steps a panel holds, as a range where that is truthful.
 *
 * A couple of panels gather steps from several places in their paper, and
 * printing the first and the last would claim everything in between.
 */
function describeRange(members: { id: string; number: string }[]): string {
  if (!members.length) return "";
  const numbers = members.map((node) => Number(node.number)).sort((a, b) => a - b);
  const contiguous = numbers.every((value, position) => value === numbers[0] + position);
  if (!contiguous) return `${members.length} steps`;

  const byNumber = [...members].sort((a, b) => Number(a.number) - Number(b.number));
  return `${byNumber[0].id}–${byNumber[byNumber.length - 1].id}`;
}

function PanelGrid({
  slug,
  groups,
  document,
}: {
  slug: string;
  groups: { id: string; title: string; summary: string; caption: string }[];
  document: { nodes: { id: string; group: string; number: string }[] };
}) {
  return (
    <ol className="panel-grid">
      {groups.map((group) => {
        const members = document.nodes.filter((node) => node.group === group.id);
        return (
          <li key={group.id}>
            <Link to={`/${slug}/explore?panel=${encodeURIComponent(group.id)}`}>
              <span className="panel-range">{describeRange(members)}</span>
              <h3>{group.title}</h3>
              <p>
                <Latex value={group.summary || group.caption} />
              </p>
            </Link>
          </li>
        );
      })}
    </ol>
  );
}
