import { Fragment, useMemo } from "react";

import { BranchList, ItemDisclosure } from "./DetailParts";
import { Latex } from "./Latex";
import type { NodeDetailPanelProps } from "./NodeDetailPanel";
import { SHAPE_NAMES } from "./ProofFlowNode";
import { refereeDossier, type ReviewCheck } from "./referee";
import type { Invariant, ProofItem, ProofNode } from "./types";

/** How many downstream leaves to name before saying "and more". */
const TERMINAL_CAP = 12;

/**
 * The display unit for one step as a referee reads it: evidence first, prose
 * second. What is claimed, what may be assumed here, why it follows, and what
 * would fall if it did not — with each answer's standing recorded, and
 * "not recorded" said where the document is silent.
 */
export function RefereePanel({
  document,
  index,
  node,
  focusItem,
  activeInvariant,
  onSelectNode,
  onSelectItem,
  onSelectInvariant,
}: NodeDetailPanelProps) {
  const group = index.groupById.get(node.group);
  const chapter = node.chapter ? index.chapterById.get(node.chapter) : undefined;
  const incoming = index.incoming.get(node.id) ?? [];
  const dossier = useMemo(() => refereeDossier(document, index, node), [document, index, node]);
  const { state, cases, closure, evidence, impact, sources, checks } = dossier;

  const disclose = (item: ProofItem) => (
    <ItemDisclosure
      key={item.key}
      item={item}
      document={document}
      index={index}
      focus={focusItem === item.key}
      onOpen={onSelectItem}
      onSelectNode={onSelectNode}
    />
  );

  return (
    <article className="node-detail node-detail-referee" aria-label={`Node ${node.id}`}>
      <header className="node-detail-header">
        <div className="node-detail-badges">
          <span className="badge badge-number">{node.id}</span>
          <span className={`badge badge-shape badge-${node.shape}`}>{SHAPE_NAMES[node.shape]}</span>
          {chapter ? <span className="badge badge-chapter">{chapter.shortTitle}</span> : null}
          {group ? <span className="badge badge-group">{group.title}</span> : null}
        </div>
        <h2 className="node-detail-statement">
          <Latex value={node.label} />
        </h2>
        <ReviewStrip checks={checks} />
      </header>

      <section className="node-detail-section referee-claim">
        <h3>Claim</h3>
        <p>
          <Latex value={dossier.claim} />
        </p>
        {dossier.failureRoute ? (
          <p className="node-detail-note">
            <span className="node-detail-note-label">If it fails</span>
            <Latex value={dossier.failureRoute} />
          </p>
        ) : null}
      </section>

      <section className="node-detail-section referee-state">
        <h3>State at this step</h3>
        <StateRow
          title="Available before"
          invariants={state.before}
          active={activeInvariant}
          onSelect={onSelectInvariant}
        />
        <StateRow
          title="Reads"
          invariants={state.reads}
          active={activeInvariant}
          onSelect={onSelectInvariant}
          empty={state.recorded ? "none declared" : "not recorded — the source has no requirement rows"}
        />
        <StateRow
          title="Establishes"
          invariants={state.establishes}
          active={activeInvariant}
          onSelect={onSelectInvariant}
        />
        {state.unavailable.length ? (
          <p className="referee-flag" role="note">
            Declared as input here but tracked neither upstream nor at this step:{" "}
            {state.unavailable.map((invariant) => (
              <InvariantChip
                key={invariant.id}
                invariant={invariant}
                active={activeInvariant === invariant.id}
                onSelect={onSelectInvariant}
              />
            ))}
          </p>
        ) : null}
        {state.dangling.map((cited) => (
          <p className="referee-flag" role="note" key={cited.number}>
            Cites constraint {cited.number}, which the ledger does not list (
            {cited.items.map((key, position) => (
              <Fragment key={key}>
                {position ? ", " : ""}
                <code>{key}</code>
              </Fragment>
            ))}
            ).
          </p>
        ))}
      </section>

      {cases ? (
        <section className="node-detail-section referee-cases">
          <h3>
            Cases <span className="count">{cases.branches.length}</span>
          </h3>
          <table>
            <thead>
              <tr>
                <th scope="col">Condition</th>
                <th scope="col">Goes to</th>
              </tr>
            </thead>
            <tbody>
              {cases.branches.map(({ edge, target }) => (
                <tr key={edge.id}>
                  <td>
                    {edge.branch ? <Latex value={edge.branch} /> : <em>no condition drawn</em>}
                  </td>
                  <td>
                    <NodeChip id={edge.target} node={target} onSelect={onSelectNode} />
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
          <p className="node-detail-hint">
            The cases are the arrows as drawn; the source records no separate argument that
            they exhaust the test
            {cases.unlabelled
              ? `, and ${cases.unlabelled} of them ${cases.unlabelled === 1 ? "carries" : "carry"} no condition`
              : ""}
            .
          </p>
        </section>
      ) : null}

      {closure ? (
        <section className="node-detail-section node-detail-dossier referee-closure">
          <h3>Closure</h3>
          <dl>
            {(
              [
                ["Closing result", closure.dossier.closingResult],
                ["Closing condition", closure.dossier.closingCondition],
                ["Route", closure.dossier.route],
                ["Slack", closure.dossier.slack],
                ["Redundant cover", closure.dossier.redundantCover],
                ["If the result were false", closure.dossier.residualCounterexample],
              ] as const
            )
              .filter(([, value]) => value && value !== "---")
              .map(([label, value]) => (
                <Fragment key={label}>
                  <dt>{label}</dt>
                  <dd>
                    <Latex value={value as string} />
                  </dd>
                </Fragment>
              ))}
          </dl>
          {closure.closingItems.length ? (
            <div className="item-group">
              <h4>Closing results</h4>
              {closure.closingItems.map(disclose)}
            </div>
          ) : null}
        </section>
      ) : node.shape === "terminal" ? (
        <section className="node-detail-section referee-closure">
          <h3>Closure</h3>
          <p className="node-detail-hint">
            {node.open
              ? "The source draws this outcome as open: no closure is claimed for it."
              : "The closure table has no row for this leaf."}
          </p>
        </section>
      ) : null}

      <section className="node-detail-section referee-evidence">
        <h3>
          Evidence <span className="count">{evidence.items.length}</span>
        </h3>
        {evidence.items.length ? (
          <div className="item-group">{evidence.items.map(disclose)}</div>
        ) : (
          <p className="node-detail-hint">No manuscript result is attached to this step alone.</p>
        )}
        {evidence.blocks.length ? (
          <div className="referee-blocks">
            {evidence.blocks.map((block) => (
              <details className="item item-block" key={block.range}>
                <summary>
                  <span className="item-kind">{block.range}</span>
                  <span className="item-title">
                    <Latex value={block.name} />
                  </span>
                  <span className="item-stage">{block.itemRefs.length}</span>
                </summary>
                <div className="item-body">
                  {block.itemRefs
                    .map((key) => index.itemByKey.get(key))
                    .filter((item): item is ProofItem => Boolean(item))
                    .map(disclose)}
                </div>
              </details>
            ))}
          </div>
        ) : null}
        {evidence.builds.length ? (
          <p className="node-detail-note">
            <span className="node-detail-note-label">Rests on</span>
            {evidence.builds.map((item) => (
              <span className="chip chip-quiet" key={item.key}>
                {item.title ? <Latex value={item.title} /> : item.key}
              </span>
            ))}
          </p>
        ) : null}
      </section>

      <section className="node-detail-section referee-depends">
        <h3>Depends on</h3>
        <BranchList
          title="Arrives from"
          edges={incoming}
          endpoint="source"
          index={index}
          onSelectNode={onSelectNode}
        />
      </section>

      <section className="node-detail-section referee-impact">
        <h3>Impact</h3>
        <BranchList
          title="Leads to"
          edges={impact.successors}
          endpoint="target"
          index={index}
          onSelectNode={onSelectNode}
        />
        <p className="referee-impact-summary">
          {impact.downstreamCount
            ? `${impact.downstreamCount} later ${impact.downstreamCount === 1 ? "step" : "steps"}`
            : "No later step"}
          {impact.terminals.length ? (
            <>
              {" · reaches "}
              {impact.terminals.slice(0, TERMINAL_CAP).map((terminal) => (
                <NodeChip key={terminal.id} id={terminal.id} node={terminal} onSelect={onSelectNode} />
              ))}
              {impact.terminals.length > TERMINAL_CAP
                ? ` and ${impact.terminals.length - TERMINAL_CAP} more ${
                    impact.terminals.length - TERMINAL_CAP === 1 ? "leaf" : "leaves"
                  }`
                : ""}
            </>
          ) : null}
        </p>
        {impact.alsoUsedAt.length ? (
          <p className="node-detail-note">
            <span className="node-detail-note-label">Results here also used at</span>
            {impact.alsoUsedAt.map((id) => (
              <NodeChip key={id} id={id} node={index.nodeById.get(id)} onSelect={onSelectNode} />
            ))}
          </p>
        ) : null}
      </section>

      <section className="node-detail-section referee-sources">
        <h3>Source</h3>
        {sources.length ? (
          <ul>
            {sources.map(({ where, items }) => (
              <li key={`${where.title}:${where.page}`}>
                <a href={where.url} target="_blank" rel="noreferrer">
                  page {where.page} of {where.title}
                </a>
                <span className="referee-source-items">
                  {items.map((item) => (
                    <span className="chip chip-quiet" key={item.key}>
                      {item.title ? <Latex value={item.title} /> : item.key}
                    </span>
                  ))}
                </span>
              </li>
            ))}
          </ul>
        ) : (
          <p className="node-detail-hint">
            {evidence.items.length
              ? "The page maps do not place this step's results."
              : "Nothing to place: this step has no manuscript result of its own."}
          </p>
        )}
      </section>

      <footer className="node-detail-footer">
        {chapter
          ? `Node [${node.number}] of ${chapter.title}`
          : `Node ${node.id} of ${document.source.diagramNodes} in the proof-dependency diagram`}
        {node.tikzId ? `, drawn as “${node.tikzId}”` : ""}.
      </footer>
    </article>
  );
}

/** Where a step stands along each dimension of review, one mark per dimension. */
function ReviewStrip({ checks }: { checks: ReviewCheck[] }) {
  const shown = checks.filter((check) => check.state !== "na");
  return (
    <ul className="review-strip" aria-label="Review status">
      {shown.map((check) => (
        <li
          key={check.id}
          className={`review-check is-${check.state}`}
          title={check.detail || undefined}
        >
          <span className="review-mark" aria-hidden="true" />
          <span className="review-label">{check.label}</span>
          <span className="review-value">
            {check.state === "unrecorded" ? "not recorded" : check.state}
          </span>
        </li>
      ))}
    </ul>
  );
}

function StateRow({
  title,
  invariants,
  active,
  onSelect,
  empty = "none recorded",
}: {
  title: string;
  invariants: Invariant[];
  /** The constraint currently lit up on the canvas. */
  active?: string | null;
  onSelect: (id: string) => void;
  /** What to say when there is nothing to list. */
  empty?: string;
}) {
  return (
    <p className={`referee-state-row${invariants.length ? "" : " is-empty"}`}>
      <span className="branch-title">{title}</span>
      <span className="branch-items">
        {invariants.length ? (
          invariants.map((invariant) => (
            <InvariantChip
              key={invariant.id}
              invariant={invariant}
              active={active === invariant.id}
              onSelect={onSelect}
            />
          ))
        ) : (
          <span className="branch-none">{empty}</span>
        )}
      </span>
    </p>
  );
}

function InvariantChip({
  invariant,
  active = false,
  onSelect,
}: {
  invariant: Invariant;
  /** Whether this constraint is the one lit up on the canvas; pressing it again clears it. */
  active?: boolean;
  onSelect: (id: string) => void;
}) {
  return (
    <button
      type="button"
      className={`chip chip-invariant${active ? " is-active" : ""}`}
      aria-pressed={active}
      onClick={() => onSelect(invariant.id)}
      title={`Constraint ${invariant.number}: ${invariant.name} — ${
        active ? "stop highlighting the steps that track it" : "show every step that tracks it"
      }`}
    >
      {invariant.number}
      <span className="chip-invariant-name">
        <Latex value={invariant.name} />
      </span>
    </button>
  );
}

function NodeChip({
  id,
  node,
  onSelect,
}: {
  id: string;
  node?: ProofNode;
  onSelect: (id: string) => void;
}) {
  return (
    <button
      type="button"
      className="chip chip-node"
      onClick={() => onSelect(id)}
      title={node ? undefined : id}
    >
      {id}
      {node ? (
        <span className="chip-node-label">
          <Latex value={node.label} />
        </span>
      ) : null}
    </button>
  );
}
