import { Fragment } from "react";

import { BranchList, ItemDisclosure, KIND_HEADINGS, KIND_ORDER } from "./DetailParts";
import { Latex } from "./Latex";
import { SHAPE_NAMES } from "./ProofFlowNode";
import type { ProofGraphDocument, ProofIndex, ProofItem, ProofNode } from "./types";

export interface NodeDetailPanelProps {
  document: ProofGraphDocument;
  index: ProofIndex;
  node: ProofNode;
  /** Key of a result to scroll to and open, e.g. after clicking a reference. */
  focusItem?: string | null;
  onSelectNode: (id: string) => void;
  /** Called when a result is opened, so the view stays linkable. */
  onSelectItem: (key: string) => void;
  /** The constraint currently lit up on the canvas, if any. */
  activeInvariant?: string | null;
  /** Called when a constraint chip is pressed; pressing the active one clears it. */
  onSelectInvariant: (id: string) => void;
}

/**
 * The display unit for one node: what it says, what it does, where it goes, and
 * every result, object and invariant behind it.
 */
export function NodeDetailPanel({
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
  const outgoing = index.outgoing.get(node.id) ?? [];

  const items = node.itemRefs
    .map((key) => index.itemByKey.get(key))
    .filter((item): item is ProofItem => Boolean(item));

  const grouped = KIND_ORDER.map((kind) => ({
    kind,
    items: items.filter((item) => item.kind === kind),
  })).filter((bucket) => bucket.items.length > 0);

  const constants = node.constantRefs
    .map((symbol) => index.constantBySymbol.get(symbol))
    .filter((constant): constant is NonNullable<typeof constant> => Boolean(constant));

  const invariants = node.invariantRefs
    .map((id) => index.invariantById.get(id))
    .filter((invariant): invariant is NonNullable<typeof invariant> => Boolean(invariant));

  return (
    <article className="node-detail" aria-label={`Node ${node.id}`}>
      <header className="node-detail-header">
        <div className="node-detail-badges">
          <span className="badge badge-number">{node.id}</span>
          <span className={`badge badge-shape badge-${node.shape}`}>
            {SHAPE_NAMES[node.shape]}
          </span>
          {chapter ? (
            <span className="badge badge-chapter">{chapter.shortTitle}</span>
          ) : null}
          {group ? <span className="badge badge-group">{group.title}</span> : null}
        </div>
        <h2 className="node-detail-statement">
          <Latex value={node.label} />
        </h2>
        {node.topics.length ? (
          <p className="node-detail-topics">
            {node.topics.map((topic) => (
              <span className="chip chip-quiet" key={topic}>
                <Latex value={topic} />
              </span>
            ))}
          </p>
        ) : null}
      </header>

      <section className="node-detail-section">
        <h3>What this step does</h3>
        <p>
          <Latex value={node.overview} />
        </p>
        {node.failureRoute && node.failureRoute !== "---" ? (
          <p className="node-detail-note">
            <span className="node-detail-note-label">If it fails</span>
            <Latex value={node.failureRoute} />
          </p>
        ) : null}
        {node.aliases.length ? (
          <p className="node-detail-note">
            <span className="node-detail-note-label">Also drawn as</span>
            {node.aliases.map((id) => (
              <button
                key={id}
                type="button"
                className="chip chip-node"
                onClick={() => onSelectNode(id)}
              >
                {id}
              </button>
            ))}
          </p>
        ) : null}
      </section>

      <section className="node-detail-section">
        <h3>Branches</h3>
        <BranchList
          title="Arrives from"
          edges={incoming}
          endpoint="source"
          index={index}
          onSelectNode={onSelectNode}
        />
        <BranchList
          title="Leads to"
          edges={outgoing}
          endpoint="target"
          index={index}
          onSelectNode={onSelectNode}
        />
      </section>

      {node.dossier ? (
        <section className="node-detail-section node-detail-dossier">
          <h3>How this leaf closes</h3>
          <dl>
            {(
              [
                ["Closing result", node.dossier.closingResult],
                ["Closing condition", node.dossier.closingCondition],
                ["Route", node.dossier.route],
                ["Slack", node.dossier.slack],
                ["Redundant cover", node.dossier.redundantCover],
                ["If the result were false", node.dossier.residualCounterexample],
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
        </section>
      ) : null}

      {grouped.length ? (
        <section className="node-detail-section">
          <h3>
            Results behind this step <span className="count">{items.length}</span>
          </h3>
          <p className="node-detail-hint">
            Expand any entry for its statement as the paper writes it, together with
            what it does and the part it plays.
          </p>
          {grouped.map((bucket) => (
            <div className="item-group" key={bucket.kind}>
              <h4>{KIND_HEADINGS[bucket.kind]}</h4>
              {bucket.items.map((item) => (
                <ItemDisclosure
                  key={item.key}
                  item={item}
                  document={document}
                  index={index}
                  focus={focusItem === item.key}
                  onOpen={onSelectItem}
                  onSelectNode={onSelectNode}
                />
              ))}
            </div>
          ))}
        </section>
      ) : null}

      {node.blocks.length ? (
        <section className="node-detail-section">
          <h3>Used across this stretch of the argument</h3>
          <p className="node-detail-hint">
            The paper attributes these to a run of steps rather than to this one
            alone.
          </p>
          {node.blocks.map((block) => (
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
                  .map((item) => (
                    <ItemDisclosure
                      key={item.key}
                      item={item}
                      document={document}
                      index={index}
                      focus={focusItem === item.key}
                      onOpen={onSelectItem}
                      onSelectNode={onSelectNode}
                    />
                  ))}
              </div>
            </details>
          ))}
        </section>
      ) : null}

      {constants.length ? (
        <section className="node-detail-section">
          <h3>Objects and constants</h3>
          <dl className="constant-list">
            {constants.map((constant) => (
              <div key={constant.symbol}>
                <dt>
                  <Latex value={constant.symbol} />
                </dt>
                <dd>
                  <strong>
                    <Latex value={constant.value} />
                  </strong>
                  <span>
                    <Latex value={constant.meaning} />
                  </span>
                </dd>
              </div>
            ))}
          </dl>
        </section>
      ) : null}

      {invariants.length ? (
        <section className="node-detail-section">
          <h3>Standing constraints tracked here</h3>
          <ul className="invariant-list">
            {invariants.map((invariant) => (
              <li key={invariant.id}>
                <button
                  type="button"
                  className={`chip chip-invariant${activeInvariant === invariant.id ? " is-active" : ""}`}
                  aria-pressed={activeInvariant === invariant.id}
                  onClick={() => onSelectInvariant(invariant.id)}
                  title={
                    activeInvariant === invariant.id
                      ? "Stop highlighting the steps that track this constraint"
                      : "Show every step that tracks this constraint"
                  }
                >
                  {invariant.number}
                </button>
                <div>
                  <strong>
                    <Latex value={invariant.name} />
                  </strong>
                  <p>
                    <Latex value={invariant.constraint} />
                  </p>
                </div>
              </li>
            ))}
          </ul>
        </section>
      ) : null}

      <footer className="node-detail-footer">
        {chapter
          ? `Node [${node.number}] of ${chapter.title}`
          : `Node ${node.id} of ${document.source.diagramNodes} in the proof-dependency diagram`}
        {node.tikzId ? `, drawn as “${node.tikzId}”` : ""}.
      </footer>
    </article>
  );
}
