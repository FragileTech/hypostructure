import { useEffect, useRef } from "react";

import { Latex } from "./Latex";
import { locate } from "./locate";
import type { ItemKind, ProofEdge, ProofGraphDocument, ProofIndex, ProofItem } from "./types";

/**
 * The pieces both readings of a step share: how a result is disclosed, how the
 * arrows in and out are listed, and the order the kinds of result come in.
 */

export const KIND_ORDER: ItemKind[] = [
  "theorem",
  "proposition",
  "lemma",
  "corollary",
  "definition",
  "remark",
];

export const KIND_HEADINGS: Record<ItemKind, string> = {
  theorem: "Theorems",
  proposition: "Propositions",
  lemma: "Lemmas",
  corollary: "Corollaries",
  definition: "Definitions",
  remark: "Remarks",
};

export const KIND_LABELS: Record<ItemKind, string> = {
  theorem: "Theorem",
  proposition: "Proposition",
  lemma: "Lemma",
  corollary: "Corollary",
  definition: "Definition",
  remark: "Remark",
};

export function BranchList({
  title,
  edges,
  endpoint,
  index,
  onSelectNode,
}: {
  title: string;
  edges: ProofEdge[];
  endpoint: "source" | "target";
  index: ProofIndex;
  onSelectNode: (id: string) => void;
}) {
  if (!edges.length) {
    return (
      <p className="branch-row is-empty">
        <span className="branch-title">{title}</span>
        <span className="branch-none">
          {endpoint === "source" ? "nothing — the argument starts here" : "nothing — the branch ends here"}
        </span>
      </p>
    );
  }

  return (
    <p className="branch-row">
      <span className="branch-title">{title}</span>
      <span className="branch-items">
        {edges.map((edge) => {
          const otherId = edge[endpoint];
          const other = index.nodeById.get(otherId);
          return (
            <button
              key={edge.id}
              type="button"
              className={`branch-chip branch-${edge.kind}`}
              onClick={() => onSelectNode(otherId)}
              title={other ? undefined : otherId}
            >
              <span className="branch-chip-number">{otherId}</span>
              {edge.branch ? (
                <span className="branch-chip-condition">
                  <Latex value={edge.branch} />
                </span>
              ) : null}
              {other ? (
                <span className="branch-chip-label">
                  <Latex value={other.label} />
                </span>
              ) : null}
            </button>
          );
        })}
      </span>
    </p>
  );
}

/**
 * One result, collapsed to its name until asked for.
 *
 * The disclosure keeps its own open state so several can be read side by side;
 * `focus` only forces this one open, which is what a cross-reference does.
 */
export function ItemDisclosure({
  item,
  document,
  index,
  focus,
  onOpen,
  onSelectNode,
}: {
  item: ProofItem;
  document: ProofGraphDocument;
  index: ProofIndex;
  focus: boolean;
  onOpen: (key: string) => void;
  onSelectNode: (id: string) => void;
}) {
  const element = useRef<HTMLDetailsElement>(null);

  useEffect(() => {
    if (!focus || !element.current) return;
    element.current.open = true;
    element.current.scrollIntoView({ block: "nearest", behavior: "smooth" });
  }, [focus]);

  const appearsAt = index.nodesByItem.get(item.key) ?? [];
  const where = locate(document, item.chapter, item.key);
  const requires = (item.requiresItems ?? [])
    .map((key) => index.itemByKey.get(key))
    .filter((required): required is ProofItem => Boolean(required));

  return (
    <details
      ref={element}
      className="item"
      onToggle={(event) => {
        if ((event.currentTarget as HTMLDetailsElement).open) onOpen(item.key);
      }}
    >
      <summary>
        <span className="item-kind">{KIND_LABELS[item.kind]}</span>
        <span className="item-title">
          {item.title ? <Latex value={item.title} /> : <code>{item.key}</code>}
        </span>
        {item.stage ? <span className="item-stage">{item.stage}</span> : null}
      </summary>

      <div className="item-body">
        <blockquote className="item-statement">
          <Latex value={item.statementLatex} />
        </blockquote>

        {item.proofLatex ? (
          <details className="item-proof">
            <summary>Proof</summary>
            <div>
              <Latex value={item.proofLatex} />
            </div>
          </details>
        ) : null}

        {item.plain ? (
          <div className="item-note">
            <h5>What it does</h5>
            <p>
              <Latex value={item.plain} />
            </p>
          </div>
        ) : null}

        {item.role ? (
          <div className="item-note">
            <h5>Its role in the argument</h5>
            <p>
              <Latex value={item.role} />
            </p>
          </div>
        ) : null}

        {requires.length ? (
          <div className="item-note">
            <h5>Builds on</h5>
            <p className="item-chips">
              {requires.map((required) => (
                <span className="chip chip-quiet" key={required.key}>
                  {required.title || required.key}
                </span>
              ))}
            </p>
          </div>
        ) : null}

        {appearsAt.length > 1 ? (
          <div className="item-note">
            <h5>Also used at</h5>
            <p className="item-chips">
              {appearsAt.map((id) => (
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
          </div>
        ) : null}

        <p className="item-source">
          {item.key} ·{" "}
          {where ? (
            <>
              stated on{" "}
              <a href={where.url} target="_blank" rel="noreferrer">
                page {where.page} of {where.title}
              </a>{" "}
              <span className="item-source-line">(line {item.sourceLine} of the source)</span>
            </>
          ) : (
            <>stated on line {item.sourceLine} of the paper</>
          )}
        </p>
      </div>
    </details>
  );
}
