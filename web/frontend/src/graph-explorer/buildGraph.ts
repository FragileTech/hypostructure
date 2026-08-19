import type { Edge, Node } from "@xyflow/react";

import { layoutGraph, type LayoutBox, type LayoutOptions } from "./layout";
import { latexToPlainText } from "./latex";
import type { ProofEdge, ProofGraphDocument, ProofNode } from "./types";

export interface FlowNodeData extends Record<string, unknown> {
  node: ProofNode;
  /** The box this node occupies, as laid out. */
  width: number;
  height: number;
  /** Reader-facing text, with maths flattened for measuring and for a11y. */
  plain: string;
  selected: boolean;
  traced: boolean;
  dimmed: boolean;
  matched: boolean;
  verified: boolean;
}

export type ProofFlowNode = Node<FlowNodeData, "proof">;

export interface BuildOptions {
  /** Restrict the canvas to one manuscript of a multi-part proof. */
  chapter?: string | null;
  /** Restrict the canvas to one panel of the diagram. */
  group?: string | null;
  selectedId?: string | null;
  tracedNodeIds?: Set<string>;
  tracedEdgeIds?: Set<string>;
  /** Ids matching the current search; others are dimmed. */
  matchedIds?: Set<string> | null;
  layout?: LayoutOptions;
}

const WIDTH = 236;

/**
 * Room for the text once it is set as mathematics, which runs taller than the
 * plain string it is measured from. Branch tests are drawn as hexagons, so their
 * text has less width to work with and needs more vertical clearance.
 */
function heightFor(plain: string, shape: ProofNode["shape"]): number {
  const perLine = shape === "decision" ? 26 : 32;
  const lines = Math.max(1, Math.ceil(plain.length / perLine));
  const base = shape === "decision" ? 76 : 62;
  return Math.min(210, base + lines * 17);
}

/** Turn a document into the nodes and edges React Flow renders. */
export function buildGraph(
  document: ProofGraphDocument,
  options: BuildOptions = {},
): { nodes: ProofFlowNode[]; edges: Edge[] } {
  const {
    chapter = null,
    group = null,
    selectedId = null,
    tracedNodeIds,
    tracedEdgeIds,
    matchedIds = null,
    layout,
  } = options;

  const visible = document.nodes.filter(
    (node) =>
      (!chapter || node.chapter === chapter) && (!group || node.group === group),
  );
  const visibleIds = new Set(visible.map((node) => node.id));

  const visibleEdges = document.edges.filter(
    (edge) => visibleIds.has(edge.source) && visibleIds.has(edge.target),
  );

  const plainById = new Map(
    visible.map((node) => [node.id, latexToPlainText(node.label)] as const),
  );

  const boxes = visible.map((node) => ({
    id: node.id,
    width: WIDTH,
    height: heightFor(plainById.get(node.id) ?? "", node.shape),
  }));

  const positions = layoutByChapter(visible, boxes, visibleEdges, layout);

  const reviewNodes = document.review?.nodes;
  const hasTrace = Boolean(tracedNodeIds && tracedNodeIds.size);
  const hasSearch = Boolean(matchedIds && matchedIds.size);

  const sizeById = new Map(boxes.map((box) => [box.id, box] as const));

  const nodes: ProofFlowNode[] = visible.map((node) => {
    const traced = hasTrace && tracedNodeIds!.has(node.id);
    const matched = hasSearch ? matchedIds!.has(node.id) : false;
    const box = sizeById.get(node.id)!;
    return {
      id: node.id,
      type: "proof",
      position: positions.get(node.id) ?? { x: 0, y: 0 },
      // Declared so the canvas can frame a step before it has measured the DOM.
      width: box.width,
      height: box.height,
      selected: node.id === selectedId,
      data: {
        node,
        width: box.width,
        height: box.height,
        plain: plainById.get(node.id) ?? "",
        selected: node.id === selectedId,
        traced,
        matched,
        // The selected step is never dimmed: a filter that hid the step you
        // just clicked would make every click look like it did nothing.
        dimmed:
          node.id !== selectedId && ((hasTrace && !traced) || (hasSearch && !matched)),
        // Green only when the step's own producer is finished *and* it
        // publishes the manuscript's statement. "Compiles" alone is not a
        // verification claim: a row stating something weaker than its
        // manuscript label still composes and still closes.
        verified:
          reviewNodes?.[node.id]?.kernel === "verified" &&
          reviewNodes?.[node.id]?.fidelity === "verified",
      },
    };
  });

  const edges: Edge[] = visibleEdges.map((edge) => toFlowEdge(edge, tracedEdgeIds));

  return { nodes, edges };
}

/** Horizontal gap between one manuscript's block of steps and the next. */
const CHAPTER_GUTTER = 420;

/**
 * Rank each manuscript on its own, then set the blocks side by side.
 *
 * Laying several papers out together lets the few arrows between them drag the
 * ranking about, pulling steps that sit next to each other in the argument
 * thousands of pixels apart. Ranking each paper alone keeps it readable, and the
 * arrows between papers simply span the gutter.
 */
function layoutByChapter(
  nodes: ProofNode[],
  boxes: LayoutBox[],
  edges: ProofEdge[],
  options: LayoutOptions | undefined,
): Map<string, { x: number; y: number }> {
  const chapters = [...new Set(nodes.map((node) => node.chapter ?? ""))];
  if (chapters.length < 2) return layoutGraph(boxes, edges, options);

  const chapterOf = new Map(nodes.map((node) => [node.id, node.chapter ?? ""] as const));
  const boxById = new Map(boxes.map((box) => [box.id, box] as const));

  const positions = new Map<string, { x: number; y: number }>();
  let offset = 0;

  for (const chapter of chapters) {
    const members = boxes.filter((box) => chapterOf.get(box.id) === chapter);
    const within = edges.filter(
      (edge) =>
        chapterOf.get(edge.source) === chapter && chapterOf.get(edge.target) === chapter,
    );

    const placed = layoutGraph(members, within, options);
    let right = 0;
    for (const [id, point] of placed) {
      positions.set(id, { x: point.x + offset, y: point.y });
      right = Math.max(right, point.x + (boxById.get(id)?.width ?? 0));
    }
    offset += right + CHAPTER_GUTTER;
  }

  return positions;
}

function toFlowEdge(edge: ProofEdge, tracedEdgeIds?: Set<string>): Edge {
  const traced = Boolean(tracedEdgeIds?.has(edge.id));
  const branch = edge.branch ?? "";
  // Continuation notes are sentences; only short branch conditions fit on an arrow.
  const label = edge.kind === "continuation" ? "continues" : branch;
  return {
    id: edge.id,
    source: edge.source,
    target: edge.target,
    type: "smoothstep",
    label: label || undefined,
    animated: traced,
    className: [
      "proof-edge",
      `proof-edge-${edge.kind}`,
      branch ? `proof-edge-branch-${branch.replace(/\W+/g, "-").toLowerCase()}` : "",
      traced ? "is-traced" : "",
      tracedEdgeIds && tracedEdgeIds.size && !traced ? "is-dimmed" : "",
    ]
      .filter(Boolean)
      .join(" "),
    data: { branch: edge.branch, kind: edge.kind },
  };
}

/** The rectangle covering the given nodes, in canvas coordinates. */
export function boundsOf(
  nodes: ProofFlowNode[],
  ids: Set<string>,
): { x: number; y: number; width: number; height: number } | null {
  let left = Infinity;
  let top = Infinity;
  let right = -Infinity;
  let bottom = -Infinity;

  for (const node of nodes) {
    if (!ids.has(node.id)) continue;
    left = Math.min(left, node.position.x);
    top = Math.min(top, node.position.y);
    right = Math.max(right, node.position.x + node.data.width);
    bottom = Math.max(bottom, node.position.y + node.data.height);
  }

  if (left === Infinity) return null;
  return { x: left, y: top, width: right - left, height: bottom - top };
}
