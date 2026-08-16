import type { ProofEdge, TraceDirection } from "./types";

export interface Trace {
  nodeIds: Set<string>;
  edgeIds: Set<string>;
}

const EMPTY: Trace = { nodeIds: new Set(), edgeIds: new Set() };

/**
 * Everything reachable from `startId` along the given direction.
 *
 * `upstream` walks the arrows backwards (what had to hold before this step),
 * `downstream` walks them forwards (where this step sends you), `both` does
 * each in turn.
 */
export function traceFrom(
  edges: ProofEdge[],
  startId: string | null,
  direction: TraceDirection,
): Trace {
  if (!startId || direction === "none") return EMPTY;

  const outgoing = new Map<string, ProofEdge[]>();
  const incoming = new Map<string, ProofEdge[]>();
  for (const edge of edges) {
    const from = outgoing.get(edge.source);
    if (from) from.push(edge);
    else outgoing.set(edge.source, [edge]);

    const to = incoming.get(edge.target);
    if (to) to.push(edge);
    else incoming.set(edge.target, [edge]);
  }

  const nodeIds = new Set<string>([startId]);
  const edgeIds = new Set<string>();

  const walk = (
    index: Map<string, ProofEdge[]>,
    next: (edge: ProofEdge) => string,
  ): void => {
    // Each direction keeps its own record of where it has been. Sharing one
    // would let a step found downstream stop the upstream walk from ever
    // reaching that step's own antecedents, which a diagram with a loop in it
    // — a branch that recomputes and re-enters — really does ask for.
    const seen = new Set<string>([startId]);
    const queue: string[] = [startId];
    for (let cursor = 0; cursor < queue.length; cursor += 1) {
      for (const edge of index.get(queue[cursor]) ?? []) {
        edgeIds.add(edge.id);
        const adjacent = next(edge);
        nodeIds.add(adjacent);
        if (!seen.has(adjacent)) {
          seen.add(adjacent);
          queue.push(adjacent);
        }
      }
    }
  };

  if (direction === "downstream" || direction === "both") {
    walk(outgoing, (edge) => edge.target);
  }
  if (direction === "upstream" || direction === "both") {
    walk(incoming, (edge) => edge.source);
  }

  return { nodeIds, edgeIds };
}
