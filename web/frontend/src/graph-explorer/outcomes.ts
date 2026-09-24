import { latexToPlainText } from "./latex";
import type { ProofGraphDocument, ProofNode } from "./types";

/** Open outcomes remain source-driven: the manuscript marks them in its diagram. */
export function openOutcomeNodes(document: ProofGraphDocument): ProofNode[] {
  return document.nodes
    .filter((node) => node.open)
    .sort((left, right) => left.id.localeCompare(right.id, undefined, { numeric: true }));
}

export function openOutcomeName(node: ProofNode): string {
  return latexToPlainText(node.label).replace(/^OPEN(?: aggregate)?:\s*/i, "");
}
