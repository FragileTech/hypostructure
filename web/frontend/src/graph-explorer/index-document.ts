import type { ProofEdge, ProofGraphDocument, ProofIndex } from "./types";

function push<K, V>(map: Map<K, V[]>, key: K, value: V): void {
  const bucket = map.get(key);
  if (bucket) bucket.push(value);
  else map.set(key, [value]);
}

/** Build the lookup tables the explorer uses while browsing a document. */
export function indexDocument(document: ProofGraphDocument): ProofIndex {
  const incoming = new Map<string, ProofEdge[]>();
  const outgoing = new Map<string, ProofEdge[]>();
  const nodesByInvariant = new Map<string, string[]>();
  const nodesByItem = new Map<string, string[]>();

  for (const edge of document.edges) {
    push(outgoing, edge.source, edge);
    push(incoming, edge.target, edge);
  }

  for (const node of document.nodes) {
    for (const id of node.invariantRefs) push(nodesByInvariant, id, node.id);
    for (const key of node.itemRefs) push(nodesByItem, key, node.id);
  }

  return {
    nodeById: new Map(document.nodes.map((node) => [node.id, node])),
    itemByKey: new Map(document.items.map((item) => [item.key, item])),
    equationByKey: new Map(
      (document.equations ?? []).map((equation) => [equation.key, equation]),
    ),
    groupById: new Map(document.groups.map((group) => [group.id, group])),
    chapterById: new Map((document.chapters ?? []).map((chapter) => [chapter.id, chapter])),
    invariantById: new Map(
      document.invariants.map((invariant) => [invariant.id, invariant]),
    ),
    constantBySymbol: new Map(
      document.constants.map((constant) => [constant.symbol, constant]),
    ),
    incoming,
    outgoing,
    nodesByInvariant,
    nodesByItem,
  };
}
