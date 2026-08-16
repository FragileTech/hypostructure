import type { ProofGraphDocument, ProofIndex, ProofNode } from "./types";

/**
 * Everything about a node a reader might type into the search box: its own
 * text, the names the source gives it, and the titles and statements of the
 * results behind it.
 */
export function nodeSearchText(index: ProofIndex, node: ProofNode): string {
  const parts: string[] = [
    node.id,
    node.label,
    node.overview,
    node.shape,
    node.tikzId ?? "",
    ...node.topics,
    ...node.constantRefs,
    ...node.invariantRefs.map((id) => `constraint ${id.split(":").pop()}`),
  ];

  for (const key of node.itemRefs) {
    const item = index.itemByKey.get(key);
    if (!item) continue;
    parts.push(key, item.title, item.kind, item.plain ?? "", item.role ?? "");
  }

  const group = index.groupById.get(node.group);
  if (group) parts.push(group.title);

  const chapter = node.chapter ? index.chapterById.get(node.chapter) : undefined;
  if (chapter) parts.push(chapter.title, chapter.shortTitle);

  return parts.join(" ").toLowerCase();
}

/** Pre-compute the search text for every node in a document. */
export function buildSearchIndex(
  document: ProofGraphDocument,
  index: ProofIndex,
): Map<string, string> {
  return new Map(
    document.nodes.map((node) => [node.id, nodeSearchText(index, node)]),
  );
}

/**
 * Node ids matching a query. Every whitespace-separated term must appear, so
 * `type a exit` narrows rather than widens. An empty query matches nothing,
 * which callers read as "no filter active".
 */
export function matchNodes(
  searchIndex: Map<string, string>,
  query: string,
): Set<string> {
  const terms = query.trim().toLowerCase().split(/\s+/).filter(Boolean);
  if (!terms.length) return new Set();

  const matched = new Set<string>();
  for (const [id, text] of searchIndex) {
    if (terms.every((term) => text.includes(term))) matched.add(id);
  }
  return matched;
}
