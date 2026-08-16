import type { Reference } from "./Latex";
import type { ProofGraphDocument, ProofIndex } from "./types";

/**
 * How a cross-reference written inside a statement or a proof is resolved.
 *
 * A paper cites the label it writes itself, while keys are namespaced per
 * manuscript so that three of them can reuse a name. So a bare label is looked
 * for in the reader's current manuscript first, then anywhere.
 */
export function createReferenceResolver(
  document: ProofGraphDocument,
  index: ProofIndex,
  currentChapter?: string,
) {
  function lookup<T>(table: Map<string, T>, key: string): T | undefined {
    const direct = table.get(key);
    if (direct) return direct;

    if (currentChapter) {
      const here = table.get(`${currentChapter}/${key}`);
      if (here) return here;
    }
    for (const chapter of document.chapters ?? []) {
      const scoped = table.get(`${chapter.id}/${key}`);
      if (scoped) return scoped;
    }
    return undefined;
  }

  function resolve(key: string): Reference {
    const item = lookup(index.itemByKey, key);
    if (item) {
      // A result some step claims can be opened there; one no step claims — an
      // auxiliary the papers only cite in passing — unfolds where it is.
      const holders = index.nodesByItem.get(item.key);
      return holders?.length
        ? { label: item.title || item.key, actionable: true }
        : {
            label: item.title || item.key.replace(/^.*?\//, ""),
            actionable: false,
            preview: item.statementLatex,
          };
    }

    const equation = lookup(index.equationByKey, key);
    if (equation) {
      // The number is this site's own, counted over the displays the paper
      // labels; the key and line say exactly which display it is.
      return {
        label: `(${equation.number})`,
        actionable: false,
        preview: equation.latex,
        note: `${equation.key.replace(/^.*?\//, "")} · line ${equation.sourceLine}`,
      };
    }

    const group = index.groupById.get(key);
    if (group) return { label: group.title, actionable: true };

    // Sections, tables and appendices of the paper have no page of their own.
    return { label: key.replace(/^.*?[a-z]+:/, "").replace(/-/g, " "), actionable: false };
  }

  /** The namespaced key a reference names, when it names something. */
  function target(key: string): { item?: string; group?: string } {
    if (index.groupById.has(key)) return { group: key };
    const item = lookup(index.itemByKey, key);
    return item ? { item: item.key } : {};
  }

  return { resolve, target };
}
