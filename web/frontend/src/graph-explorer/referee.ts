import { KIND_ORDER } from "./DetailParts";
import { locate, type SourceLocation } from "./locate";
import { traceFrom } from "./trace";
import type {
  Invariant,
  NodeReview,
  ProofBlock,
  ProofEdge,
  ProofGraphDocument,
  ProofIndex,
  ProofItem,
  ProofNode,
  TerminalDossier,
} from "./types";

/**
 * A step read the way a referee reads it: what it claims, what it may assume,
 * what stands behind it, and what falls if it does. Everything here is derived
 * from the document; nothing is a judgement of the explorer's own.
 */

/** One answer along one dimension of review, and where it came from. */
export interface ReviewCheck {
  id: string;
  label: string;
  /** `unrecorded` means the document carries no answer, not that the answer is no. */
  state: "yes" | "partial" | "no" | "unrecorded" | "na";
  detail: string;
}

/**
 * The standing constraints around a step: what it may assume and what it adds.
 *
 * `reads` are the inputs the manuscript's own requirement rows declare for the
 * step's results (`inv 4, 8, 25`). The ledger's "Used by" column is not read
 * as an input: the paper defines it as the results that introduce *or* consume
 * a constraint, and it names the result that establishes one as readily as
 * one that relies on it.
 */
export interface RefereeState {
  /** Whether the document has requirement rows at all; without them `reads` says nothing. */
  recorded: boolean;
  /** First tracked at some step strictly upstream of this one. */
  before: Invariant[];
  /** Named as inputs of this step's own results by their requirement rows. */
  reads: Invariant[];
  /** First tracked at this step. */
  establishes: Invariant[];
  /**
   * Read here yet tracked neither upstream nor here — worth a referee's eye.
   * Only constraints the ledger places at some node can be missing from a
   * branch; one it places nowhere is not claimed available anywhere.
   */
  unavailable: Invariant[];
  /** Constraint numbers a requirement row cites that the ledger does not list. */
  dangling: DanglingCitation[];
}

export interface DanglingCitation {
  number: number;
  /** The results whose requirement rows cite it. */
  items: string[];
}

export interface RefereeCase {
  edge: ProofEdge;
  target?: ProofNode;
}

export interface RefereeCases {
  branches: RefereeCase[];
  /** Arrows the diagram leaves without a condition. */
  unlabelled: number;
}

export interface RefereeClosure {
  dossier: TerminalDossier;
  closingItems: ProofItem[];
}

export interface RefereeEvidence {
  /** The step's own results, in the order the kinds of result come in. */
  items: ProofItem[];
  blocks: ProofBlock[];
  /** Results the step's own results are stated to build on. */
  builds: ProofItem[];
}

export interface RefereeImpact {
  successors: ProofEdge[];
  /** Steps reachable downstream, this one excluded. */
  downstreamCount: number;
  /** Leaves reachable downstream. */
  terminals: ProofNode[];
  /** Other steps that use one of this step's own results. */
  alsoUsedAt: string[];
}

export interface RefereeSource {
  where: SourceLocation;
  items: ProofItem[];
}

export interface RefereeDossier {
  /** The claim as the source's own dependency table states it. */
  claim: string;
  failureRoute?: string;
  state: RefereeState;
  cases?: RefereeCases;
  closure?: RefereeClosure;
  evidence: RefereeEvidence;
  impact: RefereeImpact;
  sources: RefereeSource[];
  checks: ReviewCheck[];
}

/** Numbers of the invariants a result's `requires` names, e.g. `inv 4, 8, 25`. */
export function requiredInvariantNumbers(requires: string | undefined): number[] {
  if (!requires) return [];
  const numbers = new Set<number>();
  for (const match of requires.matchAll(/\binv(?:ariants?)?\.?\s+([\d,\s–-]+)/gi)) {
    for (const part of match[1].split(",")) {
      const range = part.trim().match(/^(\d+)\s*[–-]+\s*(\d+)$/);
      if (range) {
        for (let n = Number(range[1]); n <= Number(range[2]); n += 1) numbers.add(n);
      } else if (/^\d+$/.test(part.trim())) {
        numbers.add(Number(part.trim()));
      }
    }
  }
  return [...numbers];
}

function byNumber(a: Invariant, b: Invariant): number {
  return (a.chapter ?? "").localeCompare(b.chapter ?? "") || a.number - b.number;
}

function resolveItems(index: ProofIndex, keys: string[]): ProofItem[] {
  return keys
    .map((key) => index.itemByKey.get(key))
    .filter((item): item is ProofItem => Boolean(item));
}

function deriveState(document: ProofGraphDocument, index: ProofIndex, node: ProofNode): RefereeState {
  const upstream = traceFrom(document.edges, node.id, "upstream").nodeIds;
  const before = new Map<string, Invariant>();
  for (const id of upstream) {
    if (id === node.id) continue;
    for (const ref of index.nodeById.get(id)?.invariantRefs ?? []) {
      const invariant = index.invariantById.get(ref);
      if (invariant) before.set(invariant.id, invariant);
    }
  }

  const establishes = node.invariantRefs
    .map((ref) => index.invariantById.get(ref))
    .filter((invariant): invariant is Invariant => Boolean(invariant));

  const reads = new Map<string, Invariant>();
  const dangling = new Map<number, DanglingCitation>();
  const ledgerRows = new Map<number, Invariant[]>();
  for (const invariant of document.invariants) {
    const same = ledgerRows.get(invariant.number);
    if (same) same.push(invariant);
    else ledgerRows.set(invariant.number, [invariant]);
  }
  // Every manuscript numbers its own ledger from one, so a number is read in
  // the chapter of the result that cites it; a ledger without chapters is
  // shared by all.
  const ledgerRow = (item: ProofItem, number: number): Invariant | undefined => {
    const candidates = ledgerRows.get(number) ?? [];
    const chapter = item.chapter ?? node.chapter;
    return (
      candidates.find((invariant) => invariant.chapter === chapter) ??
      candidates.find((invariant) => !invariant.chapter)
    );
  };
  for (const item of resolveItems(index, node.itemRefs)) {
    for (const number of requiredInvariantNumbers(item.requires)) {
      const invariant = ledgerRow(item, number);
      if (invariant) {
        reads.set(invariant.id, invariant);
        continue;
      }
      const cited = dangling.get(number);
      if (cited) cited.items.push(item.key);
      else dangling.set(number, { number, items: [item.key] });
    }
  }

  const available = new Set([...before.keys(), ...establishes.map((invariant) => invariant.id)]);
  return {
    recorded: document.items.some((item) => item.requires),
    before: [...before.values()].sort(byNumber),
    reads: [...reads.values()].sort(byNumber),
    establishes: [...establishes].sort(byNumber),
    unavailable: [...reads.values()]
      .filter((invariant) => invariant.nodes.length && !available.has(invariant.id))
      .sort(byNumber),
    dangling: [...dangling.values()].sort((a, b) => a.number - b.number),
  };
}

function reviewCheck(id: string, label: string, review: NodeReview | undefined): ReviewCheck {
  const state = review?.[id as keyof Omit<NodeReview, "note">];
  if (!state) return { id, label, state: "unrecorded", detail: `${label}: not recorded` };
  return {
    id,
    label,
    state: state === "verified" ? "yes" : state === "partial" ? "partial" : "no",
    detail: `${label}: ${state}${review?.note ? ` — ${review.note}` : ""}`,
  };
}

/** Everything a referee wants to see about one step, derived from the document. */
export function refereeDossier(
  document: ProofGraphDocument,
  index: ProofIndex,
  node: ProofNode,
): RefereeDossier {
  const outgoing = index.outgoing.get(node.id) ?? [];
  const items = resolveItems(index, node.itemRefs).sort(
    (a, b) => KIND_ORDER.indexOf(a.kind) - KIND_ORDER.indexOf(b.kind),
  );
  const builds = resolveItems(
    index,
    [...new Set(items.flatMap((item) => item.requiresItems ?? []))].filter(
      (key) => !node.itemRefs.includes(key),
    ),
  );

  const downstream = traceFrom(document.edges, node.id, "downstream").nodeIds;
  const terminals: ProofNode[] = [];
  for (const id of downstream) {
    const other = index.nodeById.get(id);
    if (other && other.shape === "terminal" && id !== node.id) terminals.push(other);
  }
  const alsoUsedAt = [
    ...new Set(items.flatMap((item) => index.nodesByItem.get(item.key) ?? [])),
  ].filter((id) => id !== node.id);

  const sources = new Map<string, RefereeSource>();
  let located = 0;
  for (const item of items) {
    const where = locate(document, item.chapter ?? node.chapter, item.key);
    if (!where) continue;
    located += 1;
    const key = `${where.title}:${where.page}`;
    const source = sources.get(key);
    if (source) source.items.push(item);
    else sources.set(key, { where, items: [item] });
  }

  const cases: RefereeCases | undefined =
    node.shape === "decision"
      ? {
          branches: outgoing.map((edge) => ({ edge, target: index.nodeById.get(edge.target) })),
          unlabelled: outgoing.filter((edge) => !edge.branch).length,
        }
      : undefined;

  const closure: RefereeClosure | undefined = node.dossier
    ? { dossier: node.dossier, closingItems: resolveItems(index, node.dossier.closingItems) }
    : undefined;

  const stated = items.filter((item) => item.statementLatex.trim()).length;
  const mapped = items.filter((item) => item.requiresItems?.length || item.requires).length;
  const documentMapsDependencies = document.items.some((item) => item.requires || item.requiresItems?.length);
  const review = document.review?.nodes[node.id];

  const checks: ReviewCheck[] = [
    {
      id: "manuscript",
      label: "Manuscript",
      state: items.length ? (stated === items.length ? "yes" : "partial") : node.blocks.length ? "partial" : "no",
      detail: items.length
        ? `${stated} of ${items.length} results stated in the manuscript`
        : node.blocks.length
          ? "No result of its own; the block it sits in carries the results"
          : "No manuscript result attached to this step",
    },
    {
      id: "located",
      label: "Located",
      state: !items.length ? "na" : located === items.length ? "yes" : located ? "partial" : "unrecorded",
      detail: items.length ? `${located} of ${items.length} results placed on a page of the PDF` : "",
    },
    {
      id: "dependencies",
      label: "Dependencies",
      state: !documentMapsDependencies
        ? "unrecorded"
        : !items.length
          ? "na"
          : mapped === items.length
            ? "yes"
            : mapped
              ? "partial"
              : "no",
      detail: !documentMapsDependencies
        ? "The source has no per-result dependency table"
        : `${mapped} of ${items.length} results carry a dependency row`,
    },
    {
      id: "branch",
      label: node.shape === "decision" ? "Cases" : node.shape === "terminal" ? "Closure" : "Cases",
      state:
        node.shape === "decision"
          ? outgoing.length >= 2 && !cases!.unlabelled
            ? "yes"
            : outgoing.length
              ? "partial"
              : "no"
          : node.shape === "terminal"
            ? node.open
              ? "no"
              : closure
                ? "yes"
                : "unrecorded"
            : "na",
      detail:
        node.shape === "decision"
          ? `${outgoing.length} arrows out, ${cases!.unlabelled} without a condition`
          : node.shape === "terminal"
            ? node.open
              ? "The source draws this leaf as open: no closure is claimed"
              : closure
                ? "The closure table records how this leaf closes"
                : "The closure table has no row for this leaf"
            : "",
    },
    reviewCheck("lean", "Producer exists", review),
    reviewCheck("kernel", "Producer finished", review),
    reviewCheck("fidelity", "Matches manuscript", review),
    reviewCheck("wired", "Arm probed closed", review),
    reviewCheck("local", "Residual-local", review),
    reviewCheck("external", "External input", review),
    reviewCheck("human", "Human review", review),
  ];

  return {
    claim: node.formalContent || node.overview,
    failureRoute: node.failureRoute && node.failureRoute !== "---" ? node.failureRoute : undefined,
    state: deriveState(document, index, node),
    cases,
    closure,
    evidence: { items, blocks: node.blocks, builds },
    impact: {
      successors: outgoing,
      // The walk always includes its start.
      downstreamCount: downstream.size - 1,
      terminals,
      alsoUsedAt,
    },
    sources: [...sources.values()],
    checks,
  };
}
