/**
 * The document shape the explorer renders.
 *
 * Nothing in this module knows about any particular paper: give it a
 * `ProofGraphDocument` and it will draw the flow, trace branches, and render the
 * mathematics behind each node. To add another proof, produce this shape.
 */

export type NodeShape = "assertion" | "decision" | "terminal";

export type ItemKind =
  | "theorem"
  | "proposition"
  | "lemma"
  | "corollary"
  | "definition"
  | "remark";

/** One manuscript, when a proof is written across several. */
export interface ProofChapter {
  id: string;
  title: string;
  shortTitle: string;
  description: string;
  source: string;
  /** Prefixes node numbers so ids stay unique across chapters, e.g. `S12`. */
  prefix: string;
}

/** One panel of a diagram that the source splits across several figures. */
export interface ProofGroup {
  id: string;
  title: string;
  /** What this stretch of the argument does, in a sentence or two. */
  summary: string;
  /** The source's own caption, for the detail it adds beyond the summary. */
  caption: string;
  chapter?: string;
}

/** How a terminal leaf closes, and what would survive if it did not. */
export interface TerminalDossier {
  closingResult: string;
  closingItems: string[];
  closingCondition: string;
  slack: string;
  redundantCover: string;
  residualCounterexample: string;
  /** The path through the diagram that reaches this leaf, when recorded. */
  route?: string;
}

/**
 * Results the source attributes to a stretch of the argument rather than to one
 * step. Kept apart from a node's own results so a single step never claims
 * everything its block uses.
 */
export interface ProofBlock {
  name: string;
  /** The span as the source writes it, e.g. `[63], [86]--[109]`. */
  range: string;
  itemRefs: string[];
}

export interface ProofNode {
  /** Stable identifier, carrying the chapter prefix when there is one. */
  id: string;
  /** The number the source prints inside the node, without a prefix. */
  number: string;
  chapter?: string;
  /** The node's own text, as written in the diagram. May contain LaTeX math. */
  label: string;
  shape: NodeShape;
  group: string;
  /** One-line statement of what this step establishes. */
  overview: string;
  /** Other nodes restating the same assertion in a different panel. */
  aliases: string[];
  /** Keys into `ProofGraphDocument.items` — this step's own results. */
  itemRefs: string[];
  /** Results the source attributes to the wider block this step sits in. */
  blocks: ProofBlock[];
  invariantRefs: string[];
  constantRefs: string[];
  /** Names the source's own dependency table gives to this step. */
  topics: string[];
  formalContent?: string;
  failureRoute?: string;
  dossier?: TerminalDossier;
  /** Diagram-local identifier from the source, shown for cross-referencing. */
  tikzId?: string;
}

export interface ProofEdge {
  id: string;
  source: string;
  target: string;
  /** A branch condition such as `yes` or `no`, when the diagram labels one. */
  branch: string | null;
  /** `continuation` edges join panels; `flow` edges are drawn in one panel. */
  kind: "flow" | "continuation";
}

export interface ProofItem {
  /** Reference key, e.g. `lem:return-equivalence`. */
  key: string;
  kind: ItemKind;
  title: string;
  /** The statement exactly as the source writes it. */
  statementLatex: string;
  /** Its proof, when the source gives one. */
  proofLatex?: string;
  chapter?: string;
  sourceLine: number;
  /** Plain-language description, when the source supplies one. */
  plain?: string;
  /** What this result is for in the argument. */
  role?: string;
  /** Prerequisites, as written. */
  requires?: string;
  requiresItems?: string[];
  stage?: string;
}

/** A numbered display the source labels, so references can point at it. */
export interface ProofEquation {
  key: string;
  /** Its position among the labelled displays of its chapter. */
  number: number;
  latex: string;
  sourceLine: number;
  chapter?: string;
}

export interface Invariant {
  /** Unique across the document; a constraint number alone is not, because
   * every manuscript numbers its own from one. */
  id: string;
  number: number;
  chapter?: string;
  name: string;
  nodes: string[];
  constraint: string;
  budget: string;
  usedBy: string[];
}

export interface NamedConstant {
  symbol: string;
  chapter?: string;
  value: string;
  meaning: string;
  establishedIn: string[];
}

export interface ProofGraphDocument {
  id: string;
  title: string;
  subtitle: string;
  slug: string;
  source: { files: string[]; diagramNodes: number; figures: number };
  /** LaTeX macros the source defines, forwarded to the math renderer. */
  macros: Record<string, string>;
  /** Present when the proof is written across more than one manuscript. */
  chapters?: ProofChapter[];
  groups: ProofGroup[];
  nodes: ProofNode[];
  edges: ProofEdge[];
  items: ProofItem[];
  equations: ProofEquation[];
  invariants: Invariant[];
  constants: NamedConstant[];
}

/** Direction to follow when highlighting the branches around a node. */
export type TraceDirection = "upstream" | "downstream" | "both" | "none";

/** Indexes derived once per document so lookups stay O(1) while browsing. */
export interface ProofIndex {
  nodeById: Map<string, ProofNode>;
  itemByKey: Map<string, ProofItem>;
  equationByKey: Map<string, ProofEquation>;
  groupById: Map<string, ProofGroup>;
  chapterById: Map<string, ProofChapter>;
  invariantById: Map<string, Invariant>;
  constantBySymbol: Map<string, NamedConstant>;
  incoming: Map<string, ProofEdge[]>;
  outgoing: Map<string, ProofEdge[]>;
  nodesByInvariant: Map<string, string[]>;
  nodesByItem: Map<string, string[]>;
}
