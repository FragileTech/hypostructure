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
  /**
   * True for a terminal the source leaves open: an outcome it draws (in red)
   * as not yet contradicted, rather than closed. Absent otherwise.
   */
  open?: boolean;
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

/**
 * One of the paper's own cross-reference tables, published as written.
 *
 * These index the argument — nodes against the results, constraints and routes
 * behind them — so a reader can navigate from the index rather than the canvas.
 */
export interface ProofTable {
  id: string;
  title: string;
  /** The section a run of related tables sits under, when there is one. */
  group: string;
  chapter?: string;
  sourceLine: number;
  headers: string[];
  /** Cells exactly as the paper writes them, LaTeX and all. */
  rows: string[][];
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

/** Where one label of a manuscript lands, in the source and in the PDF. */
export interface LabelLocation {
  /** 1-based line of the `\\label` in the LaTeX source. */
  line: number | null;
  /** 1-based page of the PDF the label was built into. */
  page: number | null;
  /** The number the paper prints for it, e.g. `13.4`. */
  number: string | null;
  /** The PDF's own named destination for it, e.g. `theorem.13.4`. */
  anchor: string | null;
}

/**
 * A manuscript as the reader can open it: the served PDF and the page each of
 * its labels lands on. Supplied by the host, one per chapter, from the page
 * maps `web/tools/extract_page_map.py` writes.
 */
export interface ChapterSource {
  /** How the host names the PDF, e.g. `Setup`. */
  title: string;
  /** URL of the PDF. */
  url: string;
  pages: number;
  /** Keyed by the raw label, without any chapter prefix. */
  labels: Record<string, LabelLocation>;
}

/**
 * How a step stands under review, along the dimensions a referee keeps apart.
 * Each is its own answer, and passing one never implies another:
 *
 * - `lean` — a producer for this step exists at all.
 * - `kernel` — that producer is finished, i.e. it does not reach a
 *   referenced-but-undefined declaration. Judged per producer: a large
 *   declaration runs many branch arms, and an unfinished sibling arm says
 *   nothing about this step.
 * - `wired` — the arm through this step was *probed* stub-free end to end. A
 *   measurement, not a property: an arm can pass through a declaration that is
 *   unfinished on its other arms, so `partial` means unprobed, not failing.
 * - `local` — the proposition is about the literal active residual rather
 *   than a detached universal.
 * - `fidelity` — the producer publishes the *manuscript's* statement. This is
 *   the one a kernel check cannot see: a row stating something weaker than its
 *   manuscript label still composes and still closes. A trivial proof counts as
 *   faithful when the paper's own step is equally immediate.
 * - `external` — the step leans on a declared external input.
 * - `human` — a person has read it. Left unrecorded where none has.
 */
export type ReviewState = "verified" | "partial" | "absent";

export interface NodeReview {
  lean?: ReviewState;
  kernel?: ReviewState;
  wired?: ReviewState;
  local?: ReviewState;
  fidelity?: ReviewState;
  external?: ReviewState;
  human?: ReviewState;
  note?: string;
}

/**
 * The review layer of a proof, keyed by node id. Supplied by the host as a
 * side-car, like `sources`; the explorer says "not recorded" where it is absent.
 */
export interface ProofReview {
  nodes: Record<string, NodeReview>;
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
  /**
   * The PDFs behind the chapters, keyed by chapter id (the slug when there is
   * one chapter), when the host has them. Lets a result say which page it is on.
   */
  sources?: Record<string, ChapterSource>;
  /** How each step stands under review, when the host has recorded it. */
  review?: ProofReview;
  groups: ProofGroup[];
  nodes: ProofNode[];
  edges: ProofEdge[];
  items: ProofItem[];
  equations: ProofEquation[];
  invariants: Invariant[];
  constants: NamedConstant[];
  tables: ProofTable[];
}

/** How the detail column reads a step: as a reader, or as a referee. */
export type ExplorerMode = "reader" | "referee";

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
