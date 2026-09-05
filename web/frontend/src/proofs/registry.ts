/**
 * The proofs this site hosts.
 *
 * The graph, the statements and the constants of each are extracted from its
 * manuscripts by `web/tools/extract_proof_graph.py`. What lives here is only the
 * framing a reader needs before the diagram makes sense: what the question is,
 * and how the argument is shaped.
 */

export interface ProofEntry {
  slug: string;
  /** Short name for the header switcher and the landing cards. */
  name: string;
  /** The question the paper answers, as a sentence. */
  question: string;
  /** One line for the landing card. */
  tagline: string;
  /** Paragraphs introducing the argument. May contain LaTeX. */
  overview: string[];
  /** Emblem for the landing card and the header. */
  glyph: string;
  /** The manuscripts, as PDFs served from `public/papers/`, in reading order. */
  papers: PaperFile[];
}

export interface PaperFile {
  /** File name under `public/papers/`. */
  file: string;
  /** How the header names it; short, since several may sit side by side. */
  title: string;
  /**
   * The chapter of the extracted document this manuscript is, as its items and
   * equations name it in `chapter`; the slug for a one-manuscript proof.
   */
  chapter: string;
}

/** Where a manuscript's PDF is served from. */
export function paperUrl(paper: PaperFile): string {
  return `${import.meta.env.BASE_URL}papers/${paper.file}`;
}

/**
 * Where a manuscript's page map is served from: the page every label of the
 * PDF lands on, written by `web/tools/extract_page_map.py`.
 */
export function pageMapUrl(paper: PaperFile): string {
  return `${import.meta.env.BASE_URL}data/pages/${paper.file.replace(/\.pdf$/, "")}.json`;
}

export const PROOFS: ProofEntry[] = [
  {
    slug: "erdos-gyarfas",
    name: "Erdős–Gyárfás",
    glyph: "2ᵏ",
    question:
      "Does every graph with minimum degree three contain a cycle whose length is a power of two?",
    tagline:
      "Erdős and Gyárfás asked this in 1995. The manuscript now exposes 188 diagram nodes; only [172a], [182], and [186] remain open.",
    papers: [{ file: "erdos_64_proof.pdf", title: "The paper", chapter: "erdos-gyarfas" }],
    overview: [
      "Erdős and Gyárfás asked this in 1995. The paper this site accompanies answers yes, and it does so by contradiction: assume a counterexample exists, take the smallest one, and squeeze it until nothing is left. The argument is long, and it branches. This is a way to walk it.",
      "A cycle of length $2^k$ exists exactly when some edge has a return path of length $2^k-1$ — a Mersenne number. That turns a question about geometry into one about arithmetic, and it is the target the whole proof aims at. If a minimal counterexample $G$ exists, then no edge of it has such a return, and every later step is a consequence of that single prohibition.",
      "From there the proof forces structure. Minimality makes $G$ edge-critical and its high-degree vertices independent. An external theorem says a $P_{13}$-free graph of minimum degree three already has a power-of-two cycle, so $G$ must contain induced paths on thirteen vertices. Packing those paths splits the graph into windows and a remainder, and the rest of the argument is an accounting contest between the two: how much two-step obstruction the remainder must supply against how much the windows can pay for. Wherever the books fail to balance, a branch closes.",
      "The implemented branches are now tracked against the manuscript's exact local contracts. The dense-packing continuation closes its covered arms through [173]–[180]. On route 8, [181] now routes exhaustively to the existing [124] closure or through the strict reductions [183]–[185] to the exact simultaneous balance at [186]. The remaining boundaries are shown explicitly in red at [172a], [182], and [186]; they are honest residual obligations, not claimed closures.",
    ],
  },
  {
    slug: "navier-stokes",
    name: "Navier–Stokes",
    glyph: "∇·u",
    question:
      "Can a finite-energy solution of the Navier–Stokes equations develop a singularity?",
    tagline:
      "Three manuscripts, 333 steps, closing every way a local singularity could form.",
    papers: [
      { file: "proof_setup.pdf", title: "Setup", chapter: "setup" },
      { file: "type_I_residual_closure.pdf", title: "Type I residual", chapter: "type-i" },
      { file: "type_II_regularity.pdf", title: "Type II regularity", chapter: "type-ii" },
    ],
    overview: [
      "Suppose a finite-energy suitable weak solution does go singular at some point in space and time. The local Caffarelli–Kohn–Nirenberg theory says a positive amount of critical mass must concentrate there. The argument this site accompanies takes that concentration apart, and shows every way it could happen is impossible.",
      "The first split is by rate. A Type I singularity is one whose blow-up respects the natural scaling of the equations; a Type II singularity is anything faster. The two branches are then closed by different means, and they are written up as separate manuscripts.",
      "On the Type I side, rescaling around the point and passing to the limit produces a nonzero ancient solution — a Seregin profile — that must lie in one of a fixed list of classes. The setup paper closes all but one of them by Liouville theorems. The residual paper takes the family that survives, decomposes it into axisymmetric, rotational, stationary-hull, affine, critical-tail and generic strata, and shows each stratum is empty.",
      "The Type II side never produces a clean limit, so it is handled as a state space instead. Every local concentration sequence is routed into one of a fixed set of exits — repaired gauge, multibubble, rough core, scale collapse, carrier routing, terminal profile — and the third manuscript closes each exit in turn. When every branch on both sides is closed, no singularity remains.",
    ],
  },
];

export const DEFAULT_PROOF = PROOFS[0];

export function findProof(slug: string | undefined): ProofEntry | undefined {
  return PROOFS.find((proof) => proof.slug === slug);
}
