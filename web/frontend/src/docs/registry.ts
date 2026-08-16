/**
 * The Hypostructure documentation: which pages exist, in reading order, and
 * how they group in the rail. Every page is hand-written TSX under
 * `content/`; adding one is an entry here and a file there.
 */

import type { ComponentType } from "react";

import { AssemblyPage } from "./content/Assembly";
import { ClosingPage } from "./content/Closing";
import { LedgerApiPage } from "./content/LedgerApi";
import { LedgerPage } from "./content/Ledger";
import { ProblemPage } from "./content/Problem";
import { ProblemApiPage } from "./content/ProblemApi";
import { ReadingFactsPage } from "./content/ReadingFacts";
import { ReplacementPage } from "./content/Replacement";
import { ScopePage } from "./content/Scope";
import { SemanticsApiPage } from "./content/SemanticsApi";
import { UtilitiesApiPage } from "./content/UtilitiesApi";
import { WritingFactsPage } from "./content/WritingFacts";

export interface DocsGroup {
  id: string;
  /** The rail heading. */
  title: string;
}

export interface DocsPageEntry {
  /** URL segment under `/lean/`. */
  slug: string;
  /** The page title, and its rail label. */
  title: string;
  /** One sentence for cards and the pager. */
  summary: string;
  group: DocsGroup["id"];
  Content: ComponentType;
}

export const DOCS_ROOT = "/lean";

export const DOCS_GROUPS: DocsGroup[] = [
  { id: "core", title: "The ledger" },
  { id: "problem", title: "Defining a problem" },
  { id: "assembly", title: "Assembling a proof" },
  { id: "reference", title: "Reference" },
];

export const DOCS_PAGES: DocsPageEntry[] = [
  {
    slug: "ledger",
    title: "The ExactLedger",
    summary:
      "The one indexed type that carries a branch: its residual, its facts, and why the type indices are the guarantee.",
    group: "core",
    Content: LedgerPage,
  },
  {
    slug: "reading-facts",
    title: "Reading facts",
    summary:
      "Availability is a type-class check. ExactLedger.get, FactInputs.get, and what the audit view shows.",
    group: "core",
    Content: ReadingFactsPage,
  },
  {
    slug: "writing-facts",
    title: "Writing facts",
    summary:
      "Manifests, steps and their sealed executors, factOnly, and running a step so its facts join the ledger's index.",
    group: "core",
    Content: WritingFactsPage,
  },
  {
    slug: "closing",
    title: "Closing a branch",
    summary:
      "Impossible and Incompatible facts, closeImpossible / closeIncompatible, elimClosed, direct closures, and why branches never leak.",
    group: "core",
    Content: ClosingPage,
  },
  {
    slug: "problem",
    title: "The problem is the only input",
    summary:
      "Problem, Target and Progress are the whole problem-specific input; the residual, its refinement and the contexts are derived.",
    group: "problem",
    Content: ProblemPage,
  },
  {
    slug: "scope",
    title: "Vocabulary and the opening scope",
    summary:
      "The fact vocabulary that becomes the domain's FactSystem, and opening the minimal-counterexample scope as a branch's first fact.",
    group: "problem",
    Content: ScopePage,
  },
  {
    slug: "assembly",
    title: "From steps to the theorem",
    summary:
      "Straight-line composition, freshness proofs, dichotomies, closing arms, minimality inside rows, and the bridge to the public statement.",
    group: "assembly",
    Content: AssemblyPage,
  },
  {
    slug: "replacement",
    title: "Interface replacement",
    summary:
      "Semantic equivalence, atom/context assembly, and Core's theorem that a strict replacement at a minimal counterexample is impossible.",
    group: "assembly",
    Content: ReplacementPage,
  },
  {
    slug: "ledger-api",
    title: "Ledger and execution API",
    summary:
      "Every public declaration of the ledger, manifest, execution and closure modules, with its signature and who may call it.",
    group: "reference",
    Content: LedgerApiPage,
  },
  {
    slug: "problem-api",
    title: "Problem API",
    summary:
      "Every public declaration of the problem kernel, the problem-input residual and the scope opener.",
    group: "reference",
    Content: ProblemApiPage,
  },
  {
    slug: "semantics-api",
    title: "Semantics and replacement API",
    summary:
      "Semantic equivalence, target invariance, atom/context assembly, and the interface-replacement exclusion.",
    group: "reference",
    Content: SemanticsApiPage,
  },
  {
    slug: "utilities-api",
    title: "Utility modules",
    summary:
      "Ceiling square root, dyadic lengths, target rank, certified table aggregation, and finite schedules.",
    group: "reference",
    Content: UtilitiesApiPage,
  },
];

export function findDocsPage(slug: string | undefined): DocsPageEntry | undefined {
  return DOCS_PAGES.find((page) => page.slug === slug);
}

export function docsPath(page: Pick<DocsPageEntry, "slug">): string {
  return `${DOCS_ROOT}/${page.slug}`;
}

/** The pages before and after one, in reading order. */
export function docsNeighbours(slug: string): {
  previous?: DocsPageEntry;
  next?: DocsPageEntry;
} {
  const index = DOCS_PAGES.findIndex((page) => page.slug === slug);
  if (index === -1) return {};
  return { previous: DOCS_PAGES[index - 1], next: DOCS_PAGES[index + 1] };
}
