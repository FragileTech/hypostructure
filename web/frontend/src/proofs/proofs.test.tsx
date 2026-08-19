/**
 * Checks the explorer against the real extracted papers: the shape of each
 * document, and that a node's display unit shows the mathematics behind it.
 */

import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import katex from "katex";
import { cleanup, render, screen, within } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { beforeAll, describe, expect, it } from "vitest";

import { MemoryRouter } from "react-router-dom";

import {
  GraphExplorer,
  MathProvider,
  NodeDetailPanel,
  RefereePanel,
  refereeDossier,
  buildGraph,
  TableView,
  createReferenceResolver,
  indexDocument,
  parseLatex,
  locate,
  traceFrom,
  type ChapterSource,
  type ProofGraphDocument,
} from "../graph-explorer";
import { PROOFS, paperUrl, type ProofEntry } from "./registry";

// Resolved from the Vitest root (web/frontend), which jsdom's import.meta cannot give.
function readJson<T>(path: string): T {
  return JSON.parse(readFileSync(resolve(process.cwd(), "public", path), "utf8")) as T;
}

/** The document with its manuscripts' page maps attached, as the hook serves it. */
function load(proof: ProofEntry): ProofGraphDocument {
  const document = readJson<ProofGraphDocument>(`data/${proof.slug}.json`);
  const sources: Record<string, ChapterSource> = {};
  for (const paper of proof.papers) {
    const map = readJson<ChapterSource>(`data/pages/${paper.file.replace(/\.pdf$/, "")}.json`);
    sources[paper.chapter] = { title: paper.title, url: paperUrl(paper), pages: map.pages, labels: map.labels };
  }
  return { ...document, sources };
}

const DOCUMENTS = new Map(PROOFS.map((proof) => [proof.slug, load(proof)]));
const ERDOS = DOCUMENTS.get("erdos-gyarfas")!;
const NAVIER_STOKES = DOCUMENTS.get("navier-stokes")!;

beforeAll(() => {
  // KaTeX measures glyphs; jsdom has no layout, which is fine for these assertions.
  window.HTMLElement.prototype.scrollIntoView = () => {};
});

function show(document: ProofGraphDocument, nodeId: string, focusItem: string | null = null) {
  const index = indexDocument(document);
  const node = index.nodeById.get(nodeId)!;
  const references = createReferenceResolver(document, index, node.chapter);
  return render(
    <MathProvider
      macros={document.macros}
      onReference={() => {}}
      resolveReference={references.resolve}
    >
      <NodeDetailPanel
        document={document}
        index={index}
        node={node}
        focusItem={focusItem}
        onSelectNode={() => {}}
        onSelectItem={() => {}}
        onSelectInvariant={() => {}}
      />
    </MathProvider>,
  );
}

/** The same step, read as a referee. */
function showReferee(document: ProofGraphDocument, nodeId: string, focusItem: string | null = null) {
  const index = indexDocument(document);
  const node = index.nodeById.get(nodeId)!;
  const references = createReferenceResolver(document, index, node.chapter);
  return render(
    <MathProvider
      macros={document.macros}
      onReference={() => {}}
      resolveReference={references.resolve}
    >
      <RefereePanel
        document={document}
        index={index}
        node={node}
        focusItem={focusItem}
        onSelectNode={() => {}}
        onSelectItem={() => {}}
        onSelectInvariant={() => {}}
      />
    </MathProvider>,
  );
}

describe.each([...DOCUMENTS])("the %s document", (_slug, document) => {
  it("has a registry entry and a self-consistent header", () => {
    expect(document.nodes.length).toBe(document.source.diagramNodes);
    expect(document.groups.length).toBe(document.source.figures);
    expect(document.source.files.length).toBeGreaterThan(0);
  });

  it("marks a step open only when it is a terminal", () => {
    for (const node of document.nodes) {
      if (node.open) expect(node.shape).toBe("terminal");
    }
  });

  it("is one connected argument", () => {
    expect(traceFrom(document.edges, document.nodes[0].id, "both").nodeIds.size).toBe(
      document.nodes.length,
    );
  });

  it("lays every step out without losing one", () => {
    const { nodes, edges } = buildGraph(document);
    expect(nodes).toHaveLength(document.nodes.length);
    expect(edges).toHaveLength(document.edges.length);
  });

  it("gives each step only the results that are its own", () => {
    const counts = document.nodes.map((node) => node.itemRefs.length);
    expect(Math.max(...counts)).toBeLessThanOrEqual(30);
  });

  it("resolves every reference it shows", () => {
    const index = indexDocument(document);
    for (const node of document.nodes) {
      for (const key of node.itemRefs) expect(index.itemByKey.has(key)).toBe(true);
      for (const block of node.blocks) {
        for (const key of block.itemRefs) expect(index.itemByKey.has(key)).toBe(true);
      }
    }
  });
});

describe("the Erdos-Gyarfas branch test at [15]", () => {
  it("shows its question, its own result and both branches", () => {
    show(ERDOS, "15");

    expect(screen.getByText("Branch test")).toBeInTheDocument();
    expect(screen.getByLabelText("Node 15").querySelector(".badge-number")).toHaveTextContent(
      "15",
    );

    // Its own result is the corollary; the external theorem belongs to the block.
    // The paper gives this corollary no title, so its key stands in.
    expect(screen.getByText("cor:p13-exists")).toBeInTheDocument();
    expect(screen.getByText("Corollaries")).toBeInTheDocument();
    expect(screen.getByText("Used across this stretch of the argument")).toBeInTheDocument();

    const leadsTo = screen.getByText("Leads to").parentElement!;
    expect(within(leadsTo).getByText("16")).toBeInTheDocument();
    expect(within(leadsTo).getByText("17")).toBeInTheDocument();
    expect(within(leadsTo).getAllByText(/^(yes|no)$/)).toHaveLength(2);
  });

  it("reveals the statement, the plain reading and the role when expanded", () => {
    show(ERDOS, "15", "cor:p13-exists");
    expect(screen.getByText("What it does")).toBeInTheDocument();
    expect(screen.getByText("Its role in the argument")).toBeInTheDocument();
    // The reader is sent to the page of the PDF, with the source line kept as
    // the finer address.
    const where = locate(ERDOS, "erdos-gyarfas", "cor:p13-exists")!;
    const source = screen.getByText(/cor:p13-exists · stated on/);
    const link = within(source).getByRole("link", { name: `page ${where.page} of The paper` });
    expect(link).toHaveAttribute("href", `${paperUrl(PROOFS[0].papers[0])}#page=${where.page}`);
    expect(source).toHaveTextContent(/\(line \d+ of the source\)/);
  });

  it("falls back to the source line when no page map is at hand", () => {
    show({ ...ERDOS, sources: undefined }, "15", "cor:p13-exists");
    expect(screen.getByText(/cor:p13-exists · stated on line \d+ of the paper/)).toBeInTheDocument();
  });
});

describe("the page maps", () => {
  it("place every result and display of every proof on a page of its PDF", () => {
    for (const proof of PROOFS) {
      const document = DOCUMENTS.get(proof.slug)!;
      for (const record of [...document.items, ...document.equations]) {
        const where = locate(document, record.chapter, record.key);
        expect(where, record.key).toBeDefined();
        expect(where!.page).toBeGreaterThanOrEqual(1);
        expect(where!.page).toBeLessThanOrEqual(document.sources![record.chapter ?? proof.slug].pages);
      }
    }
  });
});

describe("the Erdos-Gyarfas terminal at [124]", () => {
  it("explains how the leaf closes and that nothing follows", () => {
    show(ERDOS, "124");
    expect(screen.getByText("Terminal")).toBeInTheDocument();
    expect(screen.getByText("How this leaf closes")).toBeInTheDocument();
    expect(screen.getByText("Closing condition")).toBeInTheDocument();
    expect(screen.getByText(/nothing — the branch ends here/)).toBeInTheDocument();
  });
});

describe("the Erdos-Gyarfas neutral configuration at [163]", () => {
  it("is now a branch test in Part XII, and the paper leaves no outcome open", () => {
    const node = ERDOS.nodes.find((candidate) => candidate.id === "163")!;
    expect(node.open).toBeUndefined();
    expect(node.shape).toBe("decision");
    expect(node.group).toBe("fig:proof-diagram-part-xii");
    expect(ERDOS.nodes.filter((candidate) => candidate.open)).toEqual([]);

    show(ERDOS, "163");
    expect(screen.getByText("Branch test")).toBeInTheDocument();
    expect(screen.queryByText("Open")).not.toBeInTheDocument();
    cleanup();

    showReferee(ERDOS, "163");
    expect(screen.getByLabelText("Node 163")).toBeInTheDocument();
    expect(screen.queryByText(/draws this outcome as open/)).not.toBeInTheDocument();
  });
});

describe("referee mode", () => {
  it("puts the evidence of a branch test first: standing, claim, state, cases", () => {
    showReferee(ERDOS, "15");
    const panel = screen.getByLabelText("Node 15");

    // The strip says where the step stands, and is honest about silence.
    const strip = within(panel).getByLabelText("Review status");
    expect(within(strip).getByText("Manuscript").nextSibling).toHaveTextContent("yes");
    expect(within(strip).getByText("Located").nextSibling).toHaveTextContent("yes");
    expect(within(strip).getByText("Cases").nextSibling).toHaveTextContent("yes");
    expect(within(strip).getByText("Producer exists").nextSibling).toHaveTextContent("yes");
    expect(within(strip).getByText("Producer finished").nextSibling).toHaveTextContent("yes");
    // The dimension a kernel check cannot answer: does the producer publish the
    // manuscript's statement? [15] is `cor:p13-exists`, and it does.
    expect(within(strip).getByText("Matches manuscript").nextSibling).toHaveTextContent("yes");

    // Then, in order, the claim, the state and the cases.
    const headings = within(panel)
      .getAllByRole("heading", { level: 3 })
      .map((heading) => heading.textContent);
    expect(headings.slice(0, 3)).toEqual(["Claim", "State at this step", "Cases 2"]);

    const before = within(panel).getByText("Available before").parentElement!;
    // Constraints 1..13 are tracked upstream of [15]; the split itself tracks none.
    expect(within(before).getByTitle(/^Constraint 1:/)).toBeInTheDocument();
    expect(within(before).getByTitle(/^Constraint 13:/)).toBeInTheDocument();
    expect(within(panel).getByText("Establishes").parentElement).toHaveTextContent("none recorded");

    const cases = within(panel).getAllByRole("row").slice(1);
    expect(cases).toHaveLength(2);
    expect(cases[0]).toHaveTextContent("yes");
    expect(within(cases[0]).getByText("16")).toBeInTheDocument();
    expect(cases[1]).toHaveTextContent("no");
    expect(within(cases[1]).getByText("17")).toBeInTheDocument();
    expect(within(panel).getByText(/records no separate argument that they exhaust/)).toBeInTheDocument();

    // Its own result, what it builds on, and where it falls.
    expect(within(panel).getAllByText("cor:p13-exists").length).toBeGreaterThan(0);
    expect(within(panel).getByText("Rests on").parentElement).toHaveTextContent(/Hegde/);
    expect(within(panel).getByText(/165 later steps/)).toBeInTheDocument();
    const where = locate(ERDOS, "erdos-gyarfas", "cor:p13-exists")!;
    expect(within(panel).getAllByText(`page ${where.page} of The paper`)[0]).toHaveAttribute(
      "href",
      `${paperUrl(PROOFS[0].papers[0])}#page=${where.page}`,
    );
  });

  it("finds every declared input of every Erdős–Gyárfás step already on the table", () => {
    // The paper's rule for its requirement rows, read along the diagram: a
    // constraint a result names as input is tracked at that step or upstream,
    // never only on a sibling branch — and every number named is a ledger row.
    const index = indexDocument(ERDOS);
    const stray = ERDOS.nodes.flatMap((node) => {
      const { state } = refereeDossier(ERDOS, index, node);
      return [
        ...state.unavailable.map((invariant) => `[${node.id}] reads ${invariant.number} early`),
        ...state.dangling.map((cited) => `[${node.id}] cites ${cited.number}`),
      ];
    });
    expect(stray).toEqual([]);
    // [135] supplies the exact window-join identity on the surplus branch, where
    // the ledger already tracks the near-cubic estimates.
    expect(
      refereeDossier(ERDOS, index, index.nodeById.get("135")!).state.establishes.map(
        (invariant) => invariant.number,
      ),
    ).toEqual([14, 15, 23]);
  });

  it("says the Navier–Stokes papers declare no per-result inputs, and flags nothing", () => {
    const index = indexDocument(NAVIER_STOKES);
    for (const node of NAVIER_STOKES.nodes) {
      const { state } = refereeDossier(NAVIER_STOKES, index, node);
      expect(state.recorded).toBe(false);
      expect(state.reads).toEqual([]);
      expect(state.unavailable).toEqual([]);
      expect(state.dangling).toEqual([]);
    }
    showReferee(NAVIER_STOKES, "S2");
    expect(screen.getByText("Reads").parentElement).toHaveTextContent("not recorded");
  });

  it("gives a leaf its closure, with the closing results to open", () => {
    showReferee(ERDOS, "124");
    const panel = screen.getByLabelText("Node 124");
    expect(within(panel).getByRole("heading", { level: 3, name: "Closure" })).toBeInTheDocument();
    expect(within(panel).getByText("If the result were false")).toBeInTheDocument();
    expect(within(panel).getByText("Closing results")).toBeInTheDocument();
    expect(within(panel).getByText("Reads").parentElement).not.toHaveTextContent("none recorded");
    expect(within(panel).getByText("No later step")).toBeInTheDocument();
    expect(within(panel).getByText(/nothing — the branch ends here/)).toBeInTheDocument();
  });

  it("degrades to what the source records on a paper without a dependency layer", () => {
    showReferee(NAVIER_STOKES, "S2");
    const panel = screen.getByLabelText("Node S2");
    const strip = within(panel).getByLabelText("Review status");
    expect(within(strip).getByText("Dependencies").nextSibling).toHaveTextContent("not recorded");
    expect(within(panel).getAllByRole("row").length).toBeGreaterThan(1);
  });

  it("is what the explorer shows when asked to read as a referee", async () => {
    const user = userEvent.setup();
    const changes: Record<string, unknown>[] = [];
    render(
      <MemoryRouter>
        <GraphExplorer
          document={ERDOS}
          state={{
            selected: "15",
            chapter: null,
            group: null,
            trace: "none",
            query: "",
            item: null,
            mode: "referee",
            constraint: null,
          }}
          onChange={(patch) => changes.push(patch)}
        />
      </MemoryRouter>,
    );
    // Queried by text: computing accessible names over the whole canvas trips jsdom.
    expect(screen.getByText("Referee")).toHaveClass("is-active");
    expect(screen.getByLabelText("Review status")).toBeInTheDocument();
    expect(screen.queryByText("What this step does")).not.toBeInTheDocument();

    await user.click(screen.getByText("Reader"));
    expect(changes).toContainEqual({ mode: "reader" });
  });

  it("lights up a constraint from its chip, and puts the light out from the same chip", async () => {
    const user = userEvent.setup();
    const index = indexDocument(ERDOS);
    const step = ERDOS.nodes.find((node) => node.invariantRefs.length)!;
    const invariant = index.invariantById.get(step.invariantRefs[0])!;
    const changes: Record<string, unknown>[] = [];
    const explorer = (constraint: string | null) => (
      <MemoryRouter>
        <GraphExplorer
          document={ERDOS}
          state={{
            selected: step.id,
            chapter: null,
            group: null,
            trace: "none",
            query: "",
            item: null,
            mode: "referee",
            constraint,
          }}
          onChange={(patch) => changes.push(patch)}
        />
      </MemoryRouter>
    );
    const view = render(explorer(null));
    const panel = view.container.querySelector(".node-detail-referee")!;
    const chip = () =>
      within(panel as HTMLElement)
        .getAllByRole("button")
        .find((button) => button.textContent?.startsWith(String(invariant.number)))!;

    await user.click(chip());
    expect(changes).toContainEqual({ constraint: invariant.id, query: "" });

    // With the constraint lit, the chip reads as pressed and the toolbar offers to clear it.
    view.rerender(explorer(invariant.id));
    expect(chip()).toHaveAttribute("aria-pressed", "true");
    expect(view.container.querySelectorAll(".proof-node.is-matched").length).toBe(
      index.nodesByInvariant.get(invariant.id)!.length,
    );
    // The selected step stays legible even when the constraint dims the rest.
    expect(view.container.querySelector(".proof-node.is-selected")).not.toHaveClass("is-dimmed");

    // Kernel-verified steps carry a check; steps still resting on an unfinished
    // producer do not.  [7] counts as proved even though it is a terminal the
    // proof only ever refutes -- discharging the branch is the proof of it.
    // [124] has no Lean at all: its one route runs through an undefined producer.
    const badge = (id: string) =>
      view.container
        .querySelector(`.react-flow__node[data-id="${id}"] .proof-node-verified`);
    expect(badge("5")).not.toBeNull();
    expect(badge("7")).not.toBeNull();
    expect(badge("124")).toBeNull();
    expect(screen.getByRole("status")).toHaveTextContent("clear");

    changes.length = 0;
    await user.click(chip());
    expect(changes).toContainEqual({ constraint: null, query: "" });
    await user.click(within(screen.getByRole("status")).getByRole("button"));
    expect(changes).toContainEqual({ constraint: null });
  });
});

describe("the Navier-Stokes document", () => {
  it("spans three papers, and says which one a step belongs to", () => {
    expect(NAVIER_STOKES.chapters).toHaveLength(3);
    show(NAVIER_STOKES, "I12");
    expect(screen.getByText("Type I residual")).toBeInTheDocument();
    expect(screen.getByText(/Node \[12\] of Closing the Type I residual class/)).toBeInTheDocument();
  });

  it("keeps the three papers' node numbers apart", () => {
    const index = indexDocument(NAVIER_STOKES);
    expect(index.nodeById.get("S12")!.chapter).toBe("setup");
    expect(index.nodeById.get("II12")!.chapter).toBe("type-ii");
    expect(index.nodeById.get("S12")!.number).toBe("12");
  });

  it("draws only one paper when a chapter is chosen", () => {
    const { nodes } = buildGraph(NAVIER_STOKES, { chapter: "setup" });
    expect(nodes).toHaveLength(39);
    expect(nodes.every((node) => node.data.node.chapter === "setup")).toBe(true);
  });

  it("shows the proof of a result alongside its statement", () => {
    const proved = new Set(
      NAVIER_STOKES.items.filter((item) => item.proofLatex).map((item) => item.key),
    );
    const holder = NAVIER_STOKES.nodes.find((node) =>
      node.itemRefs.some((key) => proved.has(key)),
    )!;
    const key = holder.itemRefs.find((candidate) => proved.has(candidate))!;
    show(NAVIER_STOKES, holder.id, key);
    expect(screen.getAllByText("Proof").length).toBeGreaterThan(0);
  });

  it("routes the entry step into the Type II paper", () => {
    const index = indexDocument(NAVIER_STOKES);
    const targets = (index.outgoing.get("S4") ?? []).map((edge) => edge.target);
    expect(targets).toContain("II1");
  });
});

describe("the result dropdowns", () => {
  it("open independently, so several can be read at once", async () => {
    const user = userEvent.setup();
    // [124] carries seven results of its own.
    show(ERDOS, "124");

    const summaries = screen.getAllByRole("group").filter((element) =>
      element.classList.contains("item"),
    ) as HTMLDetailsElement[];
    expect(summaries.length).toBeGreaterThan(2);
    expect(summaries.every((item) => !item.open)).toBe(true);

    await user.click(summaries[0].querySelector("summary")!);
    await user.click(summaries[1].querySelector("summary")!);

    expect(summaries[0].open).toBe(true);
    expect(summaries[1].open).toBe(true);
  });

  it("close again when clicked a second time", async () => {
    const user = userEvent.setup();
    show(ERDOS, "124");
    const [first] = screen.getAllByRole("group").filter((element) =>
      element.classList.contains("item"),
    ) as HTMLDetailsElement[];

    const summary = first.querySelector("summary")!;
    await user.click(summary);
    expect(first.open).toBe(true);
    await user.click(summary);
    expect(first.open).toBe(false);
  });

  it("opens the one a cross-reference points at", () => {
    show(ERDOS, "124", "thm:typeA-two-carrier-nogo");
    const opened = screen
      .getAllByRole("group")
      .filter((element) => element.classList.contains("item")) as HTMLDetailsElement[];
    expect(opened.filter((item) => item.open)).toHaveLength(1);
  });
});

describe("references inside a statement", () => {
  it("resolve to a display the papers label", () => {
    const index = indexDocument(NAVIER_STOKES);
    const equation = index.equationByKey.get("setup/p0:eq:paper0-local-typeI-bound");
    expect(equation?.latex).toContain("\\sqrt{T-t}");
  });

  it("cover nearly every reference the statements and proofs make", () => {
    for (const document of DOCUMENTS.values()) {
      const index = indexDocument(document);
      const chapters = (document.chapters ?? [{ id: "" }]).map((chapter) => chapter.id);
      let total = 0;
      let unresolved = 0;

      for (const item of document.items) {
        const source = `${item.statementLatex} ${item.proofLatex ?? ""}`;
        for (const match of source.matchAll(/\\(?:eqref|ref|[cC]ref)\{([^}]*)\}/g)) {
          for (const raw of match[1].split(",")) {
            const key = raw.trim();
            // Sections, tables and figures of the paper have no page of their own.
            if (/^(sec|subsec|tab|fig|app):/.test(key)) continue;
            total += 1;
            const known = chapters.some((chapter) => {
              const scoped = chapter ? `${chapter}/${key}` : key;
              return index.itemByKey.has(scoped) || index.equationByKey.has(scoped);
            });
            if (!known) unresolved += 1;
          }
        }
      }

      expect(total).toBeGreaterThan(100);
      expect(unresolved / total).toBeLessThan(0.02);
    }
  });
});

describe("a reference to an auxiliary result", () => {
  it("unfolds the statement as prose, with its mathematics rendered", async () => {
    const user = userEvent.setup();
    const index = indexDocument(ERDOS);
    // A result no step claims, cited from one that a step does claim — the
    // definition of a sparse surplus blocker, cited by the blocker ledger.
    const auxiliary = index.itemByKey.get("def:surplus-blockers")!;
    const citer = index.itemByKey.get("def:canonical-blocker-ledger")!;
    expect(index.nodesByItem.get(auxiliary.key) ?? []).toHaveLength(0);
    expect(citer.statementLatex).toContain(`{${auxiliary.key}}`);
    const holder = index.nodesByItem.get(citer.key)![0];

    showReferee(ERDOS, holder, citer.key);
    const reference = screen.getAllByTitle(auxiliary.key)[0];
    await user.click(reference);

    const unfolded = document.querySelector(".latex-inline-reference")!;
    expect(unfolded).not.toBeNull();
    // Read by the LaTeX reader, not handed whole to KaTeX: maths renders and no
    // raw delimiter or macro leaks into the text.
    expect(unfolded.querySelector(".katex")).not.toBeNull();
    expect(unfolded.textContent).not.toMatch(/\\\(|\\emph|\\begin/);
    expect(unfolded.querySelector(".katex-error")).toBeNull();
  });
});

describe("a reference to a numbered display", () => {
  it("unfolds the equation where it stands, without moving the reader", async () => {
    const user = userEvent.setup();
    const index = indexDocument(NAVIER_STOKES);
    const equation = index.equationByKey.get("setup/p0:eq:paper0-local-typeI-bound")!;

    // [S6] cites that display inside its lemma's statement.
    show(NAVIER_STOKES, "S6", "setup/p0:lem:terminal-A-from-weak-serrin");

    // The title names the display exactly, since the number shown is this
    // site's own count rather than the paper's.
    const where = locate(NAVIER_STOKES, equation.chapter, equation.key)!;
    const reference = screen.getByTitle(`p0:eq:paper0-local-typeI-bound · page ${where.page}`);
    expect(reference).toHaveTextContent(`(${equation.number})`);
    expect(reference).toHaveAttribute("aria-expanded", "false");
    expect(document.querySelector(".latex-inline-reference")).toBeNull();

    await user.click(reference);

    expect(reference).toHaveAttribute("aria-expanded", "true");
    expect(document.querySelector(".latex-inline-reference")).not.toBeNull();

    await user.click(reference);
    expect(document.querySelector(".latex-inline-reference")).toBeNull();
  });
});

describe("every piece of mathematics the site shows", () => {
  it.each([...DOCUMENTS])("renders in the %s papers", (_slug, document) => {
    const failures: string[] = [];
    let total = 0;

    const check = (source: string | undefined, where: string) => {
      for (const segment of parseLatex(source ?? "")) {
        if (segment.kind !== "math") continue;
        total += 1;
        try {
          const html = katex.renderToString(segment.value, {
            displayMode: segment.display,
            throwOnError: true,
            strict: false,
            macros: { ...document.macros },
          });
          if (html.includes("katex-error")) failures.push(`${where}: ${segment.value}`);
        } catch (error) {
          failures.push(`${where}: ${(error as Error).message}`);
        }
      }
    };

    for (const node of document.nodes) {
      check(node.label, `node ${node.id}`);
      check(node.overview, `overview ${node.id}`);
    }
    for (const item of document.items) {
      check(item.statementLatex, `statement ${item.key}`);
      check(item.proofLatex, `proof ${item.key}`);
    }
    for (const equation of document.equations) check(equation.latex, `equation ${equation.key}`);
    for (const constant of document.constants) check(constant.meaning, "constant");
    for (const invariant of document.invariants) check(invariant.constraint, "constraint");

    expect(total).toBeGreaterThan(1000);
    // Joined, so a failure names the expression instead of showing a diff.
    expect(failures.slice(0, 4).join("\n")).toBe("");
  });
});

describe("the canvas with no step selected", () => {
  function explorer(state: Partial<Parameters<typeof GraphExplorer>[0]["state"]> = {}) {
    return render(
      <MemoryRouter>
        <GraphExplorer
          document={NAVIER_STOKES}
          state={{
            selected: null,
            chapter: null,
            group: null,
            trace: "none",
            query: "",
            item: null,
            mode: "reader",
            constraint: null,
            ...state,
          }}
          onChange={() => {}}
        />
      </MemoryRouter>,
    );
  }

  it("describes the panel in view", () => {
    const panel = NAVIER_STOKES.groups.find((group) => group.chapter === "type-ii")!;
    explorer({ chapter: "type-ii", group: panel.id });
    expect(screen.getAllByText(panel.title).length).toBeGreaterThan(0);
    expect(screen.getByText(new RegExp(panel.summary.slice(0, 40)))).toBeInTheDocument();
  });

  it("describes the paper when no panel is chosen", () => {
    const chapter = NAVIER_STOKES.chapters!.find((entry) => entry.id === "type-i")!;
    explorer({ chapter: "type-i" });
    expect(screen.getByText(chapter.title)).toBeInTheDocument();
    expect(screen.getByText(chapter.description)).toBeInTheDocument();
  });

  it("describes the whole proof when nothing is filtered", () => {
    explorer();
    expect(screen.getByText(NAVIER_STOKES.title)).toBeInTheDocument();
    expect(screen.getByText(NAVIER_STOKES.subtitle)).toBeInTheDocument();
  });
});

describe("panel summaries", () => {
  it.each([...DOCUMENTS])("never repeat the drawing legend in %s", (_slug, document) => {
    for (const group of document.groups) {
      for (const field of [group.summary, group.caption]) {
        expect(field).not.toMatch(/Rectangles are assertions/);
        expect(field).not.toMatch(/use the convention of/);
        expect(field.trimStart()).not.toMatch(/^Proof-dependency diagram/);
      }
    }
  });

  it.each([...DOCUMENTS])("say something different from the title in %s", (_slug, document) => {
    for (const group of document.groups) {
      expect(group.summary.length).toBeGreaterThan(60);
      expect(group.summary).not.toContain(group.title);
    }
  });

  it("name what a caption points at rather than printing its key", () => {
    const index = indexDocument(ERDOS);
    const references = createReferenceResolver(ERDOS, index);
    expect(references.resolve("fig:proof-diagram-part-x").label).toBe(
      "Part X - Sparse surplus accounting",
    );
  });
});

describe("a branch row with nothing to list", () => {
  it("reads as one line: the label, then the note", () => {
    // [1] is where the argument starts, so nothing arrives at it.
    show(ERDOS, "1");
    const row = document.querySelector(".branch-row.is-empty")!;
    expect(row).not.toBeNull();
    expect(row.textContent).toBe("Arrives fromnothing — the argument starts here");

    // Short enough to sit beside its label even in a narrowed column.
    const note = row.querySelector(".branch-none")!.textContent!;
    expect(note.length).toBeLessThanOrEqual(34);
  });

  it("says so at a terminal too", () => {
    show(ERDOS, "124");
    const rows = [...document.querySelectorAll(".branch-row.is-empty")];
    expect(rows).toHaveLength(1);
    expect(rows[0].textContent).toBe("Leads tonothing — the branch ends here");
  });
});

describe("the papers' own tables", () => {
  it.each([...DOCUMENTS])("index the argument in %s", (_slug, document) => {
    expect(document.tables.length).toBeGreaterThan(10);
    for (const table of document.tables) {
      expect(table.rows.length).toBeGreaterThan(0);
      expect(table.rows.every((row) => row.length === table.headers.length)).toBe(true);
    }
  });

  it("lets a cell's step number lead to that step", async () => {
    const user = userEvent.setup();
    const index = indexDocument(NAVIER_STOKES);
    // The Type I audit numbers its steps from one; the link needs the prefix.
    const table = NAVIER_STOKES.tables.find(
      (entry) => entry.chapter === "type-i" && entry.title === "Node-by-node audit table",
    )!;
    const followed: string[] = [];

    render(
      <MathProvider
        macros={NAVIER_STOKES.macros}
        onNode={(number) => followed.push(`${index.chapterById.get("type-i")!.prefix}${number}`)}
      >
        <TableView table={{ ...table, rows: table.rows.slice(0, 3) }} />
      </MathProvider>,
    );

    await user.click(screen.getAllByRole("button", { name: "1" })[0]);
    expect(followed).toEqual(["I1"]);
    expect(index.nodeById.has("I1")).toBe(true);
  });

  it("keeps every table's step numbers pointing at real steps", () => {
    for (const [, document] of DOCUMENTS) {
      const index = indexDocument(document);
      const prefixes = new Map(
        (document.chapters ?? []).map((chapter) => [chapter.id, chapter.prefix]),
      );
      for (const table of document.tables) {
        const prefix = prefixes.get(table.chapter ?? "") ?? "";
        for (const row of table.rows) {
          for (const segment of parseLatex(row.join(" "), { nodes: true })) {
            if (segment.kind !== "node") continue;
            expect(index.nodeById.has(`${prefix}${segment.id}`)).toBe(true);
          }
        }
      }
    }
  });
});
