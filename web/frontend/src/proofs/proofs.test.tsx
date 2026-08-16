/**
 * Checks the explorer against the real extracted papers: the shape of each
 * document, and that a node's display unit shows the mathematics behind it.
 */

import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import katex from "katex";
import { render, screen, within } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { beforeAll, describe, expect, it } from "vitest";

import { MemoryRouter } from "react-router-dom";

import {
  GraphExplorer,
  MathProvider,
  NodeDetailPanel,
  buildGraph,
  createReferenceResolver,
  indexDocument,
  parseLatex,
  traceFrom,
  type ProofGraphDocument,
} from "../graph-explorer";
import { PROOFS } from "./registry";

// Resolved from the Vitest root (web/frontend), which jsdom's import.meta cannot give.
function load(slug: string): ProofGraphDocument {
  return JSON.parse(
    readFileSync(resolve(process.cwd(), `public/data/${slug}.json`), "utf8"),
  ) as ProofGraphDocument;
}

const DOCUMENTS = new Map(PROOFS.map((proof) => [proof.slug, load(proof.slug)]));
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

describe.each([...DOCUMENTS])("the %s document", (_slug, document) => {
  it("has a registry entry and a self-consistent header", () => {
    expect(document.nodes.length).toBe(document.source.diagramNodes);
    expect(document.groups.length).toBe(document.source.figures);
    expect(document.source.files.length).toBeGreaterThan(0);
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
    expect(screen.getByText(/cor:p13-exists · stated on line/)).toBeInTheDocument();
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

describe("a reference to a numbered display", () => {
  it("unfolds the equation where it stands, without moving the reader", async () => {
    const user = userEvent.setup();
    const index = indexDocument(NAVIER_STOKES);
    const equation = index.equationByKey.get("setup/p0:eq:paper0-local-typeI-bound")!;

    // [S6] cites that display inside its lemma's statement.
    show(NAVIER_STOKES, "S6", "setup/p0:lem:terminal-A-from-weak-serrin");

    // The title names the display exactly, since the number shown is this
    // site's own count rather than the paper's.
    const reference = screen.getByTitle(
      `p0:eq:paper0-local-typeI-bound · line ${equation.sourceLine}`,
    );
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
