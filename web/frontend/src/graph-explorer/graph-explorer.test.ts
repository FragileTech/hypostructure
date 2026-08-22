import { describe, expect, it } from "vitest";

import { buildGraph } from "./buildGraph";
import { indexDocument } from "./index-document";
import { latexToPlainText, parseLatex } from "./latex";
import { layoutGraph } from "./layout";
import { refereeDossier, requiredInvariantNumbers } from "./referee";
import { buildSearchIndex, matchNodes } from "./search";
import { TEST_DOCUMENT } from "./test-document";
import { traceFrom } from "./trace";
import { clampDetailWidth } from "./useDetailWidth";

describe("indexDocument", () => {
  const index = indexDocument(TEST_DOCUMENT);

  it("indexes nodes, results and panels", () => {
    expect(index.nodeById.get("2")?.shape).toBe("decision");
    expect(index.itemByKey.get("lem:halving")?.title).toBe("Halving preserves integrality");
    expect(index.groupById.get("part-b")?.title).toContain("even case");
  });

  it("indexes arrows in both directions", () => {
    expect(index.outgoing.get("2")?.map((edge) => edge.target)).toEqual(["3", "4"]);
    expect(index.incoming.get("6")?.map((edge) => edge.source)).toEqual(["5"]);
    expect(index.outgoing.get("6")).toBeUndefined();
  });

  it("indexes which steps share a result or a constraint", () => {
    expect(index.nodesByItem.get("lem:halving")).toEqual(["2", "4"]);
    expect(index.nodesByInvariant.get("one:1")).toEqual(["1", "2"]);
  });
});

describe("traceFrom", () => {
  const edges = TEST_DOCUMENT.edges;

  it("walks forwards", () => {
    const trace = traceFrom(edges, "2", "downstream");
    expect([...trace.nodeIds].sort()).toEqual(["2", "3", "4", "5", "6"]);
    expect(trace.edgeIds.has("e1")).toBe(false);
  });

  it("walks backwards", () => {
    const trace = traceFrom(edges, "6", "upstream");
    expect([...trace.nodeIds].sort()).toEqual(["1", "2", "4", "5", "6"]);
  });

  it("walks both ways", () => {
    expect(traceFrom(edges, "4", "both").nodeIds.size).toBe(5);
  });

  it("is empty when there is nothing to trace", () => {
    expect(traceFrom(edges, null, "both").nodeIds.size).toBe(0);
    expect(traceFrom(edges, "1", "none").nodeIds.size).toBe(0);
  });
});

describe("refereeDossier", () => {
  const index = indexDocument(TEST_DOCUMENT);
  const at = (id: string) => refereeDossier(TEST_DOCUMENT, index, index.nodeById.get(id)!);

  it("says what a step may assume, reads and establishes", () => {
    // Evenness is first tracked at 1 and again at 2, and declared an input of
    // the halving lemma by its requirement row.
    const start = at("1").state;
    expect(start.recorded).toBe(true);
    expect(start.before).toEqual([]);
    expect(start.establishes.map((invariant) => invariant.id)).toEqual(["one:1"]);

    const split = at("2").state;
    expect(split.before.map((invariant) => invariant.id)).toEqual(["one:1"]);
    expect(split.reads.map((invariant) => invariant.id)).toEqual(["one:1"]);
    expect(split.unavailable).toEqual([]);

    // Step 4 reads it through the same lemma, and it was tracked upstream.
    const onward = at("4").state;
    expect(onward.before.map((invariant) => invariant.id)).toEqual(["one:1"]);
    expect(onward.establishes).toEqual([]);
    expect(onward.unavailable).toEqual([]);
  });

  it("flags a constraint read where nothing upstream tracked it", () => {
    const document = {
      ...TEST_DOCUMENT,
      nodes: TEST_DOCUMENT.nodes.map((node) =>
        node.id === "1" || node.id === "2" ? { ...node, invariantRefs: [] } : node,
      ),
    };
    const dossier = refereeDossier(document, indexDocument(document), document.nodes[3]);
    expect(dossier.state.unavailable.map((invariant) => invariant.id)).toEqual(["one:1"]);
  });

  it("does not read the ledger's used-by column as an input", () => {
    // Without requirement rows the document declares no inputs, and the used-by
    // column — which names the results that introduce a constraint as readily
    // as those that rely on it — must not stand in for them.
    const document = {
      ...TEST_DOCUMENT,
      items: TEST_DOCUMENT.items.map((item) => ({ ...item, requires: undefined })),
    };
    const state = refereeDossier(document, indexDocument(document), document.nodes[1]).state;
    expect(state.recorded).toBe(false);
    expect(state.reads).toEqual([]);
    expect(state.unavailable).toEqual([]);
  });

  it("does not call a constraint unavailable when the ledger places it nowhere", () => {
    const document = {
      ...TEST_DOCUMENT,
      nodes: TEST_DOCUMENT.nodes.map((node) => ({ ...node, invariantRefs: [] })),
      invariants: TEST_DOCUMENT.invariants.map((invariant) => ({ ...invariant, nodes: [] })),
    };
    const state = refereeDossier(document, indexDocument(document), document.nodes[1]).state;
    expect(state.reads.map((invariant) => invariant.id)).toEqual(["one:1"]);
    expect(state.unavailable).toEqual([]);
  });

  it("reports a cited constraint the ledger does not list", () => {
    const document = {
      ...TEST_DOCUMENT,
      items: TEST_DOCUMENT.items.map((item) =>
        item.key === "lem:halving" ? { ...item, requires: "inv 1, 7" } : item,
      ),
    };
    const state = refereeDossier(document, indexDocument(document), document.nodes[1]).state;
    expect(state.reads.map((invariant) => invariant.id)).toEqual(["one:1"]);
    expect(state.dangling).toEqual([{ number: 7, items: ["lem:halving"] }]);
  });

  it("lists the cases of a branch test as drawn", () => {
    const { cases, checks } = at("2");
    expect(cases?.branches.map(({ edge, target }) => [edge.branch, target?.id])).toEqual([
      ["yes", "3"],
      ["no", "4"],
    ]);
    expect(cases?.unlabelled).toBe(0);
    expect(checks.find((check) => check.id === "branch")?.state).toBe("yes");
    expect(at("4").cases).toBeUndefined();
  });

  it("carries the closure of a leaf with its closing results", () => {
    const { closure, checks } = at("3");
    expect(closure?.dossier.closingResult).toBe("definition of an odd number");
    expect(closure?.closingItems.map((item) => item.key)).toEqual(["def:even"]);
    expect(checks.find((check) => check.id === "branch")?.state).toBe("yes");
    // The other leaf has no closure row, and the panel must say so rather than fail.
    expect(at("6").closure).toBeUndefined();
    expect(at("6").checks.find((check) => check.id === "branch")?.state).toBe("unrecorded");
  });

  it("reports a leaf the source leaves open as unclosed, not as unrecorded", () => {
    const document = {
      ...TEST_DOCUMENT,
      nodes: TEST_DOCUMENT.nodes.map((node) => (node.id === "6" ? { ...node, open: true } : node)),
    };
    const dossier = refereeDossier(document, indexDocument(document), document.nodes[5]);
    const branch = dossier.checks.find((check) => check.id === "branch");
    expect(branch?.state).toBe("no");
    expect(branch?.detail).toMatch(/open/);
  });

  it("measures what falls downstream", () => {
    const { impact } = at("2");
    expect(impact.downstreamCount).toBe(4);
    expect(impact.terminals.map((node) => node.id).sort()).toEqual(["3", "6"]);
    expect(impact.alsoUsedAt).toEqual(["4"]);
    expect(at("6").impact.downstreamCount).toBe(0);
  });

  it("names the results a step builds on, beyond its own", () => {
    expect(at("2").evidence.builds.map((item) => item.key)).toEqual(["def:even"]);
    expect(at("2").evidence.items.map((item) => item.key)).toEqual(["lem:halving"]);
  });

  it("reports the review dimensions the document does not record as such", () => {
    const checks = at("2").checks;
    const state = (id: string) => checks.find((check) => check.id === id)?.state;
    expect(state("manuscript")).toBe("yes");
    expect(state("dependencies")).toBe("yes");
    expect(state("located")).toBe("unrecorded"); // no page maps on the toy
    expect(state("lean")).toBe("unrecorded");
    expect(state("kernel")).toBe("unrecorded");
    expect(state("human")).toBe("unrecorded");
  });

  it("reads a review side-car when the host supplies one", () => {
    const document = {
      ...TEST_DOCUMENT,
      review: { nodes: { "2": { lean: "verified" as const, kernel: "partial" as const, human: "absent" as const } } },
    };
    const checks = refereeDossier(document, indexDocument(document), document.nodes[1]).checks;
    const state = (id: string) => checks.find((check) => check.id === id)?.state;
    expect(state("lean")).toBe("yes");
    expect(state("kernel")).toBe("partial");
    expect(state("human")).toBe("no");
    expect(state("wired")).toBe("unrecorded");
  });
});

describe("requiredInvariantNumbers", () => {
  it("reads the numbers a requirement names", () => {
    expect(requiredInvariantNumbers("inv 4, 8, 25; \\cref{lem:x}")).toEqual([4, 8, 25]);
    expect(requiredInvariantNumbers("invariants 20--24")).toEqual([20, 21, 22, 23, 24]);
    expect(requiredInvariantNumbers("inv. 3 and \\cref{lem:y}")).toEqual([3]);
    expect(requiredInvariantNumbers("def:even")).toEqual([]);
    expect(requiredInvariantNumbers(undefined)).toEqual([]);
  });
});

describe("search", () => {
  const index = indexDocument(TEST_DOCUMENT);
  const searchIndex = buildSearchIndex(TEST_DOCUMENT, index);

  it("finds a step by the title of a result behind it", () => {
    expect(matchNodes(searchIndex, "halving")).toEqual(new Set(["2", "4"]));
  });

  it("requires every term", () => {
    expect(matchNodes(searchIndex, "parity split")).toEqual(new Set(["2"]));
    expect(matchNodes(searchIndex, "parity conclusion").size).toBe(0);
  });

  it("treats an empty query as no filter", () => {
    expect(matchNodes(searchIndex, "   ").size).toBe(0);
  });
});

describe("layoutGraph", () => {
  it("ranks boxes and returns top-left positions", () => {
    const boxes = TEST_DOCUMENT.nodes.map((node) => ({ id: node.id, width: 200, height: 60 }));
    const positions = layoutGraph(boxes, TEST_DOCUMENT.edges);
    expect(positions.size).toBe(6);
    expect(positions.get("1")!.y).toBeLessThan(positions.get("2")!.y);
    expect(positions.get("2")!.y).toBeLessThan(positions.get("6")!.y);
  });

  it("ignores links whose endpoints are not laid out", () => {
    const positions = layoutGraph(
      [{ id: "1", width: 100, height: 40 }],
      [{ source: "1", target: "missing" }],
    );
    expect(positions.size).toBe(1);
  });
});

describe("buildGraph", () => {
  it("renders the whole document by default", () => {
    const { nodes, edges } = buildGraph(TEST_DOCUMENT);
    expect(nodes).toHaveLength(6);
    expect(edges).toHaveLength(5);
    expect(nodes.every((node) => node.type === "proof")).toBe(true);
  });

  it("restricts to one panel, dropping arrows that leave it", () => {
    const { nodes, edges } = buildGraph(TEST_DOCUMENT, { group: "part-b" });
    expect(nodes.map((node) => node.id)).toEqual(["5", "6"]);
    expect(edges.map((edge) => edge.id)).toEqual(["e5"]);
  });

  it("dims what the trace does not reach", () => {
    const trace = traceFrom(TEST_DOCUMENT.edges, "5", "downstream");
    const { nodes } = buildGraph(TEST_DOCUMENT, {
      selectedId: "5",
      tracedNodeIds: trace.nodeIds,
      tracedEdgeIds: trace.edgeIds,
    });
    const byId = new Map(nodes.map((node) => [node.id, node.data]));
    expect(byId.get("6")!.dimmed).toBe(false);
    expect(byId.get("1")!.dimmed).toBe(true);
    expect(byId.get("5")!.selected).toBe(true);
  });

  it("marks continuation arrows so they can be drawn differently", () => {
    const { edges } = buildGraph(TEST_DOCUMENT);
    const continuation = edges.find((edge) => edge.id === "e4")!;
    expect(continuation.className).toContain("proof-edge-continuation");
    expect(continuation.label).toBe("continues");
  });

  it("sets verified from the review sidecar", () => {
    const withReview = {
      ...TEST_DOCUMENT,
      // The badge needs both gates: a finished producer that publishes the
      // manuscript's statement. "Compiles" alone is not a verification claim.
      review: { nodes: { "2": { kernel: "verified" as const, fidelity: "verified" as const } } },
    };
    const { nodes } = buildGraph(withReview);
    const byId = new Map(nodes.map((n) => [n.id, n.data]));
    expect(byId.get("2")!.verified).toBe(true);
    expect(byId.get("1")!.verified).toBe(false);
  });
});

describe("parseLatex", () => {
  it("separates prose from inline maths", () => {
    expect(parseLatex("is $n/2$ odd?")).toEqual([
      { kind: "text", value: "is " },
      { kind: "math", value: "n/2", display: false },
      { kind: "text", value: " odd?" },
    ]);
  });

  it("recognises display maths in both spellings", () => {
    expect(parseLatex("\\[ 4 \\mid n \\]")).toEqual([
      { kind: "math", value: " 4 \\mid n ", display: true },
    ]);
    const environment = parseLatex("\\begin{equation}x=1\\end{equation}");
    expect(environment).toEqual([{ kind: "math", value: "x=1", display: true }]);
  });

  it("keeps \\( \\) maths out of the prose", () => {
    const segments = parseLatex("net charge \\(\\No(X)<0\\)");
    expect(segments[1]).toEqual({ kind: "math", value: "\\No(X)<0", display: false });
  });

  it("turns line breaks into break segments", () => {
    const segments = parseLatex("target cycle\\\\continued");
    expect(segments.map((segment) => segment.kind)).toEqual(["text", "break", "text"]);
  });

  it("keeps list structure as list and item segments", () => {
    const source =
      "Either:\n\\begin{enumerate}[label=(\\alph*)]\n\\item a cycle in the sense of \\cref{lem:a};\n\n\\item[(F5)] a quotient $q$.\n\\end{enumerate}\n";
    expect(parseLatex(source)).toEqual([
      { kind: "text", value: "Either:" },
      { kind: "list", ordered: true, open: true },
      { kind: "item" },
      { kind: "text", value: "a cycle in the sense of " },
      { kind: "ref", key: "lem:a" },
      { kind: "text", value: ";" },
      { kind: "item", label: "(F5)" },
      { kind: "text", value: "a quotient " },
      { kind: "math", value: "q", display: false },
      { kind: "text", value: "." },
      { kind: "list", ordered: true, open: false },
    ]);
    expect(parseLatex("\\begin{itemize}\\item x\\end{itemize}")[0]).toEqual({
      kind: "list",
      ordered: false,
      open: true,
    });
  });

  it("separates the keys of a multi-target reference and brackets citations", () => {
    expect(parseLatex("by \\cref{lem:a,cor:b,lem:c} and \\cite{HSS2024}.")).toEqual([
      { kind: "text", value: "by " },
      { kind: "ref", key: "lem:a" },
      { kind: "text", value: ", " },
      { kind: "ref", key: "cor:b" },
      { kind: "text", value: " and " },
      { kind: "ref", key: "lem:c" },
      { kind: "text", value: " and [HSS2024]." },
    ]);
  });

  it("unwraps text-only formatting", () => {
    expect(parseLatex("\\emph{target-safe} paths")).toEqual([
      { kind: "text", value: "target-safe paths" },
    ]);
  });

  it("keeps the text of a coloured span and drops the colour", () => {
    expect(parseLatex("configuration; \\textcolor{red}{open node [163]}")).toEqual([
      { kind: "text", value: "configuration; open node [163]" },
    ]);
    expect(parseLatex("\\textcolor{red}{[163] \\texttt{(neutral)}}", { nodes: true })).toEqual([
      { kind: "node", id: "163" },
      { kind: "text", value: " (neutral)" },
    ]);
  });

  it("exposes cross-references as their own segments", () => {
    const segments = parseLatex("see \\cref{lem:halving,def:even} above");
    expect(segments.filter((segment) => segment.kind === "ref")).toEqual([
      { kind: "ref", key: "lem:halving" },
      { kind: "ref", key: "def:even" },
    ]);
  });

  it("flattens to plain text for measuring and labelling", () => {
    expect(latexToPlainText("is $n/2$ odd?")).toBe("is n/2 odd?");
    expect(latexToPlainText("")).toBe("");
  });
});

describe("maths after a line break", () => {
  it("is still recognised (the \\\\ is not an escaped dollar)", () => {
    const segments = parseLatex("visible-first excess:\\\\$S^{exc}(X)\\ge4D(X)$");
    expect(segments.map((segment) => segment.kind)).toEqual(["text", "break", "math"]);
    expect(segments[2]).toEqual({
      kind: "math",
      value: "S^{exc}(X)\\ge4D(X)",
      display: false,
    });
  });

  it("still treats a genuinely escaped dollar as text", () => {
    expect(parseLatex("costs \\$5")).toEqual([{ kind: "text", value: "costs \\$5" }]);
  });
});

describe("clampDetailWidth", () => {
  it("leaves a dragged width alone when it fits", () => {
    expect(clampDetailWidth(420, 1400)).toBe(420);
    expect(clampDetailWidth(755.4, 1400)).toBe(755);
  });

  it("never lets the column become unreadable", () => {
    expect(clampDetailWidth(80, 1400)).toBe(300);
    expect(clampDetailWidth(-500, 1400)).toBe(300);
  });

  it("always leaves room for the diagram", () => {
    expect(clampDetailWidth(9999, 1400)).toBe(1080);
  });

  it("prefers a readable column when the window is too small for both", () => {
    expect(clampDetailWidth(9999, 500)).toBe(300);
  });
});

describe("references to numbered displays", () => {
  it("reads \\eqref and \\ref, not only \\cref", () => {
    for (const source of [
      "the bound \\eqref{eq:halving} holds",
      "the bound \\ref{eq:halving} holds",
      "the bound \\cref{eq:halving} holds",
      "the bound \\Cref{eq:halving} holds",
    ]) {
      expect(parseLatex(source)).toContainEqual({ kind: "ref", key: "eq:halving" });
    }
  });

  it("keeps the sentence around the reference intact", () => {
    expect(parseLatex("assume \\eqref{eq:halving} at $z_*$.")).toEqual([
      { kind: "text", value: "assume " },
      { kind: "ref", key: "eq:halving" },
      { kind: "text", value: " at " },
      { kind: "math", value: "z_*", display: false },
      { kind: "text", value: "." },
    ]);
  });
});

describe("indexDocument equations", () => {
  it("indexes the displays a reference can point at", () => {
    const index = indexDocument(TEST_DOCUMENT);
    expect(index.equationByKey.get("eq:halving")?.latex).toBe("n = 2m");
  });
});

describe("a reference wrapped in maths delimiters", () => {
  it("is read as a reference, not handed to the maths renderer", () => {
    expect(parseLatex("as in \\(\\cref{lem:halving}\\), we halve")).toEqual([
      { kind: "text", value: "as in " },
      { kind: "ref", key: "lem:halving" },
      { kind: "text", value: ", we halve" },
    ]);
  });

  it("leaves real mathematics alone", () => {
    expect(parseLatex("\\(n/2\\)")).toEqual([
      { kind: "math", value: "n/2", display: false },
    ]);
  });
});

describe("tracing a diagram with a loop in it", () => {
  // 1 -> 2 -> 3 -> 2 : step 3 recomputes and re-enters at 2.
  const LOOPED = [
    { id: "a", source: "1", target: "2", branch: null, kind: "flow" as const },
    { id: "b", source: "2", target: "3", branch: null, kind: "flow" as const },
    { id: "c", source: "3", target: "2", branch: "recompute", kind: "flow" as const },
  ];

  it("still reaches what led to a step found downstream", () => {
    const trace = traceFrom(LOOPED, "2", "both");
    expect([...trace.nodeIds].sort()).toEqual(["1", "2", "3"]);
    expect(trace.edgeIds.size).toBe(3);
  });

  it("terminates rather than following the loop forever", () => {
    expect(traceFrom(LOOPED, "1", "downstream").nodeIds.size).toBe(3);
    expect(traceFrom(LOOPED, "3", "upstream").nodeIds.size).toBe(3);
  });
});

describe("bracketed step numbers", () => {
  it("are read as steps only when asked for", () => {
    const source = "the split at [22] closes";
    expect(parseLatex(source)).toEqual([{ kind: "text", value: "the split at [22] closes" }]);
    expect(parseLatex(source, { nodes: true })).toEqual([
      { kind: "text", value: "the split at " },
      { kind: "node", id: "22" },
      { kind: "text", value: " closes" },
    ]);
  });

  it("leave a statement alone, where a bracket may mean anything", () => {
    const item = TEST_DOCUMENT.items.find((entry) => entry.key === "def:even")!;
    for (const segment of parseLatex(item.statementLatex)) {
      expect(segment.kind).not.toBe("node");
    }
  });

  it("survive a flatten as the paper wrote them", () => {
    expect(latexToPlainText("see [22]")).toBe("see [22]");
  });
});
