import { describe, expect, it } from "vitest";

import { buildGraph } from "./buildGraph";
import { indexDocument } from "./index-document";
import { latexToPlainText, parseLatex } from "./latex";
import { layoutGraph } from "./layout";
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

  it("unwraps text-only formatting", () => {
    expect(parseLatex("\\emph{dyadic-safe} paths")).toEqual([
      { kind: "text", value: "dyadic-safe paths" },
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
