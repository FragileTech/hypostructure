import { describe, expect, it } from "vitest";

import {
  autorouteRecordId,
  buildAutorouteGraph,
  buildDagGraph,
  entitySearchText,
  traceSelection,
} from "./erdos-graph";
import {
  syntheticAutoroute as autoroute,
  syntheticCertifiedProofRun as run,
} from "./test-proof-run";
import type { HypostructureProofRun } from "./proof-run-types";

describe("proof graph reconstruction", () => {
  it("renders resolved semantic autoroutes without named blocks", () => {
    const graph = buildAutorouteGraph(run);
    expect(graph.nodes.map((node) => node.id)).toEqual(["v0", "v1"]);
    expect(graph.edges).toHaveLength(1);
    expect(graph.edges[0]).toMatchObject({
      source: "v0",
      target: "v1",
      label: "Synthetic literal transport",
      data: { entity: `autoroute:${autorouteRecordId(autoroute, 0)}` },
    });
    expect(graph.nodes.find((node) => node.id === "v0")?.data.depth).toBe(1);
    expect(graph.nodes.find((node) => node.id === "v1")?.data.depth).toBe(8);
    expect(graph.nodes.every((node) => Number.isFinite(node.position.x))).toBe(true);
  });

  it("adds semantic autoroutes to the normalized DAG", () => {
    const graph = buildDagGraph(run);
    expect(graph.nodes).toHaveLength(
      run.dag.nodes.length + run.dag.terminals.length,
    );
    expect(graph.edges).toHaveLength(
      run.dag.edges.length,
    );
    expect(graph.nodes.find((node) => node.id === run.dag.entry)?.data.entry).toBe(true);
    expect(graph.nodes.find((node) => node.id === "t0")?.data.kind).toBe("terminal-closed");
    expect(run.dag.terminals).not.toHaveLength(0);
    expect(run.dag.terminals.some((terminal) => terminal.status === "closed")).toBe(true);
    expect(run.dag.terminals.some((terminal) => terminal.status === "open")).toBe(true);
    expect(run.dag.terminals.some(
      (terminal) => terminal.residual.disposition === "open",
    )).toBe(true);
  });

  it("marks decision strategies as dichotomy-shaped graph nodes", () => {
    const decisionRun: HypostructureProofRun = structuredClone(run);
    const decision = decisionRun.dag.nodes.find((node) => node.id === "v0");
    if (!decision || decision.kind === "join") {
      throw new Error("synthetic decision fixture is missing");
    }
    decision.kind = "decision";
    decision.strategy.kind = "finite_density_budget";

    const graph = buildDagGraph(decisionRun);
    const rendered = graph.nodes.find((node) => node.id === decision.id);
    expect(rendered?.data.kind).toBe("decision");
    expect(rendered?.position.y).not.toBeNaN();
  });

  it("recognizes named dichotomies in older proof-run exports", () => {
    const legacyRun: HypostructureProofRun = structuredClone(run);
    const decision = legacyRun.dag.nodes.find((node) => node.id === "v0");
    if (!decision || decision.kind === "join") {
      throw new Error("synthetic decision fixture is missing");
    }
    decision.kind = "operation";
    decision.strategy.kind = "scale_threshold_dichotomy";

    const graph = buildDagGraph(legacyRun);
    expect(graph.nodes.find((node) => node.id === decision.id)?.data.kind).toBe(
      "decision",
    );
  });

  it("indexes every semantic selection and bridge-provenance field", () => {
    const text = entitySearchText(
      run,
      `autoroute:${autorouteRecordId(autoroute, 0)}`,
    );
    expect(text).toContain("v0");
    expect(text).toContain("v1");
    expect(text).toContain("literal_residual");
    expect(text).toContain("Synthetic literal transport");
    expect(text).toContain("Cosmetic route commentary retained in the JSON fixture.");
    expect(text).toContain("autoroute");
    expect(text).toContain("deepest_most_restrictive");
    expect(text).toContain("smallest_stable_structural_id");
    expect(text).toContain("BridgeCertificate.residual_eq");
    expect(text).toContain("literal_residual_identity");
    expect(text).toContain("nearest_enclosing_continuation_entry");
    expect(text).toContain("literal_predecessor_stage");
    expect(text).toContain("Hypostructure.Core.Residual.Ledger.extend_previous");
    expect(text).toContain("Hypostructure.Core.Residual.Ledger.Extension");
    expect(text).toContain("1");
    expect(text).toContain("true");
  });

  it("keeps node and registration metadata searchable", () => {
    expect(entitySearchText(run, "node:v0")).toContain("certificate decision");
    expect(entitySearchText(run, "node:v0")).toContain("rooted-return validation");
    expect(entitySearchText(run, "node:v0")).toMatch(/\b0\b/);
    expect(entitySearchText(run, "registration:ordered_witness_scan:0")).toContain("schedule");
  });

  it("is explicit synthetic certified reduction data with a retained residual", () => {
    expect(run.schema_version).toBe("2.3.0");
    expect(run.problem.presentation.tags).toContain("synthetic");
    expect(run.run.kind).toBe("certified_reduction");
    expect(run.run.certified).toBe(true);
    expect(run.trust.kernel_checked).toBe(true);
    expect(run.execution.result).toBe("reduced");
    expect(run.execution.statement_ref).toBe("execution.target_or_residual");
    expect(run.execution.residual_disposition).toBe("retained");
    expect(run.strategy_registrations.some(
      (registration) => registration.kind === "finite_density_budget",
    )).toBe(true);
  });

  it("traces through resolved semantic autoroute edges", () => {
    const downstream = traceSelection(run, "v0", "downstream");
    expect(downstream.vertexIds.has("v1")).toBe(true);
    expect(
      downstream.edgeIds.has(`autoroute-edge:${autorouteRecordId(autoroute, 0)}`),
    ).toBe(true);

    const both = traceSelection(run, "v1", "both");
    const upstream = traceSelection(run, "v1", "upstream");
    expect(both.vertexIds).toEqual(
      new Set([
        ...upstream.vertexIds,
        ...traceSelection(run, "v1", "downstream").vertexIds,
      ]),
    );
  });
});
