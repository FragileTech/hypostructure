import { useCallback, useEffect, useMemo, useRef } from "react";
import { Link, useSearchParams } from "react-router-dom";
import {
  Background,
  Controls,
  Handle,
  MiniMap,
  Position,
  ReactFlow,
  type Edge,
  type NodeProps,
  type NodeTypes,
  type ReactFlowInstance,
} from "@xyflow/react";
import "@xyflow/react/dist/style.css";

import { fetchExamplePage, fetchProofRun } from "../api";
import {
  buildAutorouteGraph,
  buildDagGraph,
  entitySearchText,
  findAutoroute,
  isDichotomyNode,
  traceSelection,
  type ProofGraphNode,
  type TraceDirection,
} from "../erdos-graph";
import { useApiResource } from "../hooks/useApiResource";
import { useDocumentMetadata } from "../hooks/useDocumentMetadata";
import type {
  HypostructureProofRun,
  StrategyRegistration,
} from "../proof-run-types";
import { ContentBlocks } from "../components/ContentBlocks";

type ExplorerView = "autoroutes" | "dag";

function ProofNode({ data, selected }: NodeProps<ProofGraphNode>) {
  return (
    <div
      className={[
        "proof-graph-node",
        `proof-graph-node-${data.kind}`,
        data.entry ? "is-entry" : "",
        selected ? "is-selected" : "",
        data.traced ? "is-traced" : "",
        data.dimmed ? "is-dimmed" : "",
      ].filter(Boolean).join(" ")}
    >
      <Handle type="target" position={Position.Top} />
      <span className="proof-graph-node-surface" aria-hidden="true" />
      <span className="proof-graph-node-content">
        <span>{data.kind.replaceAll("-", " ")}</span>
        <strong>{data.label}</strong>
        <small>{data.subtitle}</small>
      </span>
      {data.entry ? <span className="proof-graph-entry">Entry</span> : null}
      <Handle type="source" position={Position.Bottom} />
    </div>
  );
}

const nodeTypes: NodeTypes = { proof: ProofNode };

function RequestFailure({ error }: { error: Error }) {
  return (
    <section className="request-state request-error" role="alert">
      <span aria-hidden="true">!</span>
      <h1>We could not load the proof run</h1>
      <p>{error.message}</p>
      <button type="button" onClick={() => window.location.reload()}>Try again</button>
      <Link to="/examples">Return to examples</Link>
    </section>
  );
}

function Value({ value }: { value: string | number | boolean | null | undefined }) {
  if (value === null || value === undefined || value === "") return <span className="empty-value">Not supplied</span>;
  return <>{typeof value === "boolean" ? (value ? "Yes" : "No") : value}</>;
}

function DetailGrid({
  items,
}: {
  items: Array<[string, string | number | boolean | null | undefined]>;
}) {
  return (
    <dl className="proof-detail-grid">
      {items.map(([label, value]) => (
        <div key={label}>
          <dt>{label}</dt>
          <dd><Value value={value} /></dd>
        </div>
      ))}
    </dl>
  );
}

function registrationSummary(registration: StrategyRegistration) {
  return registration.presentation.label
    ?? `${registration.kind.replaceAll("_", " ")} #${registration.index}`;
}

function entityRecord(run: HypostructureProofRun, entity: string | null): {
  title: string;
  eyebrow: string;
  value: unknown;
  details: Array<[string, string | number | boolean | null | undefined]>;
} | null {
  if (!entity) return null;
  const separator = entity.indexOf(":");
  if (separator < 0) return null;
  const kind = entity.slice(0, separator);
  const id = entity.slice(separator + 1);
  if (kind === "autoroute") {
    const value = findAutoroute(run, id);
    return value ? {
      title: value.presentation.label
        ?? `${value.source_id} → ${value.destination_id}`,
      eyebrow: "Resolved semantic autoroute",
      value,
      details: [
        ["Source node", value.source_id],
        ["Source depth", value.source_depth],
        ["Destination node", value.destination_id],
        ["Destination depth", value.destination_depth],
        ["Name", value.presentation.label],
        ["Note", value.presentation.note],
        ["Tags", value.presentation.tags.join(", ")],
        ["Relation", value.relation],
        [
          "Compatible candidates",
          value.compatible_candidates.map((candidate) =>
            `${candidate.node_id} (depth ${candidate.depth}, ${candidate.relation})`
          ).join(", "),
        ],
        ["Selection", value.selection.rule],
        ["Selected candidate", value.selection.selected_candidate_id],
        ["Tie-break", value.selection.tie_break],
        ["Relation witness", value.bridge_provenance.relation_witness],
        ["Target congruence", value.bridge_provenance.target_congruence],
        [
          "Destination requirements",
          value.bridge_provenance.destination_requirements.join(", "),
        ],
        ["Ledger ancestors", value.bridge_provenance.ledger_ancestors.join(", ")],
        ["Framework lemmas", value.bridge_provenance.framework_lemmas.join(", ")],
        ["Ledger extension", value.bridge_provenance.ledger_extension],
        ["Work", value.work],
        ["Acyclic", value.acyclic],
      ],
    } : null;
  }
  if (kind === "node") {
    const value = run.dag.nodes.find((item) => item.id === id);
    if (!value) return null;
    const isJoin = value.kind === "join";
    return {
      title: isJoin
        ? value.presentation.label ?? value.id
        : value.presentation.resolved.label ?? value.id,
      eyebrow: `${value.kind} node`,
      value,
      details: isJoin ? [
        ["ID", value.id],
        ["Integer ID", value.internal_id],
        ["Status", value.status],
        ["Label", value.presentation.label],
        ["Note", value.presentation.note],
      ] : [
        ["ID", value.id],
        ["Integer ID", value.internal_id],
        ["Status", value.status],
        ["Strategy", value.strategy.kind],
        ["Strategy index", value.strategy.index],
        ["Registration", value.strategy.registration_id],
        ["Resolved label", value.presentation.resolved.label],
        ["Resolved note", value.presentation.resolved.note],
        ["Authored label", value.presentation.authored.label],
        ["Authored note", value.presentation.authored.note],
        ["Registered label", value.presentation.registered.label],
        ["Registered note", value.presentation.registered.note],
        ["Registered tags", value.presentation.registered.tags.join(", ")],
        ["Components", value.components.length],
      ],
    };
  }
  if (kind === "terminal") {
    const value = run.dag.terminals.find((item) => item.id === id);
    return value ? {
      title: `${value.id} · ${value.status} terminal`,
      eyebrow: value.kind.replaceAll("_", " "),
      value,
      details: [
        ["ID", value.id],
        ["Integer ID", value.internal_id],
        ["Status", value.status],
        ["Reason", value.reason],
        ["Residual kind", value.residual.kind],
        ["Disposition", value.residual.disposition],
        ["Baseline", value.residual.baseline_ref],
        ["Path representation", value.residual.constraints.representation],
      ],
    } : null;
  }
  if (kind === "edge") {
    const value = run.dag.edges.find((item) => item.id === id);
    return value ? {
      title: value.presentation.label ?? value.output ?? value.id,
      eyebrow: `${value.kind} edge`,
      value,
      details: [
        ["ID", value.id],
        ["Integer ID", value.internal_id],
        ["From", value.source],
        ["To", value.target],
        ["Output", value.output],
        ["Status", value.status],
        ["Label", value.presentation.label],
        ["Note", value.presentation.note],
      ],
    } : null;
  }
  if (kind === "registration") {
    const value = run.strategy_registrations.find((item) => item.id === id);
    return value ? {
      title: registrationSummary(value),
      eyebrow: "Strategy registration",
      value,
      details: [
        ["ID", value.id],
        ["Integer index", value.index],
        ["Kind", value.kind],
        ["Label", value.presentation.label],
        ["Note", value.presentation.note],
        ["Tags", value.presentation.tags.join(", ")],
        ["Contract fields", value.interface.map((item) => item.name).join(", ")],
        ["Components", value.components.length],
        ["Outputs", value.outputs.map((item) => item.port).join(", ")],
        ["Closes target", value.closures?.target],
        ["Closes residual", value.closures?.residual],
      ],
    } : null;
  }
  return null;
}

function EntityInspector({
  run,
  entity,
}: {
  run: HypostructureProofRun;
  entity: string | null;
}) {
  const record = entityRecord(run, entity);
  if (!record) {
    return (
      <aside className="proof-inspector proof-inspector-empty">
        <span className="section-eyebrow">Inspector</span>
        <h2>Select part of the proof</h2>
        <p>Choose a semantic autoroute, strategy node, edge, terminal, or registration to inspect every exported field.</p>
      </aside>
    );
  }
  return (
    <aside className="proof-inspector" aria-live="polite">
      <span className="section-eyebrow">{record.eyebrow}</span>
      <h2>{record.title}</h2>
      <DetailGrid items={record.details} />
      <details className="proof-json-details">
        <summary>Structured JSON</summary>
        <pre><code>{JSON.stringify(record.value, null, 2)}</code></pre>
      </details>
    </aside>
  );
}

function FormalDefinition({ run }: { run: HypostructureProofRun }) {
  return (
    <section className="proof-panel" id="definition">
      <div className="proof-panel-heading">
        <div>
          <p className="section-eyebrow">Problem definition</p>
          <h2>What the DAG is proving</h2>
        </div>
        <code>{run.problem.identity.definition_ref}</code>
      </div>
      <DetailGrid items={[
        ["Problem ID", run.problem.id],
        ["Module", run.problem.identity.module],
        ["Source expression", run.problem.identity.source_expression],
        ["Label", run.problem.presentation.label],
        ["Note", run.problem.presentation.note],
        ["Tags", run.problem.presentation.tags.join(", ")],
        ["Authored signature", run.problem.presentation.authored_signature],
        ["Authored statement", run.problem.presentation.authored_statement],
      ]} />
      <div className="formal-reference-grid">
        {Object.entries(run.problem.formal).map(([name, reference]) => (
          <article key={name}>
            <h3>{name.replaceAll("_", " ")}</h3>
            <code>{reference.rendering}</code>
            <small>{reference.declaration_ref}</small>
          </article>
        ))}
      </div>
    </section>
  );
}

function Outcome({ run }: { run: HypostructureProofRun }) {
  const closed = run.dag.terminals.filter((terminal) => terminal.status === "closed").length;
  const open = run.dag.terminals.length - closed;
  return (
    <section className="proof-panel" id="outcome">
      <div className="proof-panel-heading">
        <div>
          <p className="section-eyebrow">Execution outcome</p>
          <h2>Kernel-certified reduction</h2>
        </div>
        <span className="proof-status is-certified">Certified</span>
      </div>
      <p className="proof-trust-note">{run.trust.verification_note}</p>
      <DetailGrid items={[
        ["Run", run.run.name],
        ["Kind", run.run.kind],
        ["Certified", run.run.certified],
        ["Kernel checked", run.trust.kernel_checked],
        ["Result", run.execution.result],
        ["Residual disposition", run.execution.residual_disposition],
        ["Checks bound", run.execution.checks_bound],
        ["Work bound", run.execution.work_bound],
        ["Open terminals", open],
        ["Closed terminals", closed],
        ["Retained residuals", run.dag.terminals.filter(
          (terminal) => terminal.residual.disposition === "open",
        ).length],
        ["Proof term exported", run.trust.proof_term_exported],
      ]} />
    </section>
  );
}

function Explorer({
  run,
  view,
  selected,
  traceDirection,
  query,
  kindFilter,
  registrationFilter,
  statusFilter,
  updateParameter,
  updateParameters,
}: {
  run: HypostructureProofRun;
  view: ExplorerView;
  selected: string | null;
  traceDirection: TraceDirection;
  query: string;
  kindFilter: string;
  registrationFilter: string;
  statusFilter: string;
  updateParameter: (name: string, value: string, replace?: boolean) => void;
  updateParameters: (
    values: Record<string, string | null>,
    replace?: boolean,
  ) => void;
}) {
  const flowRef = useRef<ReactFlowInstance<ProofGraphNode, Edge> | null>(null);
  const graph = useMemo(
    () => (view === "autoroutes" ? buildAutorouteGraph(run) : buildDagGraph(run)),
    [run, view],
  );
  const selectedVertexId = selected?.startsWith("node:")
    ? selected.slice("node:".length)
    : selected?.startsWith("terminal:")
      ? selected.slice("terminal:".length)
      : null;
  const trace = useMemo(
    () => traceSelection(run, selectedVertexId, traceDirection),
    [run, selectedVertexId, traceDirection],
  );
  const normalizedQuery = query.trim().toLocaleLowerCase();
  const strategyKinds = useMemo(
    () => [...new Set(run.strategy_registrations.map(({ kind }) => kind))],
    [run.strategy_registrations],
  );
  const matches = useCallback((entity: string) => {
    const text = entitySearchText(run, entity).toLocaleLowerCase();
    if (normalizedQuery && !text.includes(normalizedQuery)) return false;
    if (!kindFilter && !registrationFilter && !statusFilter) return true;
    if (entity.startsWith("node:")) {
      const id = entity.slice("node:".length);
      const node = run.dag.nodes.find((item) => item.id === id);
      if (!node || node.kind === "join") return false;
      if (kindFilter && node.strategy.kind !== kindFilter) return false;
      if (registrationFilter && node.strategy.registration_id !== registrationFilter) return false;
      if (statusFilter && node.status !== statusFilter) return false;
      return true;
    }
    if (entity.startsWith("terminal:")) {
      const terminal = run.dag.terminals.find(
        (item) => item.id === entity.slice("terminal:".length),
      );
      return Boolean(
        terminal
        && !kindFilter
        && !registrationFilter
        && (!statusFilter || terminal.status === statusFilter),
      );
    }
    if (entity.startsWith("edge:")) {
      const edge = run.dag.edges.find(
        (item) => item.id === entity.slice("edge:".length),
      );
      return Boolean(
        edge
        && !kindFilter
        && !registrationFilter
        && (!statusFilter || edge.status === statusFilter),
      );
    }
    if (entity.startsWith("autoroute:")) {
      return !kindFilter && !registrationFilter && !statusFilter;
    }
    return !kindFilter && !registrationFilter && !statusFilter;
  }, [kindFilter, normalizedQuery, registrationFilter, run, statusFilter]);
  const graphNodes = useMemo(
    () => graph.nodes.map((node) => {
      const traceActive = view === "dag" && selectedVertexId !== null;
      const traced = trace.vertexIds.has(node.id);
      return {
        ...node,
        selected: node.data.entity === selected,
        data: {
          ...node.data,
          traced,
          dimmed: !matches(node.data.entity)
            || (traceActive && !traced),
        },
      };
    }),
    [
      graph.nodes,
      matches,
      selected,
      selectedVertexId,
      trace.vertexIds,
      view,
    ],
  );
  const nodeById = new Map(graphNodes.map((node) => [node.id, node]));
  const graphEdges: Edge[] = graph.edges.map((edge) => {
    const entity = String(edge.data?.entity ?? (view === "dag" ? `edge:${edge.id}` : edge.id));
    const dimmed = !matches(entity)
      && Boolean(nodeById.get(edge.source)?.data.dimmed)
      && Boolean(nodeById.get(edge.target)?.data.dimmed);
    const traceActive = view === "dag" && selectedVertexId !== null;
    const traced = trace.edgeIds.has(edge.id);
    return {
      ...edge,
      selected: entity === selected,
      animated: traced,
      className: [
        edge.className,
        traced ? "is-traced" : "",
      ].filter(Boolean).join(" "),
      style: {
        ...edge.style,
        opacity: dimmed
          || (traceActive && !traced)
          ? 0.1
          : 1,
      },
    };
  });
  useEffect(() => {
    if (view !== "dag" || !flowRef.current) return;
    const targetIds = selectedVertexId ? trace.vertexIds : null;
    if (!targetIds?.size) return;
    const targets = graphNodes.filter((node) => targetIds.has(node.id));
    const frame = window.requestAnimationFrame(() => {
      void flowRef.current?.fitView({
        nodes: targets,
        padding: 0.28,
        duration: 500,
        maxZoom: 0.72,
      });
    });
    return () => window.cancelAnimationFrame(frame);
  }, [
    graphNodes,
    selectedVertexId,
    trace.vertexIds,
    view,
  ]);
  const accessibleEntities = [
    ...graphNodes.map((node) => ({
      entity: node.data.entity,
      label: node.data.label,
      detail: node.data.subtitle,
      dimmed: node.data.dimmed,
    })),
    ...graphEdges.map((edge) => {
      const entity = String(edge.data?.entity ?? (view === "dag" ? `edge:${edge.id}` : edge.id));
      return {
        entity,
        label: String(edge.label ?? edge.id),
        detail: `${edge.source} → ${edge.target}`,
        dimmed: !matches(entity),
      };
    }),
  ];

  return (
    <section className="proof-explorer" id="explorer">
      <div className="proof-explorer-heading">
        <div>
          <p className="section-eyebrow">Interactive reconstruction</p>
          <h2>{view === "autoroutes" ? "Resolved semantic autoroutes" : "Normalized strategy DAG"}</h2>
          <p>
            {view === "autoroutes"
              ? "Inspect Core-selected destinations, candidate ordering, bridge provenance, work, and acyclicity."
              : "Inspect every exported strategy vertex, branch edge, semantic autoroute, join, and terminal."}
          </p>
        </div>
        {run.dag.autoroutes.length > 0 ? (
        <div className="view-switcher" role="group" aria-label="Proof representation">
          <button
            className={view === "autoroutes" ? "active" : ""}
            type="button"
            onClick={() => updateParameters({
              view: "autoroutes",
              selected: null,
              trace: null,
            })}
          >Semantic routes</button>
          <button
            className={view === "dag" ? "active" : ""}
            type="button"
            onClick={() => updateParameters({ view: "dag", selected: null })}
          >Full DAG</button>
        </div>
        ) : null}
      </div>
      {view === "dag" && selectedVertexId ? (
        <div className="proof-trace-toolbar" role="group" aria-label="Path tracing direction">
          <span>Trace selected strategy</span>
          {(["upstream", "downstream", "both"] as TraceDirection[]).map((direction) => (
            <button
              className={traceDirection === direction ? "active" : ""}
              type="button"
              key={direction}
              onClick={() => updateParameter("trace", direction)}
            >{direction}</button>
          ))}
          <button
            type="button"
            onClick={() => updateParameters({ selected: null, trace: null })}
          >Clear trace</button>
        </div>
      ) : null}
      <div className="proof-filter-bar">
        <label>
          <span>Search exported fields</span>
          <input
            type="search"
            value={query}
            placeholder="Label, note, ID, tag…"
            onChange={(event) => updateParameter("q", event.target.value, true)}
          />
        </label>
        <label>
          <span>Strategy kind</span>
          <select
            value={kindFilter}
            onChange={(event) => updateParameter("kind", event.target.value)}
          >
            <option value="">All kinds</option>
            {strategyKinds.map((kind) => (
              <option key={kind} value={kind}>{kind.replaceAll("_", " ")}</option>
            ))}
          </select>
        </label>
        <label>
          <span>Registration</span>
          <select
            value={registrationFilter}
            onChange={(event) => updateParameter("registration", event.target.value)}
          >
            <option value="">All registrations</option>
            {run.strategy_registrations.map((registration) => (
              <option key={registration.id} value={registration.id}>{registration.id}</option>
            ))}
          </select>
        </label>
        <label>
          <span>Status</span>
          <select
            value={statusFilter}
            onChange={(event) => updateParameter("status", event.target.value)}
          >
            <option value="">All statuses</option>
            {["active", "certified", "conditional", "open", "closed"].map((status) => (
              <option key={status} value={status}>{status}</option>
            ))}
          </select>
        </label>
      </div>
      <div className="proof-shape-key" aria-label="Proof graph shape key">
        <span><i className="is-operation" aria-hidden="true" /> Strategy step</span>
        <span><i className="is-dichotomy" aria-hidden="true" /> Dichotomy</span>
        <span><i className="is-terminal" aria-hidden="true" /> Terminal</span>
      </div>
      <div className="proof-workbench">
        <div className="proof-canvas" aria-label={`${view === "autoroutes" ? "Semantic autoroute" : "Normalized DAG"} visualization`}>
          <ReactFlow<ProofGraphNode, Edge>
            nodes={graphNodes}
            edges={graphEdges}
            nodeTypes={nodeTypes}
            fitView
            fitViewOptions={{ padding: 0.18 }}
            minZoom={0.12}
            maxZoom={1.8}
            nodesDraggable={false}
            nodesConnectable={false}
            elementsSelectable
            onInit={(instance) => { flowRef.current = instance; }}
            onNodeClick={(_event, node) => {
              if (view === "autoroutes") {
                updateParameters({
                  view: "dag",
                  selected: node.data.entity,
                  trace: "both",
                });
              } else {
                updateParameters({
                  selected: node.data.entity,
                  trace: "both",
                });
              }
            }}
            onEdgeClick={(_event, edge) => {
              const entity = String(edge.data?.entity ?? (view === "dag" ? `edge:${edge.id}` : edge.id));
              updateParameter("selected", entity);
            }}
          >
            <Background gap={24} size={1} color="#b9c5bf" />
            <MiniMap
              pannable
              zoomable
              nodeColor={(node) => {
                const kind = node.data?.kind?.toString() ?? "";
                if (kind === "decision") return "#c7a24d";
                return kind.startsWith("terminal") ? "#2e705c" : "#0e7376";
              }}
            />
            <Controls showInteractive={false} />
          </ReactFlow>
        </div>
        <EntityInspector run={run} entity={selected} />
      </div>
      <details className="proof-accessible-list">
        <summary>Browse the graph as a structured list</summary>
        <ul>
          {accessibleEntities.map((item) => (
            <li key={item.entity} className={item.dimmed ? "is-dimmed" : ""}>
              <button type="button" onClick={() => updateParameter("selected", item.entity)}>
                <strong>{item.label}</strong>
                <span>{item.detail}</span>
              </button>
            </li>
          ))}
        </ul>
      </details>
    </section>
  );
}

export default function ErdosProofPage() {
  const [parameters, setParameters] = useSearchParams();
  const load = useCallback(
    async (signal: AbortSignal) => {
      const [page, run] = await Promise.all([
        fetchExamplePage("erdos", signal),
        fetchProofRun("erdos", signal),
      ]);
      return { page, run };
    },
    [],
  );
  const resource = useApiResource(load, []);
  const requestedView = parameters.get("view");
  const hasAutoroutes = resource.state === "ready"
    && resource.data.run.dag.autoroutes.length > 0;
  const view: ExplorerView = requestedView === "autoroutes" && hasAutoroutes
    ? "autoroutes"
    : "dag";
  const requestedSelected = parameters.get("selected");
  const query = parameters.get("q") ?? "";
  const requestedKind = parameters.get("kind");
  const kindFilter = resource.state === "ready"
    && resource.data.run.strategy_registrations.some(
      (registration) => registration.kind === requestedKind,
    )
    ? requestedKind ?? ""
    : "";
  const requestedRegistration = parameters.get("registration") ?? "";
  const requestedStatus = parameters.get("status") ?? "";
  const updateParameters = useCallback((
    values: Record<string, string | null>,
    replace = false,
  ) => {
    const next = new URLSearchParams(parameters);
    for (const [name, value] of Object.entries(values)) {
      if (value) next.set(name, value);
      else next.delete(name);
    }
    setParameters(next, { replace });
  }, [parameters, setParameters]);
  const updateParameter = useCallback((
    name: string,
    value: string,
    replace = false,
  ) => updateParameters({ [name]: value }, replace), [updateParameters]);

  const page = resource.state === "ready" ? resource.data.page : null;
  useDocumentMetadata(
    page?.title ?? "Erdős proof explorer",
    page?.summary ?? "Interactive Hypostructure proof-run explorer.",
    "/examples/erdos",
  );

  if (resource.state === "loading") {
    return (
      <section className="request-state" role="status">
        <span className="loading-mark" aria-hidden="true" />
        <p>Reconstructing the structured proof run…</p>
      </section>
    );
  }
  if (resource.state === "error") return <RequestFailure error={resource.error} />;
  const { run } = resource.data;
  const closedTerminals = run.dag.terminals.filter(
    (terminal) => terminal.status === "closed",
  ).length;
  const openTerminals = run.dag.terminals.length - closedTerminals;
  const retainedResiduals = run.dag.terminals.filter(
    (terminal) => terminal.residual.disposition === "open",
  ).length;
  const dichotomyNodes = run.dag.nodes.filter(isDichotomyNode).length;
  const autorouteWork = run.dag.autoroutes.reduce(
    (total, route) => total + route.work,
    0,
  );
  const compatibleCandidates = run.dag.autoroutes.reduce(
    (total, route) => total + route.compatible_candidates.length,
    0,
  );
  const acyclicAutoroutes = run.dag.autoroutes.filter(
    (route) => route.acyclic,
  ).length;
  const requestedTrace = parameters.get("trace");
  const traceDirection: TraceDirection = requestedTrace === "upstream"
    || requestedTrace === "downstream"
    || requestedTrace === "both"
    ? requestedTrace
    : "both";
  const selected = entityRecord(run, requestedSelected) ? requestedSelected : null;
  const registrationFilter = run.strategy_registrations.some(
    (registration) => registration.id === requestedRegistration,
  ) ? requestedRegistration : "";
  const statusFilter = ["active", "certified", "conditional", "open", "closed"].includes(
    requestedStatus,
  ) ? requestedStatus : "";

  return (
    <article className="erdos-proof-page">
      <header className="page-hero erdos-proof-hero">
        <div className="hero-orbit orbit-one" aria-hidden="true" />
        <div className="hero-orbit orbit-two" aria-hidden="true" />
        <div className="hero-content">
          <nav className="breadcrumbs" aria-label="Breadcrumb">
            <ol>
              <li><Link to="/examples">Examples</Link></li>
              <li><span aria-current="page">Erdős proof</span></li>
            </ol>
          </nav>
          <p className="hero-eyebrow">Erdős proof explorer · current strategy API</p>
          <h1>{resource.data.page.title}</h1>
          <p className="hero-summary">
            Inspect the official kernel-certified reduction, including every
            closed branch and every retained strategy residual.
          </p>
          <dl className="hero-metrics">
            <div><dt>Strategy nodes</dt><dd>{run.dag.nodes.length}</dd></div>
            <div><dt>Edges</dt><dd>{run.dag.edges.length}</dd></div>
            <div><dt>Open terminals</dt><dd>{openTerminals}</dd></div>
            <div><dt>Closed terminals</dt><dd>{closedTerminals}</dd></div>
            <div><dt>Dichotomies</dt><dd>{dichotomyNodes}</dd></div>
            <div><dt>Registrations</dt><dd>{run.strategy_registrations.length}</dd></div>
            <div><dt>Run status</dt><dd>Certified</dd></div>
          </dl>
        </div>
      </header>
      <div className="erdos-proof-body">
        <aside className="proof-boundary is-certified" role="note">
          <strong>Kernel-certified reduction</strong>
          <span>{run.trust.verification_note}</span>
          <a href="/api/v2/proof-runs/erdos">Open raw JSON ↗</a>
        </aside>
        <section className="proof-introduction">
          {resource.data.page.sections.map((section) => (
            <div key={section.id}>
              {section.title ? <h2>{section.title}</h2> : null}
              <ContentBlocks blocks={section.blocks} />
            </div>
          ))}
        </section>
        <section className="proof-overview" aria-label="Proof structure summary">
          <article>
            <span>Open terminals</span>
            <strong>{openTerminals}</strong>
            <small>branches not yet closed by the strategy program</small>
          </article>
          <article>
            <span>Closed terminals</span>
            <strong>{closedTerminals}</strong>
            <small>branches discharged by a registered strategy</small>
          </article>
          <article>
            <span>Retained residuals</span>
            <strong>{retainedResiduals}</strong>
            <small>residual obligations preserved by the reduction</small>
          </article>
          <article>
            <span>Checks / work</span>
            <strong>{run.execution.checks_bound} / {run.execution.work_bound}</strong>
            <small>kernel-certified execution bounds</small>
          </article>
        </section>
        {run.dag.autoroutes.length > 0 ? (
          <section className="proof-route-summary" aria-label="Semantic autoroute summary">
            <strong>{run.dag.autoroutes.length} semantic autoroutes</strong>
            <span>{compatibleCandidates} candidates · {autorouteWork} work · {acyclicAutoroutes} acyclic</span>
          </section>
        ) : null}
        <Explorer
          run={run}
          view={view}
          selected={selected}
          traceDirection={traceDirection}
          query={query}
          kindFilter={kindFilter}
          registrationFilter={registrationFilter}
          statusFilter={statusFilter}
          updateParameter={updateParameter}
          updateParameters={updateParameters}
        />
        <section className="registration-catalog" id="registrations">
          <div className="proof-panel-heading">
            <div>
              <p className="section-eyebrow">Registered strategy data</p>
              <h2>Contracts available to the DAG</h2>
            </div>
            <span>{run.strategy_registrations.length} registrations</span>
          </div>
          <div className="registration-grid">
            {run.strategy_registrations.map((registration) => (
              <button
                type="button"
                key={registration.id}
                onClick={() => updateParameter("selected", `registration:${registration.id}`)}
              >
                <small>{registration.id}</small>
                <strong>{registrationSummary(registration)}</strong>
                <span>{registration.interface.length} fields · {registration.components.length} components · {registration.outputs.length} outputs</span>
                {registration.presentation.note ? <p>{registration.presentation.note}</p> : null}
              </button>
            ))}
          </div>
        </section>
        <FormalDefinition run={run} />
        <Outcome run={run} />
      </div>
    </article>
  );
}
