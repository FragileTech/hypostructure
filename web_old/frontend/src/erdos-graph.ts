import dagre from "@dagrejs/dagre";
import type { Edge, Node } from "@xyflow/react";

import type {
  DagNode,
  DagTerminal,
  HypostructureProofRun,
  SemanticAutorouteRecord,
  StrategyReference,
} from "./proof-run-types";

export type ExplorerEntityKind =
  | "autoroute"
  | "node"
  | "terminal"
  | "edge"
  | "registration";

export interface ProofGraphData extends Record<string, unknown> {
  label: string;
  subtitle: string;
  kind: string;
  entity: string;
  dimmed: boolean;
  traced?: boolean;
  depth?: number;
  entry?: boolean;
}

export type ProofGraphNode = Node<ProofGraphData, "proof">;

const STANDARD_NODE_SIZE = { width: 232, height: 82 } as const;
const DICHOTOMY_NODE_SIZE = { width: 232, height: 112 } as const;

export function isDichotomyNode(node: DagNode): boolean {
  return node.kind !== "join"
    && (node.kind === "decision" || node.strategy.kind.endsWith("_dichotomy"));
}

function graphNodeKind(node: DagNode): string {
  if (node.kind === "join") return node.kind;
  return isDichotomyNode(node) ? "decision" : node.kind;
}

function graphNodeSize(node: ProofGraphNode) {
  return node.data.kind === "decision"
    ? DICHOTOMY_NODE_SIZE
    : STANDARD_NODE_SIZE;
}

function strategyLabel(strategy: StrategyReference): string {
  return strategy.index === null
    ? strategy.kind.replaceAll("_", " ")
    : `${strategy.kind.replaceAll("_", " ")} #${strategy.index}`;
}

export function dagNodeLabel(node: DagNode): string {
  if (node.kind === "join") {
    return node.presentation.label ?? `join #${node.internal_id}`;
  }
  return (
    node.presentation.resolved.label
    ?? node.presentation.authored.label
    ?? strategyLabel(node.strategy)
  );
}

export function terminalLabel(terminal: DagTerminal): string {
  return `${terminal.id} · ${terminal.status} terminal`;
}

export function autorouteRecordId(
  route: SemanticAutorouteRecord,
  index: number,
): string {
  return `${route.source_id}->${route.destination_id}@${index}`;
}

export function findAutoroute(
  run: HypostructureProofRun,
  id: string,
): SemanticAutorouteRecord | undefined {
  return run.dag.autoroutes.find(
    (route, index) => autorouteRecordId(route, index) === id,
  );
}

function autorouteLabel(route: SemanticAutorouteRecord): string {
  return route.presentation.label ?? route.relation.replaceAll("_", " ");
}

function autorouteSearchText(route: SemanticAutorouteRecord): string {
  return [
    route.source_id,
    route.destination_id,
    route.source_depth,
    route.destination_depth,
    route.relation,
    route.presentation.label,
    route.presentation.note,
    route.presentation.tags.join(" "),
    route.selection.rule,
    route.selection.selected_candidate_id,
    route.selection.tie_break,
    route.work,
    route.acyclic,
    route.bridge_provenance.relation_witness,
    route.bridge_provenance.target_congruence,
    route.bridge_provenance.destination_requirements.join(" "),
    route.bridge_provenance.ledger_ancestors.join(" "),
    route.bridge_provenance.framework_lemmas.join(" "),
    route.bridge_provenance.ledger_extension,
    ...route.compatible_candidates.flatMap((candidate) => [
      candidate.node_id,
      candidate.depth,
      candidate.relation,
    ]),
  ].filter((value) => value !== null).join(" ");
}

function layout(
  nodes: ProofGraphNode[],
  edges: Edge[],
  direction: "TB" | "LR",
): ProofGraphNode[] {
  const graph = new dagre.graphlib.Graph();
  graph.setDefaultEdgeLabel(() => ({}));
  graph.setGraph({
    rankdir: direction,
    ranksep: direction === "TB" ? 76 : 100,
    nodesep: 42,
    edgesep: 24,
    marginx: 24,
    marginy: 24,
  });
  for (const node of nodes) graph.setNode(node.id, graphNodeSize(node));
  for (const edge of edges) graph.setEdge(edge.source, edge.target);
  dagre.layout(graph);
  return nodes.map((node) => {
    const position = graph.node(node.id) as { x: number; y: number };
    const size = graphNodeSize(node);
    return {
      ...node,
      position: {
        x: position.x - size.width / 2,
        y: position.y - size.height / 2,
      },
    };
  });
}

function semanticAutorouteEdges(run: HypostructureProofRun): Edge[] {
  return run.dag.autoroutes.map((route, index) => {
    const id = autorouteRecordId(route, index);
    return {
      id: `autoroute-edge:${id}`,
      source: route.source_id,
      target: route.destination_id,
      label: autorouteLabel(route),
      type: "smoothstep",
      animated: false,
      data: { entity: `autoroute:${id}` },
      className: "proof-edge proof-edge-route",
    };
  });
}

function normalizedDagEdges(run: HypostructureProofRun): Edge[] {
  const routeQueues = new Map<string, Array<{ route: SemanticAutorouteRecord; index: number }>>();
  run.dag.autoroutes.forEach((route, index) => {
    const key = `${route.source_id}->${route.destination_id}`;
    routeQueues.set(key, [...(routeQueues.get(key) ?? []), { route, index }]);
  });
  return run.dag.edges.map((edge) => {
    if (edge.kind === "autoroute") {
      const key = `${edge.source}->${edge.target}`;
      const [resolved, ...remaining] = routeQueues.get(key) ?? [];
      routeQueues.set(key, remaining);
      if (resolved) {
        const routeId = autorouteRecordId(resolved.route, resolved.index);
        return {
          id: `autoroute-edge:${routeId}`,
          source: edge.source,
          target: edge.target,
          label: edge.presentation.label ?? autorouteLabel(resolved.route),
          type: "smoothstep",
          data: { entity: `autoroute:${routeId}` },
          className: "proof-edge proof-edge-route",
        };
      }
    }
    return {
      id: edge.id,
      source: edge.source,
      target: edge.target,
      label: edge.presentation.label ?? edge.output ?? undefined,
      type: "smoothstep",
      data: { entity: `edge:${edge.id}` },
      className: `proof-edge proof-edge-${edge.status}`,
    };
  });
}

export function buildAutorouteGraph(run: HypostructureProofRun): {
  nodes: ProofGraphNode[];
  edges: Edge[];
} {
  const depths = new Map<string, number>();
  for (const route of run.dag.autoroutes) {
    depths.set(route.source_id, route.source_depth);
    depths.set(route.destination_id, route.destination_depth);
  }
  const nodes = [...depths.entries()].map(([id, depth]): ProofGraphNode => {
    const node = run.dag.nodes.find((candidate) => candidate.id === id);
    return {
      id,
      type: "proof",
      position: { x: 0, y: 0 },
      data: {
        label: node ? dagNodeLabel(node) : id,
        subtitle: `${id} · depth ${depth}`,
        kind: "autoroute-node",
        entity: `node:${id}`,
        dimmed: false,
        depth,
        entry: id === run.dag.entry,
      },
    };
  });
  const edges = semanticAutorouteEdges(run);
  return { nodes: layout(nodes, edges, "LR"), edges };
}

export function buildDagGraph(run: HypostructureProofRun): {
  nodes: ProofGraphNode[];
  edges: Edge[];
} {
  const strategyNodes: ProofGraphNode[] = run.dag.nodes.map((node) => ({
    id: node.id,
    type: "proof",
    position: { x: 0, y: 0 },
    data: {
      label: dagNodeLabel(node),
      subtitle:
        node.kind === "join"
          ? `${node.id} · join`
          : `${node.id} · ${node.strategy.registration_id ?? node.strategy.kind}`,
      kind: graphNodeKind(node),
      entity: `node:${node.id}`,
      dimmed: false,
      entry: node.id === run.dag.entry,
    },
  }));
  const terminals: ProofGraphNode[] = run.dag.terminals.map((terminal) => ({
    id: terminal.id,
    type: "proof",
    position: { x: 0, y: 0 },
    data: {
      label: terminalLabel(terminal),
      subtitle: terminal.reason,
      kind: `terminal-${terminal.status}`,
      entity: `terminal:${terminal.id}`,
      dimmed: false,
    },
  }));
  const edges = normalizedDagEdges(run);
  const nodes = [...strategyNodes, ...terminals];
  return { nodes: layout(nodes, edges, "TB"), edges };
}

export type TraceDirection = "upstream" | "downstream" | "both";

interface TraceEdge {
  id: string;
  source: string;
  target: string;
}

function traceEdges(run: HypostructureProofRun): TraceEdge[] {
  return normalizedDagEdges(run).map(({ id, source, target }) => ({
    id,
    source,
    target,
  }));
}

export function traceSelection(
  run: HypostructureProofRun,
  startId: string | null,
  direction: TraceDirection,
): { vertexIds: Set<string>; edgeIds: Set<string> } {
  if (!startId) return { vertexIds: new Set(), edgeIds: new Set() };
  const outgoing = new Map<string, TraceEdge[]>();
  const incoming = new Map<string, TraceEdge[]>();
  for (const edge of traceEdges(run)) {
    outgoing.set(edge.source, [...(outgoing.get(edge.source) ?? []), edge]);
    incoming.set(edge.target, [...(incoming.get(edge.target) ?? []), edge]);
  }
  const vertexIds = new Set([startId]);
  const edgeIds = new Set<string>();
  const walk = (
    index: Map<string, TraceEdge[]>,
    next: (edge: TraceEdge) => string,
  ) => {
    const queue = [startId];
    while (queue.length) {
      const vertex = queue.shift()!;
      for (const edge of index.get(vertex) ?? []) {
        edgeIds.add(edge.id);
        const adjacent = next(edge);
        if (!vertexIds.has(adjacent)) {
          vertexIds.add(adjacent);
          queue.push(adjacent);
        }
      }
    }
  };
  if (direction === "downstream" || direction === "both") {
    walk(outgoing, (edge) => edge.target);
  }
  if (direction === "upstream" || direction === "both") {
    walk(incoming, (edge) => edge.source);
  }
  return { vertexIds, edgeIds };
}

export function entitySearchText(
  run: HypostructureProofRun,
  entity: string,
): string {
  const separator = entity.indexOf(":");
  if (separator < 0) return "";
  const kind = entity.slice(0, separator) as ExplorerEntityKind;
  const id = entity.slice(separator + 1);
  if (kind === "autoroute") {
    const route = findAutoroute(run, id);
    return route ? autorouteSearchText(route) : "";
  }
  if (kind === "node") {
    const node = run.dag.nodes.find((item) => item.id === id);
    if (!node) return "";
    if (node.kind === "join") {
      return `${node.id} ${node.internal_id} join ${node.presentation.label ?? ""} ${node.presentation.note ?? ""}`;
    }
    return [
      node.id,
      node.internal_id,
      node.kind,
      node.status,
      node.strategy.kind,
      node.strategy.index,
      node.strategy.registration_id,
      node.presentation.authored.label,
      node.presentation.authored.note,
      node.presentation.registered.label,
      node.presentation.registered.note,
      node.presentation.registered.tags.join(" "),
      node.presentation.resolved.label,
      node.presentation.resolved.note,
      ...node.components.flatMap((item) => [
        item.label,
        item.note,
        item.tags.join(" "),
      ]),
    ].filter((value) => value !== null).join(" ");
  }
  if (kind === "terminal") {
    const terminal = run.dag.terminals.find((item) => item.id === id);
    return terminal
      ? `${terminal.id} ${terminal.internal_id} ${terminal.kind} ${terminal.status} ${terminal.reason} ${terminal.residual.kind} ${terminal.residual.disposition}`
      : "";
  }
  if (kind === "edge") {
    const edge = run.dag.edges.find((item) => item.id === id);
    return edge
      ? `${edge.id} ${edge.internal_id} ${edge.kind} ${edge.status} ${edge.source} ${edge.target} ${edge.output ?? ""} ${edge.presentation.label ?? ""} ${edge.presentation.note ?? ""}`
      : "";
  }
  const registration = run.strategy_registrations.find((item) => item.id === id);
  return registration
    ? [
      registration.id,
      registration.index,
      registration.kind,
      registration.presentation.label,
      registration.presentation.note,
      registration.presentation.tags.join(" "),
      ...registration.interface.map((item) => item.name),
      ...registration.components.flatMap((item) => [
        item.label,
        item.note,
        item.tags.join(" "),
      ]),
    ].filter((value) => value !== null).join(" ")
    : "";
}
