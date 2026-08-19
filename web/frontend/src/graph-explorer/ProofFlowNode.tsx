import { Handle, Position, type NodeProps } from "@xyflow/react";

import { Latex } from "./Latex";
import type { ProofFlowNode as FlowNode } from "./buildGraph";
import type { NodeShape } from "./types";

export const SHAPE_NAMES: Record<NodeShape, string> = {
  assertion: "Assertion",
  decision: "Branch test",
  terminal: "Terminal",
};

export function ProofFlowNode({ data }: NodeProps<FlowNode>) {
  const { node, selected, traced, dimmed, matched, verified } = data;
  const className = [
    "proof-node",
    `proof-node-${node.shape}`,
    node.open ? "proof-node-open" : "",
    selected ? "is-selected" : "",
    traced ? "is-traced" : "",
    matched ? "is-matched" : "",
    dimmed ? "is-dimmed" : "",
  ]
    .filter(Boolean)
    .join(" ");

  return (
    <div className={className} data-open={node.open ? "true" : undefined}>
      <Handle type="target" position={Position.Top} />
      <span className="proof-node-shape" aria-hidden="true" />
      {verified ? <span className="proof-node-verified" aria-label="Lean-verified">✓</span> : null}
      <span className="proof-node-body">
        <span className="proof-node-number">{node.id}</span>
        <span className="proof-node-label">
          <Latex value={node.label} />
          {node.open ? <span className="proof-node-open-tag">open</span> : null}
        </span>
      </span>
      <Handle type="source" position={Position.Bottom} />
    </div>
  );
}

export const nodeTypes = { proof: ProofFlowNode };
