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
  const { node, selected, traced, dimmed, matched } = data;
  const className = [
    "proof-node",
    `proof-node-${node.shape}`,
    selected ? "is-selected" : "",
    traced ? "is-traced" : "",
    matched ? "is-matched" : "",
    dimmed ? "is-dimmed" : "",
  ]
    .filter(Boolean)
    .join(" ");

  return (
    <div className={className}>
      <Handle type="target" position={Position.Top} />
      <span className="proof-node-shape" aria-hidden="true" />
      <span className="proof-node-body">
        <span className="proof-node-number">{node.id}</span>
        <span className="proof-node-label">
          <Latex value={node.label} />
        </span>
      </span>
      <Handle type="source" position={Position.Bottom} />
    </div>
  );
}

export const nodeTypes = { proof: ProofFlowNode };
