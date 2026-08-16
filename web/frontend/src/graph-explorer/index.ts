/**
 * A reusable explorer for proof-dependency diagrams.
 *
 * Supply a `ProofGraphDocument` — nodes, arrows, and the results behind each
 * node — and this module renders an interactive flow with a detail panel that
 * shows the mathematics. It has no knowledge of any particular paper.
 */

export { GraphExplorer, type ExplorerState, type GraphExplorerProps } from "./GraphExplorer";
export { NodeDetailPanel, type NodeDetailPanelProps } from "./NodeDetailPanel";
export { ProofFlowNode, SHAPE_NAMES, nodeTypes } from "./ProofFlowNode";
export { Latex, MathProvider, type Reference } from "./Latex";
export { parseLatex, latexToPlainText, type Segment } from "./latex";
export { buildGraph, type BuildOptions, type FlowNodeData, type ProofFlowNode as FlowNode } from "./buildGraph";
export { indexDocument } from "./index-document";
export { layoutGraph, type LayoutBox, type LayoutLink, type LayoutOptions } from "./layout";
export { traceFrom, type Trace } from "./trace";
export { buildSearchIndex, matchNodes, nodeSearchText } from "./search";
export { createReferenceResolver } from "./references";
export { useDetailWidth, clampDetailWidth, DEFAULT_DETAIL_WIDTH } from "./useDetailWidth";
export type * from "./types";
