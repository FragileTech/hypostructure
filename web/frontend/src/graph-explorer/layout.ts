import dagre from "@dagrejs/dagre";

export interface LayoutBox {
  id: string;
  width: number;
  height: number;
}

export interface LayoutLink {
  source: string;
  target: string;
}

export interface LayoutOptions {
  direction?: "TB" | "LR";
  rankSeparation?: number;
  nodeSeparation?: number;
  edgeSeparation?: number;
  margin?: number;
}

/**
 * Rank the boxes with dagre and return top-left positions.
 *
 * dagre reports node centres; React Flow positions by top-left corner, so each
 * result is shifted by half the box.
 */
export function layoutGraph(
  boxes: LayoutBox[],
  links: LayoutLink[],
  options: LayoutOptions = {},
): Map<string, { x: number; y: number }> {
  const {
    direction = "TB",
    rankSeparation = direction === "TB" ? 78 : 104,
    nodeSeparation = 46,
    edgeSeparation = 24,
    margin = 32,
  } = options;

  const graph = new dagre.graphlib.Graph();
  graph.setDefaultEdgeLabel(() => ({}));
  graph.setGraph({
    rankdir: direction,
    ranksep: rankSeparation,
    nodesep: nodeSeparation,
    edgesep: edgeSeparation,
    marginx: margin,
    marginy: margin,
  });

  const known = new Set(boxes.map((box) => box.id));
  for (const box of boxes) {
    graph.setNode(box.id, { width: box.width, height: box.height });
  }
  for (const link of links) {
    if (known.has(link.source) && known.has(link.target)) {
      graph.setEdge(link.source, link.target);
    }
  }

  dagre.layout(graph);

  const positions = new Map<string, { x: number; y: number }>();
  for (const box of boxes) {
    const placed = graph.node(box.id) as { x: number; y: number } | undefined;
    if (!placed) continue;
    positions.set(box.id, {
      x: placed.x - box.width / 2,
      y: placed.y - box.height / 2,
    });
  }
  return positions;
}
