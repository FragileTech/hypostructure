import { useCallback, useEffect, useMemo, useRef } from "react";
import {
  Background,
  Controls,
  MiniMap,
  ReactFlow,
  ReactFlowProvider,
  useReactFlow,
  useStore,
  type Edge,
} from "@xyflow/react";
import "@xyflow/react/dist/style.css";

import { Latex, MathProvider } from "./Latex";
import { NodeDetailPanel, type NodeDetailPanelProps } from "./NodeDetailPanel";
import { RefereePanel } from "./RefereePanel";
import { SHAPE_NAMES, nodeTypes } from "./ProofFlowNode";
import { boundsOf, buildGraph, type ProofFlowNode } from "./buildGraph";
import { createReferenceResolver } from "./references";
import { indexDocument } from "./index-document";
import { buildSearchIndex, matchNodes } from "./search";
import { traceFrom } from "./trace";
import { useDetailWidth } from "./useDetailWidth";
import type { ExplorerMode, ProofGraphDocument, TraceDirection } from "./types";

/** Grow a rectangle about its centre until it is at least the given size. */
function expand(
  bounds: { x: number; y: number; width: number; height: number },
  minimumWidth: number,
  minimumHeight: number,
) {
  const width = Math.max(bounds.width, minimumWidth);
  const height = Math.max(bounds.height, minimumHeight);
  return {
    x: bounds.x - (width - bounds.width) / 2,
    y: bounds.y - (height - bounds.height) / 2,
    width,
    height,
  };
}

const TRACE_OPTIONS: { value: TraceDirection; label: string; hint: string }[] = [
  { value: "none", label: "Off", hint: "Show the whole panel" },
  { value: "upstream", label: "What led here", hint: "Everything the step depends on" },
  { value: "downstream", label: "Where it goes", hint: "Everything the step feeds" },
  { value: "both", label: "Both", hint: "The full branch through this step" },
];

const MODE_OPTIONS: { value: ExplorerMode; label: string; hint: string }[] = [
  { value: "reader", label: "Reader", hint: "What each step does, then the results behind it" },
  {
    value: "referee",
    label: "Referee",
    hint: "Evidence first: the claim, the state it may assume, its cases and its impact",
  },
];

export interface ExplorerState {
  selected: string | null;
  chapter: string | null;
  group: string | null;
  trace: TraceDirection;
  query: string;
  item: string | null;
  /** How the detail column reads a step. */
  mode: ExplorerMode;
  /** A standing constraint to light up on the canvas: every step that tracks it. */
  constraint: string | null;
}

export interface GraphExplorerProps {
  document: ProofGraphDocument;
  state: ExplorerState;
  onChange: (patch: Partial<ExplorerState>) => void;
}

/**
 * The workbench: a canvas of the proof flow beside the detail panel for whatever
 * step is selected. All view state is owned by the caller, so it can live in the
 * URL and every view stays linkable.
 */
/**
 * Moves the viewport onto the steps worth looking at.
 *
 * Lives inside the canvas and waits for it to have a size. It deliberately does
 * not wait for the nodes to be measured: their boxes are set from the layout, so
 * the canvas never measures them and would never report them as initialised.
 */
function Framing({
  nodes,
  focusIds,
}: {
  nodes: ProofFlowNode[];
  focusIds: Set<string> | null;
}) {
  const flow = useReactFlow();
  const measured = useStore((store) => store.width > 0 && store.height > 0);
  const framed = useRef(false);

  useEffect(() => {
    if (!measured || !focusIds) return;
    // The selected step may be filtered off the canvas, in which case there is
    // nothing to frame on it and the panel as a whole is the next best view.
    const bounds =
      boundsOf(nodes, focusIds) ?? boundsOf(nodes, new Set(nodes.map((node) => node.id)));
    if (!bounds) return;
    // Keep a little of the surrounding argument in frame; without a floor, a
    // step with one neighbour fills the canvas.
    flow.fitBounds(expand(bounds, 940, 620), {
      padding: 0.14,
      // The first view arrives already framed; later moves are worth following.
      duration: framed.current ? 420 : 0,
    });
    framed.current = true;
  }, [flow, focusIds, measured, nodes]);

  return null;
}

/** The detail column, read one way or the other. */
function DetailPanel({ mode, ...props }: NodeDetailPanelProps & { mode: ExplorerMode }) {
  return mode === "referee" ? <RefereePanel {...props} /> : <NodeDetailPanel {...props} />;
}

export function GraphExplorer({ document, state, onChange }: GraphExplorerProps) {
  const index = useMemo(() => indexDocument(document), [document]);
  const hasOpenNodes = useMemo(() => document.nodes.some((node) => node.open), [document]);
  const searchIndex = useMemo(
    () => buildSearchIndex(document, index),
    [document, index],
  );

  const detail = useDetailWidth(`proof-explorer:${document.id}:detail-width`);

  const selectedNode = state.selected ? index.nodeById.get(state.selected) : undefined;

  const trace = useMemo(
    () => traceFrom(document.edges, state.selected, state.trace),
    [document.edges, state.selected, state.trace],
  );

  const matchedIds = useMemo(() => {
    if (state.constraint) {
      return new Set(index.nodesByInvariant.get(state.constraint) ?? []);
    }
    const matched = matchNodes(searchIndex, state.query);
    return matched.size ? matched : null;
  }, [index, searchIndex, state.constraint, state.query]);

  const { nodes, edges } = useMemo(
    () =>
      buildGraph(document, {
        chapter: state.chapter,
        group: state.group,
        selectedId: state.selected,
        tracedNodeIds: trace.nodeIds,
        tracedEdgeIds: trace.edgeIds,
        matchedIds,
      }),
    [document, matchedIds, state.chapter, state.group, state.selected, trace],
  );

  /**
   * What the canvas should frame: the traced branch when one is being followed,
   * otherwise the selected step and whatever it directly touches. Tracing both
   * directions through a connected proof reaches nearly every step, so framing
   * the neighbourhood is what actually lets you read the diagram.
   */
  const focusIds = useMemo(() => {
    if (!state.selected) return new Set(nodes.map((node) => node.id));
    if (state.trace !== "none" && trace.nodeIds.size) return trace.nodeIds;
    // Neighbours in another paper are a jump, not adjacency: including them
    // would zoom out far enough to take in both, showing neither.
    const selected = index.nodeById.get(state.selected);
    const neighbours = new Set([state.selected]);
    const near = (id: string) => {
      const node = index.nodeById.get(id);
      if (node && node.chapter === selected?.chapter) neighbours.add(id);
    };
    for (const edge of index.incoming.get(state.selected) ?? []) near(edge.source);
    for (const edge of index.outgoing.get(state.selected) ?? []) near(edge.target);
    return neighbours;
  }, [index, nodes, state.selected, state.trace, trace]);

  /** Widen the filters just enough that a step stays visible when selected. */
  const reveal = useCallback(
    (id: string) => {
      const node = index.nodeById.get(id);
      if (!node) return {};
      return {
        chapter: state.chapter && node.chapter !== state.chapter ? node.chapter ?? null : state.chapter,
        group: state.group && node.group !== state.group ? node.group : state.group,
      };
    },
    [index, state.chapter, state.group],
  );

  const selectNode = useCallback(
    (id: string) => {
      onChange({ selected: id, item: null, ...reveal(id) });
    },
    [onChange, reveal],
  );

  /**
   * Light up every step tracking a constraint, or put the light out again when
   * the same chip is pressed a second time. Search and the constraint share the
   * canvas highlight, so one always replaces the other.
   */
  const toggleInvariant = useCallback(
    (id: string) => {
      onChange({ constraint: state.constraint === id ? null : id, query: "" });
    },
    [onChange, state.constraint],
  );

  const references = useMemo(
    () =>
      createReferenceResolver(
        document,
        index,
        state.selected ? index.nodeById.get(state.selected)?.chapter : undefined,
      ),
    [document, index, state.selected],
  );

  const openReference = useCallback(
    (key: string) => {
      const named = references.target(key);
      if (named.group) {
        const group = index.groupById.get(named.group);
        onChange({
          group: named.group,
          chapter: state.chapter && group?.chapter ? group.chapter : state.chapter,
        });
        return;
      }
      const holders = named.item ? index.nodesByItem.get(named.item) : undefined;
      if (named.item && holders?.length) {
        const target = holders.includes(state.selected ?? "") ? state.selected! : holders[0];
        onChange({ selected: target, item: named.item, ...reveal(target) });
      }
    },
    [index, onChange, references, reveal, state.chapter, state.selected],
  );

  const panels = useMemo(
    () =>
      state.chapter
        ? document.groups.filter((group) => group.chapter === state.chapter)
        : document.groups,
    [document.groups, state.chapter],
  );

  /** What the canvas is currently showing, narrowest first. */
  const scope = useMemo(() => {
    const panel = state.group ? index.groupById.get(state.group) : undefined;
    if (panel) return { title: panel.title, summary: panel.summary || panel.caption };

    const chapter = state.chapter ? index.chapterById.get(state.chapter) : undefined;
    if (chapter) return { title: chapter.title, summary: chapter.description };

    return { title: document.title, summary: document.subtitle };
  }, [document, index, state.chapter, state.group]);

  const matchCount = matchedIds?.size ?? 0;

  return (
    <MathProvider
      macros={document.macros}
      onReference={openReference}
      resolveReference={references.resolve}
    >
      <div className={`explorer${state.mode === "referee" ? " is-referee" : ""}`}>
        <div className="explorer-toolbar">
          <label className="field field-search">
            <span>Search the proof</span>
            <input
              type="search"
              value={state.query}
              placeholder="entropy cap, route 8, Mersenne…"
              onChange={(event) => onChange({ query: event.target.value, constraint: null })}
            />
          </label>

          {document.chapters?.length ? (
            <label className="field">
              <span>Paper</span>
              <select
                value={state.chapter ?? ""}
                onChange={(event) =>
                  onChange({ chapter: event.target.value || null, group: null })
                }
              >
                <option value="">
                  All {document.chapters.length} papers
                </option>
                {document.chapters.map((chapter) => (
                  <option key={chapter.id} value={chapter.id}>
                    {chapter.shortTitle}
                  </option>
                ))}
              </select>
            </label>
          ) : null}

          <label className="field">
            <span>Panel</span>
            <select
              value={state.group ?? ""}
              onChange={(event) => onChange({ group: event.target.value || null })}
            >
              <option value="">All {panels.length} panels</option>
              {panels.map((group) => {
                const chapter = group.chapter
                  ? index.chapterById.get(group.chapter)
                  : undefined;
                return (
                  <option key={group.id} value={group.id}>
                    {chapter && !state.chapter
                      ? `${chapter.shortTitle} · ${group.title}`
                      : group.title}
                  </option>
                );
              })}
            </select>
          </label>

          <fieldset className="field field-mode">
            <legend>Read as</legend>
            <div className="segmented">
              {MODE_OPTIONS.map((option) => (
                <button
                  key={option.value}
                  type="button"
                  title={option.hint}
                  className={state.mode === option.value ? "is-active" : ""}
                  onClick={() => onChange({ mode: option.value })}
                >
                  {option.label}
                </button>
              ))}
            </div>
          </fieldset>

          <fieldset className="field field-trace">
            <legend>Follow the branch</legend>
            <div className="segmented">
              {TRACE_OPTIONS.map((option) => (
                <button
                  key={option.value}
                  type="button"
                  title={option.hint}
                  className={state.trace === option.value ? "is-active" : ""}
                  onClick={() => onChange({ trace: option.value })}
                >
                  {option.label}
                </button>
              ))}
            </div>
          </fieldset>

          <div className="explorer-status" role="status">
            {state.constraint ? (
              <button
                type="button"
                className="chip chip-clear"
                onClick={() => onChange({ constraint: null })}
              >
                Constraint {index.invariantById.get(state.constraint)?.number ?? state.constraint} ·{" "}
                {matchCount} {matchCount === 1 ? "step" : "steps"} · clear
              </button>
            ) : matchedIds ? (
              <span>
                {matchCount} of {nodes.length} steps match
              </span>
            ) : (
              <span>
                {nodes.length} steps
                {state.group
                  ? " in this panel"
                  : state.chapter
                    ? " in this paper"
                    : ` across ${document.groups.length} panels`}
              </span>
            )}
          </div>
        </div>

        {state.group ? (
          <p className="explorer-caption">
            <strong>{index.groupById.get(state.group)?.title}</strong>
            <Latex value={index.groupById.get(state.group)?.caption ?? ""} />
          </p>
        ) : null}

        <div
          className={`explorer-body${detail.dragging ? " is-resizing" : ""}`}
          ref={detail.container}
          style={{ ["--detail-width" as string]: `${detail.width}px` }}
        >
          <div className="explorer-canvas">
            <ReactFlowProvider>
            <ReactFlow<ProofFlowNode, Edge>
              nodes={nodes}
              edges={edges}
              nodeTypes={nodeTypes}
              minZoom={0.06}
              maxZoom={1.8}
              nodesDraggable={false}
              nodesConnectable={false}
              elementsSelectable
              proOptions={{ hideAttribution: true }}
              onNodeClick={(_event, node) => selectNode(node.id)}
            >
              <Framing key={document.id} nodes={nodes} focusIds={focusIds} />
              <Background gap={26} size={1} />
              <MiniMap pannable zoomable ariaLabel="Proof map" />
              <Controls showInteractive={false} />
            </ReactFlow>
            </ReactFlowProvider>

            <ul className="shape-key">
              {(["assertion", "decision", "terminal"] as const).map((shape) => (
                <li key={shape}>
                  <span className={`shape-swatch shape-${shape}`} aria-hidden="true" />
                  {SHAPE_NAMES[shape]}
                </li>
              ))}
              {hasOpenNodes ? (
                <li>
                  <span className="shape-swatch shape-open" aria-hidden="true" />
                  Open outcome
                </li>
              ) : null}
              <li>
                <span className="shape-swatch shape-continuation" aria-hidden="true" />
                Continues in another panel
              </li>
            </ul>
          </div>

          <div
            className="explorer-resizer"
            role="separator"
            aria-orientation="vertical"
            aria-label="Resize the detail column"
            aria-valuenow={Math.round(detail.width)}
            tabIndex={0}
            title="Drag to resize · double-click to reset"
            {...detail.handleProps}
          >
            <span aria-hidden="true" />
          </div>

          <aside className="explorer-detail">
            {selectedNode ? (
              <DetailPanel
                mode={state.mode}
                document={document}
                index={index}
                node={selectedNode}
                focusItem={state.item}
                activeInvariant={state.constraint}
                onSelectNode={selectNode}
                onSelectItem={(item) => onChange({ item })}
                onSelectInvariant={toggleInvariant}
              />
            ) : (
              <div className="explorer-empty">
                <h2>{scope.title}</h2>
                <p className="explorer-empty-summary">
                  <Latex value={scope.summary} />
                </p>
                <p>
                  {state.mode === "referee"
                    ? "Pick a step to see its claim, the state it may assume, its evidence and what depends on it — or start at "
                    : "Pick a step to see what it asserts, which results stand behind it, and where the argument goes next — or start at "}
                  <button
                    type="button"
                    className="chip chip-node"
                    onClick={() => selectNode(nodes[0]?.id ?? document.nodes[0].id)}
                  >
                    {nodes[0]?.id ?? document.nodes[0].id}
                  </button>{" "}
                  and walk forwards.
                </p>
              </div>
            )}
          </aside>
        </div>

        <details className="explorer-outline">
          <summary>All steps, as a list</summary>
          <ol>
            {nodes.map((node) => (
              <li key={node.id}>
                <button type="button" onClick={() => selectNode(node.id)}>
                  <span className="chip chip-node">{node.id}</span>
                  {node.data.plain}
                </button>
              </li>
            ))}
          </ol>
        </details>
      </div>
    </MathProvider>
  );
}
