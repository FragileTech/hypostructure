import { useCallback, useMemo } from "react";
import { useSearchParams } from "react-router-dom";

import {
  GraphExplorer,
  type ExplorerMode,
  type ExplorerState,
  type TraceDirection,
} from "../graph-explorer";
import { useProof } from "../hooks/useProof";
import { useProofDocument } from "../hooks/useProofDocument";
import { LoadingPanel, ErrorPanel } from "../components/RequestPanels";
import { NotFoundPage } from "./NotFoundPage";

const TRACE_VALUES: TraceDirection[] = ["none", "upstream", "downstream", "both"];
const MODE_VALUES: ExplorerMode[] = ["reader", "referee"];

const KEYS: Record<keyof ExplorerState, string> = {
  selected: "step",
  chapter: "paper",
  group: "panel",
  trace: "trace",
  query: "q",
  item: "result",
  mode: "mode",
  constraint: "constraint",
};

export function readState(parameters: URLSearchParams): ExplorerState {
  const trace = parameters.get(KEYS.trace) as TraceDirection | null;
  const mode = parameters.get(KEYS.mode) as ExplorerMode | null;
  return {
    selected: parameters.get(KEYS.selected),
    chapter: parameters.get(KEYS.chapter),
    group: parameters.get(KEYS.group),
    // Off by default: selecting a step frames its neighbourhood, and tracing is
    // an explicit choice to light up a whole branch.
    trace: trace && TRACE_VALUES.includes(trace) ? trace : "none",
    query: parameters.get(KEYS.query) ?? "",
    item: parameters.get(KEYS.item),
    // Reading is the default; a referee asks for the other view, and the link
    // carries it so a view can be handed on.
    mode: mode && MODE_VALUES.includes(mode) ? mode : "reader",
    constraint: parameters.get(KEYS.constraint),
  };
}

export function ExplorePage() {
  const proof = useProof();
  const [parameters, setParameters] = useSearchParams();
  const state = useMemo(() => readState(parameters), [parameters]);
  const request = useProofDocument(proof?.slug ?? "");

  const onChange = useCallback(
    (patch: Partial<ExplorerState>) => {
      setParameters(
        (current) => {
          const next = new URLSearchParams(current);
          for (const [field, value] of Object.entries(patch)) {
            const key = KEYS[field as keyof ExplorerState];
            const isDefault =
              (field === "trace" && value === "none") || (field === "mode" && value === "reader");
            if (value === null || value === "" || isDefault) {
              next.delete(key);
            } else {
              next.set(key, String(value));
            }
          }
          return next;
        },
        { replace: true },
      );
    },
    [setParameters],
  );

  if (!proof) return <NotFoundPage />;
  if (request.status === "loading") return <LoadingPanel />;
  if (request.status === "error") return <ErrorPanel error={request.error} />;

  return (
    <div className="page page-explore">
      <GraphExplorer document={request.document} state={state} onChange={onChange} />
    </div>
  );
}
