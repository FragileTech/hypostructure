import { useCallback, useMemo } from "react";
import { useSearchParams } from "react-router-dom";

import { GraphExplorer, type ExplorerState, type TraceDirection } from "../graph-explorer";
import { useProof } from "../hooks/useProof";
import { useProofDocument } from "../hooks/useProofDocument";
import { LoadingPanel, ErrorPanel } from "../components/RequestPanels";
import { NotFoundPage } from "./NotFoundPage";

const TRACE_VALUES: TraceDirection[] = ["none", "upstream", "downstream", "both"];

const KEYS: Record<keyof ExplorerState, string> = {
  selected: "step",
  chapter: "paper",
  group: "panel",
  trace: "trace",
  query: "q",
  item: "result",
};

function readState(parameters: URLSearchParams): ExplorerState {
  const trace = parameters.get(KEYS.trace) as TraceDirection | null;
  return {
    selected: parameters.get(KEYS.selected),
    chapter: parameters.get(KEYS.chapter),
    group: parameters.get(KEYS.group),
    // Off by default: selecting a step frames its neighbourhood, and tracing is
    // an explicit choice to light up a whole branch.
    trace: trace && TRACE_VALUES.includes(trace) ? trace : "none",
    query: parameters.get(KEYS.query) ?? "",
    item: parameters.get(KEYS.item),
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
            if (value === null || value === "" || (field === "trace" && value === "none")) {
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
