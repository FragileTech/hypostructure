import { useEffect, useState } from "react";

import type { ProofGraphDocument } from "../graph-explorer";
import { loadProofDocument } from "../proofs/document";

export type DocumentState =
  | { status: "loading" }
  | { status: "ready"; document: ProofGraphDocument }
  | { status: "error"; error: Error };

export function useProofDocument(slug: string): DocumentState {
  const [state, setState] = useState<DocumentState>({ status: "loading" });

  useEffect(() => {
    // No slug means the route named a proof this site does not have; the page
    // says so itself, and there is nothing to fetch.
    if (!slug) return;

    let active = true;
    setState({ status: "loading" });
    loadProofDocument(slug).then(
      (document) => active && setState({ status: "ready", document }),
      (error: Error) => active && setState({ status: "error", error }),
    );
    return () => {
      active = false;
    };
  }, [slug]);

  return state;
}
