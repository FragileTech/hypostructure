import { useEffect, useState } from "react";

import type { ProofGraphDocument } from "../graph-explorer";
import { loadProofDocument } from "../proofs/document";
import { loadProofSources } from "../proofs/pages";
import { findProof } from "../proofs/registry";

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
    // The PDFs' page maps ride along so a result can say which page it is on;
    // they are a convenience, so a failure there leaves the document intact.
    const proof = findProof(slug);
    Promise.all([loadProofDocument(slug), proof ? loadProofSources(proof) : {}]).then(
      ([document, sources]) => active && setState({ status: "ready", document: { ...document, sources } }),
      (error: Error) => active && setState({ status: "error", error }),
    );
    return () => {
      active = false;
    };
  }, [slug]);

  return state;
}
