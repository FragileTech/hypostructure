import { useParams } from "react-router-dom";

import { findProof, type ProofEntry } from "../proofs/registry";

/** The proof named by the current route, or undefined for an unknown slug. */
export function useProof(): ProofEntry | undefined {
  const { proof } = useParams();
  return findProof(proof);
}
