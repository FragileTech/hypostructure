import type { ProofGraphDocument } from "../graph-explorer";

const pending = new Map<string, Promise<ProofGraphDocument>>();

/**
 * A proof's dependency diagram, extracted from its manuscripts by
 * `web/tools/extract_proof_graph.py`. Fetched once per proof and shared.
 */
export function loadProofDocument(slug: string): Promise<ProofGraphDocument> {
  const existing = pending.get(slug);
  if (existing) return existing;

  const request = fetch(`${import.meta.env.BASE_URL}data/${slug}.json`).then((response) => {
    if (!response.ok) {
      throw new Error(
        `Could not load the ${slug} diagram (${response.status} ${response.statusText}).`,
      );
    }
    return response.json() as Promise<ProofGraphDocument>;
  });
  pending.set(slug, request);
  return request;
}
