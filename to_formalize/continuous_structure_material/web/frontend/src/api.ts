import type {
  PageView,
  SearchView,
  SiteView,
  SourceExcerptView,
} from "./v2-types";
import type { HypostructureProofRun } from "./proof-run-types";

export class ApiError extends Error {
  constructor(message: string, readonly status: number) {
    super(message);
  }
}

async function getJson<T>(path: string, signal?: AbortSignal): Promise<T> {
  const response = await fetch(path, {
    headers: { Accept: "application/json" },
    signal,
  });
  if (!response.ok) {
    let message = `${response.status} ${response.statusText}`;
    try {
      const body = (await response.json()) as {
        detail?: string;
        title?: string;
        message?: string;
      };
      message = body.detail ?? body.message ?? body.title ?? message;
    } catch {
      // Keep the HTTP status when an upstream server returns a non-JSON response.
    }
    throw new ApiError(message, response.status);
  }
  return (await response.json()) as T;
}

export function fetchSite(signal?: AbortSignal): Promise<SiteView> {
  return getJson<SiteView>("/api/v2/site", signal);
}

export function fetchPage(page: string, signal?: AbortSignal): Promise<PageView> {
  return getJson<PageView>(`/api/v2/pages/${encodeURIComponent(page)}`, signal);
}

export function fetchStrategy(strategyId: string, signal?: AbortSignal): Promise<PageView> {
  return getJson<PageView>(`/api/v2/strategies/${encodeURIComponent(strategyId)}`, signal);
}

export function fetchExamplePage(exampleId: string, signal?: AbortSignal): Promise<PageView> {
  return getJson<PageView>(`/api/v2/examples/${encodeURIComponent(exampleId)}`, signal);
}

export function fetchProofRun(
  proofRunId: string,
  signal?: AbortSignal,
): Promise<HypostructureProofRun> {
  return getJson<HypostructureProofRun>(
    `/api/v2/proof-runs/${encodeURIComponent(proofRunId)}`,
    signal,
  );
}

export function fetchModule(moduleId: string, signal?: AbortSignal): Promise<PageView> {
  return getJson<PageView>(`/api/v2/reference/modules/${encodeURIComponent(moduleId)}`, signal);
}

export function fetchDeclaration(declarationId: string, signal?: AbortSignal): Promise<PageView> {
  return getJson<PageView>(
    `/api/v2/reference/declarations/${encodeURIComponent(declarationId)}`,
    signal,
  );
}

export function fetchSearch(parameters: URLSearchParams, signal?: AbortSignal): Promise<SearchView> {
  const query = parameters.toString();
  return getJson<SearchView>(`/api/v2/search${query ? `?${query}` : ""}`, signal);
}

export function fetchSourceExcerpt(
  sourceId: string,
  range: { start?: string | null; end?: string | null } = {},
  signal?: AbortSignal,
): Promise<SourceExcerptView> {
  const query = new URLSearchParams();
  if (range.start) query.set("start", range.start);
  if (range.end) query.set("end", range.end);
  const suffix = query.size > 0 ? `?${query.toString()}` : "";
  return getJson<SourceExcerptView>(
    `/api/v2/sources/${encodeURIComponent(sourceId)}/excerpt${suffix}`,
    signal,
  );
}
