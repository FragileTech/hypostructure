import type { ChapterSource, LabelLocation, ProofGraphDocument } from "./types";

/** Where a result or display can be read in its manuscript's PDF. */
export interface SourceLocation {
  /** How the host names the PDF. */
  title: string;
  page: number;
  /** URL that opens the PDF at that page. */
  url: string;
  location: LabelLocation;
}

/**
 * The page a labelled record — a result, an equation — is stated on, when the
 * host supplied the manuscripts' page maps. `key` may carry a chapter prefix
 * (`setup/thm:main`); the maps are keyed by the label as the paper writes it.
 */
export function locate(
  document: Pick<ProofGraphDocument, "sources" | "slug">,
  chapter: string | undefined,
  key: string,
): SourceLocation | undefined {
  const source: ChapterSource | undefined = document.sources?.[chapter ?? document.slug];
  if (!source) return undefined;
  const location = source.labels[key.replace(/^.*?\//, "")];
  if (!location?.page) return undefined;
  return {
    title: source.title,
    page: location.page,
    url: `${source.url}#page=${location.page}`,
    location,
  };
}
