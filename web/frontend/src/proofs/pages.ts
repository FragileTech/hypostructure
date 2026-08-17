import type { ChapterSource, LabelLocation } from "../graph-explorer";
import { pageMapUrl, paperUrl, type PaperFile, type ProofEntry } from "./registry";

/** The shape `web/tools/extract_page_map.py` writes, one file per PDF. */
interface PageMapFile {
  pdf: string;
  tex: string;
  chapter: string;
  pages: number;
  labels: Record<string, LabelLocation>;
}

const pending = new Map<string, Promise<ChapterSource>>();

function loadPageMap(paper: PaperFile): Promise<ChapterSource> {
  const existing = pending.get(paper.file);
  if (existing) return existing;

  const request = fetch(pageMapUrl(paper)).then(async (response) => {
    if (!response.ok) {
      throw new Error(
        `Could not load the page map of ${paper.file} (${response.status} ${response.statusText}).`,
      );
    }
    const file = (await response.json()) as PageMapFile;
    return { title: paper.title, url: paperUrl(paper), pages: file.pages, labels: file.labels };
  });
  pending.set(paper.file, request);
  return request;
}

/**
 * The manuscripts of a proof as the reader can open them, keyed by chapter id.
 *
 * A manuscript whose page map cannot be fetched is left out rather than failing
 * the proof: the explorer then falls back to naming the source line.
 */
export async function loadProofSources(proof: ProofEntry): Promise<Record<string, ChapterSource>> {
  const sources: Record<string, ChapterSource> = {};
  await Promise.all(
    proof.papers.map(async (paper) => {
      try {
        sources[paper.chapter] = await loadPageMap(paper);
      } catch (error) {
        console.warn(error);
      }
    }),
  );
  return sources;
}
