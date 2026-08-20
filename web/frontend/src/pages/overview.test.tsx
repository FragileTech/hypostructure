import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import { render, screen, within } from "@testing-library/react";
import { MemoryRouter } from "react-router-dom";
import { describe, expect, it, vi } from "vitest";

import type { ChapterSource, ProofGraphDocument } from "../graph-explorer";
import { findProof, paperUrl } from "../proofs/registry";

const hookState = vi.hoisted(() => ({
  proof: undefined as unknown,
  request: undefined as unknown,
}));

vi.mock("../hooks/useProof", () => ({ useProof: () => hookState.proof }));
vi.mock("../hooks/useProofDocument", () => ({ useProofDocument: () => hookState.request }));

import { OverviewPage } from "./OverviewPage";

function readJson<T>(path: string): T {
  return JSON.parse(readFileSync(resolve(process.cwd(), "public", path), "utf8")) as T;
}

function loadEG(): ProofGraphDocument {
  const proof = findProof("erdos-gyarfas")!;
  const document = readJson<ProofGraphDocument>(`data/${proof.slug}.json`);
  const sources: Record<string, ChapterSource> = {};
  for (const paper of proof.papers) {
    const map = readJson<ChapterSource>(`data/pages/${paper.file.replace(/\.pdf$/, "")}.json`);
    sources[paper.chapter] = {
      title: paper.title,
      url: paperUrl(paper),
      pages: map.pages,
      labels: map.labels,
    };
  }
  return { ...document, sources };
}

describe("the proof overview", () => {
  it("places the EG structural crosswalk immediately after the 12 panels", () => {
    const proof = findProof("erdos-gyarfas")!;
    hookState.proof = proof;
    hookState.request = { status: "ready", document: loadEG() };

    const { container } = render(
      <MemoryRouter initialEntries={["/erdos-gyarfas"]}>
        <OverviewPage />
      </MemoryRouter>,
    );

    const panels = screen.getByRole("heading", { level: 2, name: "The 12 panels" }).closest("section")!;
    const survey = screen
      .getByRole("heading", { level: 2, name: "Structural survey of the Erdős–Gyárfás proof" })
      .closest("section")!;
    const footer = container.querySelector(".page-footer")!;
    expect(panels.compareDocumentPosition(survey) & Node.DOCUMENT_POSITION_FOLLOWING).toBeTruthy();
    expect(survey.compareDocumentPosition(footer) & Node.DOCUMENT_POSITION_FOLLOWING).toBeTruthy();
    expect(within(survey).getAllByRole("row").slice(1)).toHaveLength(38);
  });
});
