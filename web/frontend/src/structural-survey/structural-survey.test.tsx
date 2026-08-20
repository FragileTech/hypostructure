import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import { render, screen, within } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { MemoryRouter, useLocation } from "react-router-dom";
import { describe, expect, it } from "vitest";

import { MathProvider } from "../graph-explorer/Latex";
import { indexDocument } from "../graph-explorer/index-document";
import { locate } from "../graph-explorer/locate";
import type { ChapterSource, ProofGraphDocument } from "../graph-explorer/types";
import { PROOFS, paperUrl } from "../proofs/registry";
import { EGStructuralSurvey } from "./EGStructuralSurvey";
import { GeneralStructuralSurvey } from "./GeneralStructuralSurvey";
import {
  ALL_STRUCTURAL_PROPERTIES,
  EG_INVARIANT_BINDINGS,
  STRUCTURAL_SURVEY_PART_ANCHOR,
  STRUCTURAL_PROPERTY_GROUPS,
  STRUCTURAL_TECHNIQUES,
  propertyAnchor,
  techniqueAnchor,
} from "./data";

function readJson<T>(path: string): T {
  return JSON.parse(readFileSync(resolve(process.cwd(), "public", path), "utf8")) as T;
}

function loadEG(): ProofGraphDocument {
  const proof = PROOFS.find((candidate) => candidate.slug === "erdos-gyarfas")!;
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

const ERDOS = loadEG();

function LocationState() {
  const location = useLocation();
  return <output data-testid="location-state">{(location.state as { scrollTo?: string } | null)?.scrollTo}</output>;
}

describe("the problem-independent structural survey", () => {
  it("has 19 techniques and 88 unique atomic properties in nine groups", () => {
    expect(STRUCTURAL_TECHNIQUES).toHaveLength(19);
    expect(STRUCTURAL_PROPERTY_GROUPS).toHaveLength(9);
    expect(ALL_STRUCTURAL_PROPERTIES).toHaveLength(88);

    expect(new Set(STRUCTURAL_TECHNIQUES.map((technique) => technique.id))).toHaveLength(19);
    expect(new Set(ALL_STRUCTURAL_PROPERTIES.map((property) => property.id))).toHaveLength(88);
  });

  it("uses only registered techniques and gives every technique something to evaluate", () => {
    const techniqueIds = new Set(STRUCTURAL_TECHNIQUES.map((technique) => technique.id));
    const used = new Set<string>();
    for (const property of ALL_STRUCTURAL_PROPERTIES) {
      expect(property.techniques.length, property.id).toBeGreaterThan(0);
      for (const technique of property.techniques) {
        expect(techniqueIds.has(technique), `${property.id} refers to ${technique}`).toBe(true);
        used.add(technique);
      }
    }
    expect(used).toEqual(techniqueIds);
  });

  it("renders the technique register and all nine structural registers", () => {
    const { container } = render(<GeneralStructuralSurvey />);
    const tables = screen.getAllByRole("table");
    expect(tables).toHaveLength(10);
    expect(within(tables[0]).getAllByRole("row")).toHaveLength(20);
    expect(container.querySelectorAll(".survey-property-table tbody tr")).toHaveLength(88);

    for (const technique of STRUCTURAL_TECHNIQUES) {
      expect(document.getElementById(techniqueAnchor(technique.id))).not.toBeNull();
    }
    for (const property of ALL_STRUCTURAL_PROPERTIES) {
      expect(document.getElementById(propertyAnchor(property.id))).not.toBeNull();
    }
  });
});

describe("the Erdős–Gyárfás structural crosswalk", () => {
  it("maps every one of the paper's 38 invariants to real general coordinates", () => {
    expect(ERDOS.invariants).toHaveLength(38);
    expect(EG_INVARIANT_BINDINGS).toHaveLength(38);
    expect(EG_INVARIANT_BINDINGS.map((binding) => binding.number)).toEqual(
      Array.from({ length: 38 }, (_, index) => index + 1),
    );

    const propertyIds = new Set(ALL_STRUCTURAL_PROPERTIES.map((property) => property.id));
    const techniqueIds = new Set(STRUCTURAL_TECHNIQUES.map((technique) => technique.id));
    for (const binding of EG_INVARIANT_BINDINGS) {
      expect(binding.propertyIds.length, `invariant ${binding.number}`).toBeGreaterThan(0);
      expect(binding.techniqueIds.length, `invariant ${binding.number}`).toBeGreaterThan(0);
      for (const property of binding.propertyIds) expect(propertyIds.has(property)).toBe(true);
      for (const technique of binding.techniqueIds) expect(techniqueIds.has(technique)).toBe(true);
    }
  });

  it("resolves every mapped node, implementing result, and dynamic PDF page", () => {
    const index = indexDocument(ERDOS);
    const invariantByNumber = new Map(
      ERDOS.invariants.map((invariant) => [invariant.number, invariant]),
    );

    for (const binding of EG_INVARIANT_BINDINGS) {
      const invariant = invariantByNumber.get(binding.number);
      const item = index.itemByKey.get(binding.primaryItem);
      expect(invariant, `missing invariant ${binding.number}`).toBeDefined();
      expect(item, `missing ${binding.primaryItem}`).toBeDefined();
      expect(["theorem", "proposition", "lemma", "corollary"]).toContain(item!.kind);
      for (const node of invariant!.nodes) {
        expect(index.nodeById.has(node), `invariant ${binding.number} names node ${node}`).toBe(true);
      }
      const where = locate(ERDOS, item!.chapter, item!.key);
      expect(where, `no PDF page for ${item!.key}`).toBeDefined();
      expect(where!.location.number, `no printed result number for ${item!.key}`).not.toBeNull();
    }
  });

  it("renders a six-column, 38-row ledger with live destinations", () => {
    const { container } = render(
      <MemoryRouter>
        <MathProvider macros={ERDOS.macros}>
          <EGStructuralSurvey document={ERDOS} />
        </MathProvider>
      </MemoryRouter>,
    );

    const table = screen.getByRole("table");
    expect(within(table).getAllByRole("columnheader").map((header) => header.textContent)).toEqual([
      "EG invariant",
      "General structure",
      "Technique",
      "Nodes",
      "Implementing result",
      "Page",
    ]);

    const rows = within(table).getAllByRole("row").slice(1);
    expect(rows).toHaveLength(38);
    const index = indexDocument(ERDOS);
    rows.forEach((row, rowIndex) => {
      expect(row.querySelectorAll(":scope > th, :scope > td")).toHaveLength(6);
      expect(row.querySelector("td:nth-child(2) a.survey-coordinate.is-property")).toHaveAttribute(
        "href",
        "/",
      );
      expect(row.querySelector("td:nth-child(3) a.survey-coordinate.is-technique")).toHaveAttribute(
        "href",
        "/",
      );
      expect(row.querySelector("td:nth-child(4) a.chip-node")).not.toBeNull();
      const binding = EG_INVARIANT_BINDINGS[rowIndex];
      const item = index.itemByKey.get(binding.primaryItem)!;
      const where = locate(ERDOS, item.chapter, item.key)!;
      expect(row.querySelector("td:nth-child(5) > a[target='_blank']")).toHaveAttribute(
        "href",
        where.url,
      );
      expect(row.querySelector("td:nth-child(5)")).toHaveTextContent(where.location.number!);
      expect(row.querySelector("td:nth-child(6) > a[target='_blank']")).toHaveAttribute(
        "href",
        where.url,
      );
      expect(row.querySelector("td:nth-child(6)")).toHaveTextContent(`p. ${where.page}`);
    });

    expect(container.querySelectorAll("details.eg-survey-more").length).toBeGreaterThan(0);
    for (const link of container.querySelectorAll<HTMLAnchorElement>(".eg-survey-more li > a")) {
      expect(link.getAttribute("href")).toMatch(/\.pdf#page=\d+$/);
    }

    for (const link of container.querySelectorAll<HTMLAnchorElement>(".eg-survey-nodes a")) {
      const id = link.textContent!;
      expect(link.getAttribute("href")).toBe(
        `/erdos-gyarfas/explore?step=${encodeURIComponent(id)}`,
      );
    }
  });

  it("links its coordinates back to the exact rows of the general methodology", async () => {
    const user = userEvent.setup();
    const { container } = render(
      <MemoryRouter initialEntries={["/erdos-gyarfas"]}>
        <MathProvider macros={ERDOS.macros}>
          <EGStructuralSurvey document={ERDOS} />
        </MathProvider>
        <LocationState />
      </MemoryRouter>,
    );

    await user.click(container.querySelector<HTMLAnchorElement>(".panel-lead > a")!);
    expect(screen.getByTestId("location-state")).toHaveTextContent(STRUCTURAL_SURVEY_PART_ANCHOR);

    await user.click(container.querySelector<HTMLAnchorElement>("a.survey-coordinate.is-property")!);
    expect(screen.getByTestId("location-state")).toHaveTextContent(propertyAnchor("C02"));

    await user.click(container.querySelector<HTMLAnchorElement>("a.survey-coordinate.is-technique")!);
    expect(screen.getByTestId("location-state")).toHaveTextContent(techniqueAnchor("T08"));
  });

  it("does not add an EG ledger to another proof", () => {
    const other = { ...ERDOS, slug: "navier-stokes" };
    const { container } = render(<EGStructuralSurvey document={other} />);
    expect(container).toBeEmptyDOMElement();
  });
});
