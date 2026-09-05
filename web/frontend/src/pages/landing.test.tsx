/**
 * The landing page: the proof cards, and the account of the method behind
 * both proofs.
 */

import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import { fireEvent, render, screen, within } from "@testing-library/react";
import { describe, expect, it } from "vitest";

import { MemoryRouter } from "react-router-dom";

import { METHODOLOGY_PARTS, methodologySectionPath, partAnchor } from "../components/MethodologySection";
import { PROOFS } from "../proofs/registry";
import { ALL_STRUCTURAL_PROPERTIES, STRUCTURAL_TECHNIQUES } from "../structural-survey/data";
import { LandingPage } from "./LandingPage";

function show(initialEntry = "/") {
  return render(
    <MemoryRouter initialEntries={[initialEntry]}>
      <LandingPage />
    </MemoryRouter>,
  );
}

describe("the landing page", () => {
  it("offers every proof", () => {
    show();
    for (const proof of PROOFS) {
      expect(screen.getByRole("heading", { level: 2, name: proof.name })).toBeInTheDocument();
    }
  });

  it("points at the Hypostructure docs", () => {
    show();
    expect(screen.getByRole("link", { name: "Read the docs" })).toHaveAttribute("href", "/lean");
    expect(screen.getByRole("heading", { level: 2, name: "Hypostructure" })).toBeInTheDocument();
  });

  it("presents the methodology under its own heading", () => {
    show();
    const section = document.getElementById("methodology");
    expect(section).not.toBeNull();
    expect(within(section!).getByText("The methodology")).toBeInTheDocument();
    expect(
      within(section!).getByRole("heading", { level: 2, name: "Structural Exhaustion" }),
    ).toBeInTheDocument();
  });

  it("walks the six stages of one iteration, in order", () => {
    show();
    const section = document.getElementById(partAnchor("iteration"))!;
    const stages = within(section)
      .getAllByRole("listitem")
      .map((item) => item.querySelector("strong")?.textContent)
      .filter((name): name is string => Boolean(name));
    expect(stages).toEqual(["Propose", "Admit", "Select", "Execute", "Route", "Record"]);
  });

  it("opens with the three ways a counterexample pays", () => {
    show();
    const opening = document.getElementById(partAnchor("philosophy"))!;
    const costs = Array.from(opening.querySelectorAll("dt")).map((dt) => dt.textContent);
    expect(costs).toEqual(["Compression", "Quantity", "Constraint"]);
  });

  it("maps each working practice to the capability it leverages", () => {
    show();
    const part = document.getElementById(partAnchor("mechanisms"))!;
    const table = within(part).getByRole("table");
    const headers = within(table).getAllByRole("columnheader").map((h) => h.textContent);
    expect(headers).toEqual(["How the proof is built", "The capability it leverages"]);
    const rows = within(table).getAllByRole("row").slice(1);
    expect(rows.length).toBeGreaterThanOrEqual(6);
    for (const row of rows) expect(within(row).getAllByRole("cell")).toHaveLength(2);
  });

  it("explains each failure mode and the discipline that prevents it", () => {
    show();
    const part = document.getElementById(partAnchor("controls"))!;
    const controls = Array.from(part.querySelectorAll("dt")).map((dt) => dt.textContent);
    expect(controls).toEqual([
      "Lost forward tracking",
      "Extrapolation beyond standard material",
      "Omitted difficult steps",
      "Unsupported global estimates",
      "Re-encoding the difficulty",
      "Untyped residuals",
      "Deferential agreement with erroneous steps",
      "Status-cue audit drift",
    ]);
    // Each entry says what the failure is, then how it is avoided.
    for (const entry of part.querySelectorAll("dd")) {
      const labels = Array.from(entry.querySelectorAll("em")).map((em) => em.textContent);
      expect(labels).toEqual(["The failure.", "The discipline."]);
    }
  });

  it("describes the chapter-1 artifacts, each with what it records and why it helps", () => {
    show();
    const part = document.getElementById(partAnchor("artifacts"))!;
    const artifacts = Array.from(part.querySelectorAll("dt")).map((dt) => dt.textContent);
    expect(artifacts).toEqual([
      "The proof-dependency diagram",
      "The diagram map and the node-by-node audit table",
      "The constraint ledger",
      "The per-result requirement table",
      "The branch-closure audit ledger",
      "Notation, constants and the diagram legend",
    ]);
    for (const entry of part.querySelectorAll("dd")) {
      const labels = Array.from(entry.querySelectorAll("em")).map((em) => em.textContent);
      expect(labels).toHaveLength(2);
      expect(labels[0]).toMatch(/^What (it|they) records?\.$/);
      expect(labels[1]).toMatch(/^Why (it|they) helps?\.$/);
    }
  });

  it("lists every proof move with its Erdos-Gyarfas and Navier-Stokes realisation", () => {
    show();
    const part = document.getElementById(partAnchor("moves"))!;
    const table = within(part).getByRole("table");
    const headers = within(table).getAllByRole("columnheader").map((h) => h.textContent);
    expect(headers).toEqual(["Move", "What it does", "In Erdős–Gyárfás", "In Navier–Stokes"]);
    const rows = within(table).getAllByRole("row").slice(1);
    expect(rows).toHaveLength(21);
    const names = rows.map((row) => row.querySelector("strong")?.textContent);
    expect(names).toEqual([
      "Local target tests",
      "Minimality and replacement",
      "External-type compression",
      "Charging schemes",
      "Local-to-global bookkeeping",
      "Active/dormant dichotomy",
      "Exchange trichotomy",
      "Finite-state pumping",
      "Overload exhaustion",
      "Default refinement",
      "Localization",
      "Peeling loop",
      "Tiered charging",
      "Aggregate closure",
      "Rank forcing",
      "Whole-object exact types",
      "Target thickening",
      "Limit extraction and transport back",
      "Symmetry fixing and gauge repair",
      "Rigidity closure by a fixed input",
      "Monotone quantity along scale",
    ]);
    for (const row of rows) {
      const cells = within(row).getAllByRole("cell");
      expect(cells).toHaveLength(4);
      expect(cells[0].textContent?.trim().length).toBeGreaterThan(0);
      for (const cell of cells.slice(1)) expect(cell.textContent?.trim().length).toBeGreaterThan(20);
    }
  });

  it("links every step it names to a real one, in the right proof", () => {
    show();
    const section = document.getElementById("methodology")!;
    const part = document.getElementById(partAnchor("moves"))!;
    const table = within(part).getByRole("table");
    const rows = within(table).getAllByRole("row");

    const known: Record<string, Set<string>> = {};
    for (const proof of PROOFS) {
      const raw = readFileSync(resolve(process.cwd(), "public", "data", `${proof.slug}.json`), "utf8");
      known[proof.slug] = new Set((JSON.parse(raw).nodes as { id: string }[]).map((n) => n.id));
    }
    const links = Array.from(section.querySelectorAll("a.chip-node"));
    expect(links.length).toBeGreaterThan(80);
    for (const link of links) {
      const match = link.getAttribute("href")!.match(/^\/(erdos-gyarfas|navier-stokes)\/explore\?step=(.+)$/);
      expect(match, link.getAttribute("href") ?? "").not.toBeNull();
      const [, slug, id] = match!;
      expect(known[slug].has(id), `${slug} has no step ${id}`).toBe(true);
      expect(link.textContent).toBe(id);
    }
    // Every move is used somewhere in at least one proof.
    for (const row of rows.slice(1)) {
      expect(row.querySelectorAll("a.chip-node").length).toBeGreaterThan(0);
    }
  });

  it("shows how a failed step is repaired, with three worked repairs", () => {
    show();
    const part = document.getElementById(partAnchor("repair"))!;
    const figure = part.querySelector("svg[role='img']")!;
    expect(figure).not.toBeNull();
    expect(figure.querySelector("title")?.textContent).toMatch(/repaired/);
    const kinds = Array.from(part.querySelectorAll("dt")).map((dt) => dt.textContent);
    expect(kinds).toEqual([
      "A compactness claim on too small a state",
      "An estimate missing a hypothesis",
      "A budget used outside its regime",
    ]);
    for (const entry of part.querySelectorAll("dd")) {
      const labels = Array.from(entry.querySelectorAll("p > em:first-child")).map((em) => em.textContent);
      expect(labels).toEqual([
        "What red-teaming found.",
        "The hypothesis it exposed.",
        "The repair.",
        "What was left untouched.",
      ]);
      expect(entry.querySelectorAll("a.chip-node").length).toBeGreaterThan(3);
    }
  });

  it("does not use the retired tactic name", () => {
    show();
    expect(document.body.textContent).not.toMatch(/\bCT1\b|CT1–CT17|CT17/);
  });

  it("links each case study to its proof", () => {
    show();
    const section = document.getElementById("methodology")!;
    for (const proof of PROOFS) {
      const link = within(section).getByRole("link", { name: new RegExp(proof.name) });
      expect(link).toHaveAttribute("href", `/${proof.slug}`);
    }
  });

  it("ends with the problem-independent technique and invariant registers", () => {
    show();
    const proofCases = document.getElementById(partAnchor("proofs"))!;
    const survey = document.getElementById(partAnchor("survey"))!;
    expect(
      proofCases.compareDocumentPosition(survey) & Node.DOCUMENT_POSITION_FOLLOWING,
    ).toBeTruthy();
    expect(within(survey).getByText(/These 88 coordinates exhaust/)).toBeInTheDocument();
    expect(survey.querySelectorAll(".survey-technique-table tbody tr")).toHaveLength(
      STRUCTURAL_TECHNIQUES.length,
    );
    expect(survey.querySelectorAll(".survey-property-table tbody tr")).toHaveLength(
      ALL_STRUCTURAL_PROPERTIES.length,
    );
  });

  it("renders every piece of its mathematics", () => {
    show();
    const section = document.getElementById("methodology")!;
    expect(section.querySelectorAll(".katex").length).toBeGreaterThan(10);
    expect(section.querySelectorAll(".katex-error")).toHaveLength(0);
    // The display equations are there as displays, not folded into the prose.
    expect(section.querySelectorAll(".katex-display").length).toBeGreaterThanOrEqual(3);
  });

  it("has a rail naming every part of the methodology, in order", () => {
    show();
    const rail = screen.getByRole("navigation", { name: "The methodology" });
    const names = within(rail)
      .getAllByRole("link")
      .map((button) => button.textContent);
    expect(names).toEqual(METHODOLOGY_PARTS.map((part) => part.title));
    // Every rail entry has a part to land on, headed by the same title.
    for (const part of METHODOLOGY_PARTS) {
      const target = document.getElementById(partAnchor(part.id));
      expect(target, part.id).not.toBeNull();
      const level = "parent" in part ? 4 : 3;
      const heading = target!.querySelector(`h${level}`);
      expect(heading, part.id + " heading").not.toBeNull();
      expect(heading).toHaveTextContent(part.title);
      expect(within(rail).getByRole("link", { name: part.title })).toHaveAttribute(
        "href",
        methodologySectionPath(part.id),
      );
      if ("parent" in part) {
        // A subsection sits inside its parent's article and after its heading.
        expect(document.getElementById(partAnchor(part.parent))!.contains(target)).toBe(true);
      }
    }
  });

  it("opens with the philosophy and its three currencies, then the language-model design", () => {
    show();
    const order = METHODOLOGY_PARTS.map((part) => document.getElementById(partAnchor(part.id))!);
    for (let index = 1; index < order.length; index += 1) {
      // Document order follows reading order.
      expect(order[index - 1].compareDocumentPosition(order[index]) & Node.DOCUMENT_POSITION_FOLLOWING).toBeTruthy();
    }
    const ids = METHODOLOGY_PARTS.map((part) => part.id);
    expect(ids.slice(0, 7)).toEqual([
      "philosophy",
      "constraint",
      "quantity",
      "compression",
      "llm",
      "mechanisms",
      "controls",
    ]);
    const rail = screen.getByRole("navigation", { name: "The methodology" });
    // Subsections are nested under their parent in the rail.
    const nested = Array.from(rail.querySelectorAll("ul ul a")).map((b) => b.textContent);
    expect(nested).toEqual(
      METHODOLOGY_PARTS.filter((part) => "parent" in part).map((part) => part.title),
    );
  });

  it("scrolls to a part from its rail entry, and marks exactly one part current", () => {
    show();
    const rail = screen.getByRole("navigation", { name: "The methodology" });
    const buttons = within(rail).getAllByRole("link");
    // jsdom lays nothing out, so which part is current is not meaningful here;
    // that there is always one is.
    const current = buttons.filter((button) => button.classList.contains("is-current"));
    expect(current).toHaveLength(1);
    expect(current[0]).toHaveAttribute("aria-current", "true");

    const target = document.getElementById(partAnchor("quantity"))!;
    let scrolled = false;
    target.scrollIntoView = () => {
      scrolled = true;
    };
    fireEvent.click(within(rail).getByRole("link", { name: "Cost as quantity: structural accounting" }));
    expect(scrolled).toBe(true);
  });

  it("opens a methodology section from its direct URL", () => {
    let scrolled = false;
    const originalScrollIntoView = Element.prototype.scrollIntoView;
    Element.prototype.scrollIntoView = () => {
      scrolled = true;
    };
    try {
      show(methodologySectionPath("recipe-execute"));
      expect(document.getElementById(partAnchor("recipe-execute"))).not.toBeNull();
      expect(scrolled).toBe(true);
    } finally {
      Element.prototype.scrollIntoView = originalScrollIntoView;
    }
  });

  it("can jump from the hero to the methodology", () => {
    show();
    const target = document.getElementById("methodology")!;
    let scrolled = false;
    target.scrollIntoView = () => {
      scrolled = true;
    };
    screen.getByRole("button", { name: "Read the methodology" }).click();
    expect(scrolled).toBe(true);
  });
});
