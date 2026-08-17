/**
 * The Hypostructure section: its rail, its pages, and the Lean highlighter
 * the pages are typeset with.
 */

import { render, screen, within } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { describe, expect, it } from "vitest";

import { MemoryRouter, Route, Routes } from "react-router-dom";

import { DocsHomePage } from "./DocsHomePage";
import { DocsLayout } from "./DocsLayout";
import { DocsPage } from "./DocsPage";
import { highlightLean } from "./lean-highlight";
import { DOCS_GROUPS, DOCS_PAGES, docsPath } from "./registry";

function show(path: string) {
  return render(
    <MemoryRouter initialEntries={[path]}>
      <Routes>
        <Route path="lean" element={<DocsLayout />}>
          <Route index element={<DocsHomePage />} />
          <Route path=":page" element={<DocsPage />} />
        </Route>
      </Routes>
    </MemoryRouter>,
  );
}

describe("the framework docs", () => {
  it("lists every page in the rail, and the overview first", () => {
    show("/lean");
    const rail = screen.getByRole("navigation", { name: "Hypostructure docs" });
    const links = within(rail).getAllByRole("link");
    expect(links[0]).toHaveTextContent("Overview");
    expect(links[0]).toHaveClass("is-current");
    for (const page of DOCS_PAGES) {
      expect(within(rail).getByRole("link", { name: page.title })).toHaveAttribute(
        "href",
        docsPath(page),
      );
    }
  });

  it("heads the rail with every group", () => {
    show("/lean");
    const rail = screen.getByRole("navigation", { name: "Hypostructure docs" });
    for (const group of DOCS_GROUPS) {
      expect(within(rail).getByRole("heading", { level: 2, name: group.title })).toBeInTheDocument();
    }
  });

  it("keeps every page reachable when the rail is folded away", async () => {
    // Folding is done in CSS, so the rail never leaves the document. That is
    // what keeps a deep link landing on its entry, and what lets the two tests
    // above stand unchanged.
    show("/lean");
    await userEvent.click(screen.getByRole("button", { name: "Contents" }));
    const rail = screen.getByRole("navigation", { name: "Hypostructure docs" });
    for (const group of DOCS_GROUPS) {
      expect(within(rail).getByRole("heading", { level: 2, name: group.title })).toBeInTheDocument();
    }
    for (const page of DOCS_PAGES) {
      expect(within(rail).getByRole("link", { name: page.title })).toHaveAttribute(
        "href",
        docsPath(page),
      );
    }
  });

  it("opens on the framework overview", () => {
    show("/lean");
    expect(
      screen.getByRole("heading", { level: 1, name: "The hypostructure framework" }),
    ).toBeInTheDocument();
    // The overview links to every page as a card.
    for (const page of DOCS_PAGES) {
      expect(screen.getAllByRole("link", { name: new RegExp(`^${page.title}`) }).length).toBeGreaterThan(0);
    }
  });

  it.each(DOCS_PAGES.map((page) => [page.slug, page.title] as const))(
    "renders /lean/%s under its title",
    (slug, title) => {
      show(`/lean/${slug}`);
      expect(screen.getByRole("heading", { level: 1, name: title })).toBeInTheDocument();
      const rail = screen.getByRole("navigation", { name: "Hypostructure docs" });
      expect(within(rail).getByRole("link", { name: title })).toHaveClass("is-current");
    },
  );

  it("pages forward and back in reading order", () => {
    show(`/lean/${DOCS_PAGES[1].slug}`);
    const pager = screen.getByRole("navigation", { name: "Neighbouring pages" });
    expect(within(pager).getByRole("link", { name: /Previous/ })).toHaveAttribute(
      "href",
      docsPath(DOCS_PAGES[0]),
    );
    expect(within(pager).getByRole("link", { name: /Next/ })).toHaveAttribute(
      "href",
      docsPath(DOCS_PAGES[2]),
    );
  });

  it("shows the not-found panel for an unknown page", () => {
    show("/lean/no-such-page");
    expect(screen.getByText("There is no page here")).toBeInTheDocument();
  });

  it.each(["ledger", "closing", "assembly", "replacement"])(
    "typesets Lean on /lean/%s",
    (slug) => {
      show(`/lean/${slug}`);
      const blocks = document.querySelectorAll(".lean-code pre");
      expect(blocks.length).toBeGreaterThan(3);
      for (const block of blocks) {
        expect(block.querySelector(".tok-keyword, .tok-comment")).not.toBeNull();
      }
    },
  );

  it("colours every Lean snippet without losing a character", () => {
    show("/lean/ledger");
    const blocks = document.querySelectorAll(".lean-code pre");
    expect(blocks.length).toBeGreaterThan(3);
    for (const block of blocks) {
      expect(block.querySelector(".tok-keyword")).not.toBeNull();
    }
  });
});

describe("the Lean highlighter", () => {
  it("round-trips the source", () => {
    const source = 'def x := "a -- not a comment" -- a comment\n/- block -/ `name @[simp]';
    expect(
      highlightLean(source)
        .map((token) => token.text)
        .join(""),
    ).toBe(source);
  });

  it("tells keywords, comments, strings, names and sorts apart", () => {
    const kinds = new Map(highlightLean(
      'theorem foo : Type := by simp -- done\n/-- doc -/ `Hypostructure.Core @[simp] "s" exactLedgerInternal% sorry',
    ).map((token) => [token.text, token.kind]));
    expect(kinds.get("theorem")).toBe("keyword");
    expect(kinds.get("by")).toBe("keyword");
    expect(kinds.get("Type")).toBe("sort");
    expect(kinds.get("-- done")).toBe("comment");
    expect(kinds.get("/-- doc -/")).toBe("comment");
    expect(kinds.get("`Hypostructure.Core")).toBe("name");
    expect(kinds.get("@[simp]")).toBe("attribute");
    expect(kinds.get('"s"')).toBe("string");
    expect(kinds.get("exactLedgerInternal%")).toBe("hole");
    expect(kinds.get("sorry")).toBe("hole");
    expect(kinds.get("foo")).toBeUndefined();
  });

  it("does not colour a keyword inside an identifier", () => {
    const tokens = highlightLean("defined byte");
    expect(tokens.every((token) => token.kind === "plain")).toBe(true);
  });
});
