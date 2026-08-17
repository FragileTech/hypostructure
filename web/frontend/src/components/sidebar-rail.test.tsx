/**
 * The chrome around a table of contents: folding it away at a desk, and the
 * drawer it becomes on a phone.
 */

import { render, screen, within } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { afterEach, beforeEach, describe, expect, it } from "vitest";

import { MemoryRouter, NavLink, Route, Routes } from "react-router-dom";

import { railPageClass, useSidebar } from "../hooks/useSidebar";
import { SidebarRail } from "./SidebarRail";

const KEY = "test:sidebar-rail";
const PAGES = ["First", "Second", "Third"];

/** A stand-in for a page that carries a rail. */
function Harness() {
  const sidebar = useSidebar(KEY);
  return (
    <div data-testid="page" className={railPageClass("page", sidebar)}>
      <SidebarRail sidebar={sidebar} label="Test rail" id="test-rail" className="docs-rail">
        <h2>A group</h2>
        <ul>
          {PAGES.map((page) => (
            <li key={page}>
              <NavLink to={`/${page.toLowerCase()}`}>{page}</NavLink>
            </li>
          ))}
        </ul>
      </SidebarRail>
      <div>the article</div>
    </div>
  );
}

function show(path = "/first") {
  return render(
    <MemoryRouter initialEntries={[path]}>
      <Routes>
        <Route path="*" element={<Harness />} />
      </Routes>
    </MemoryRouter>,
  );
}

const original = Object.getOwnPropertyDescriptor(window, "matchMedia");

function stubMedia(matches: boolean) {
  Object.defineProperty(window, "matchMedia", {
    writable: true,
    configurable: true,
    value: (query: string) => ({
      media: query,
      matches,
      onchange: null,
      addEventListener() {},
      removeEventListener() {},
      addListener() {},
      removeListener() {},
      dispatchEvent: () => false,
    }),
  });
}

function toggle() {
  return screen.getByRole("button", { name: "Contents" });
}

describe("the collapsible rail", () => {
  beforeEach(() => {
    window.localStorage.clear();
    document.body.className = "";
    stubMedia(false);
  });

  afterEach(() => {
    if (original) Object.defineProperty(window, "matchMedia", original);
  });

  it("names the rail it controls", () => {
    show();
    const rail = screen.getByRole("navigation", { name: "Test rail" });
    expect(toggle()).toHaveAttribute("aria-expanded", "true");
    expect(toggle()).toHaveAttribute("aria-controls", rail.id);
  });

  it("folds the rail away at a desk", async () => {
    show();
    await userEvent.click(toggle());
    expect(toggle()).toHaveAttribute("aria-expanded", "false");
    expect(screen.getByTestId("page")).toHaveClass("is-rail-collapsed");
  });

  it("keeps every page of a folded rail addressable", async () => {
    // The fold is done in CSS, never by unmounting: the docs tests read the
    // rail's links straight out of the document, and a reader following a deep
    // link must still land on the right entry. Do not relax this.
    show();
    await userEvent.click(toggle());
    const rail = screen.getByRole("navigation", { name: "Test rail" });
    expect(within(rail).getByRole("heading", { level: 2, name: "A group" })).toBeInTheDocument();
    for (const page of PAGES) {
      expect(within(rail).getByRole("link", { name: page })).toBeInTheDocument();
    }
  });

  it("opens as a drawer on a phone, and takes focus with it", async () => {
    stubMedia(true);
    show();
    await userEvent.click(toggle());
    expect(screen.getByTestId("page")).toHaveClass("is-rail-open");
    expect(screen.getByRole("button", { name: "Close the contents" })).toHaveFocus();
  });

  it("closes the drawer on Escape, and hands focus back", async () => {
    stubMedia(true);
    show();
    await userEvent.click(toggle());
    await userEvent.keyboard("{Escape}");
    expect(screen.getByTestId("page")).not.toHaveClass("is-rail-open");
    expect(toggle()).toHaveFocus();
  });

  it("closes the drawer on its close button", async () => {
    stubMedia(true);
    show();
    await userEvent.click(toggle());
    await userEvent.click(screen.getByRole("button", { name: "Close the contents" }));
    expect(screen.getByTestId("page")).not.toHaveClass("is-rail-open");
  });

  it("closes the drawer when the page behind it is tapped", async () => {
    stubMedia(true);
    const { container } = show();
    await userEvent.click(toggle());
    const scrim = container.querySelector(".rail-scrim") as HTMLElement;
    await userEvent.click(scrim);
    expect(screen.getByTestId("page")).not.toHaveClass("is-rail-open");
  });

  it("gets out of the way once an entry is chosen", async () => {
    stubMedia(true);
    show();
    await userEvent.click(toggle());
    expect(screen.getByTestId("page")).toHaveClass("is-rail-open");
    await userEvent.click(screen.getByRole("link", { name: "Second" }));
    expect(screen.getByTestId("page")).not.toHaveClass("is-rail-open");
  });

  it("keeps the keyboard inside an open drawer", async () => {
    stubMedia(true);
    show();
    await userEvent.click(toggle());
    const close = screen.getByRole("button", { name: "Close the contents" });
    const last = screen.getByRole("link", { name: "Third" });

    last.focus();
    await userEvent.tab();
    expect(close).toHaveFocus();

    await userEvent.tab({ shift: true });
    expect(last).toHaveFocus();
  });

  it("does not trap the keyboard when there is no drawer", async () => {
    show();
    screen.getByRole("link", { name: "Third" }).focus();
    await userEvent.tab();
    expect(screen.getByRole("link", { name: "Third" })).not.toHaveFocus();
  });
});
