/**
 * The header: which sections it offers, and that each proof's manuscripts can
 * be downloaded from it.
 */

import { existsSync, readFileSync } from "node:fs";
import { resolve } from "node:path";

import { render, screen, within } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { describe, expect, it } from "vitest";

import { MemoryRouter, Route, Routes } from "react-router-dom";

import { PROOFS, findProof, paperUrl } from "../proofs/registry";
import { AppShell } from "./AppShell";

function show(path: string) {
  return render(
    <MemoryRouter initialEntries={[path]}>
      <Routes>
        <Route element={<AppShell />}>
          <Route index element={<p>home</p>} />
          <Route path="lean" element={<p>docs</p>} />
          <Route path=":proof" element={<p>overview</p>} />
        </Route>
      </Routes>
    </MemoryRouter>,
  );
}

describe("the header", () => {
  it("shows no sections and no downloads on the landing page", () => {
    show("/");
    expect(screen.queryByRole("navigation", { name: "Sections" })).toBeNull();
    expect(screen.queryByText(/Download the paper/)).toBeNull();
  });

  it("offers the Lean Framework from every page", () => {
    show("/");
    expect(screen.getByRole("link", { name: "Lean Framework" })).toHaveAttribute("href", "/lean");
    show("/erdos-gyarfas");
    expect(screen.getAllByRole("link", { name: "Lean Framework" }).length).toBeGreaterThan(0);
  });

  it("offers the methodology from every page, pointing at the landing page", () => {
    show("/erdos-gyarfas");
    expect(screen.getByRole("link", { name: "Methodology" })).toHaveAttribute("href", "/");
    show("/lean");
    expect(screen.getAllByRole("link", { name: "Methodology" }).length).toBeGreaterThan(0);
  });

  it("shows no proof sections on the framework docs", () => {
    show("/lean");
    expect(screen.queryByRole("navigation", { name: "Sections" })).toBeNull();
    expect(screen.getByRole("link", { name: "Lean Framework" })).toHaveClass("active");
  });

  it("offers the Erdos-Gyarfas manuscript as one download", () => {
    show("/erdos-gyarfas");
    const proof = findProof("erdos-gyarfas")!;
    const sections = screen.getByRole("navigation", { name: "Sections" });
    const link = within(sections).getByRole("link", { name: "Download the paper" });
    expect(link).toHaveAttribute("href", paperUrl(proof.papers[0]));
    expect(link).toHaveAttribute("download");
  });

  it("offers the three Navier-Stokes manuscripts as a menu", () => {
    show("/navier-stokes");
    const proof = findProof("navier-stokes")!;
    const sections = screen.getByRole("navigation", { name: "Sections" });
    expect(within(sections).getByText("Download the papers")).toBeInTheDocument();
    for (const paper of proof.papers) {
      const link = within(sections).getByRole("link", { name: new RegExp(`^${paper.title}`) });
      expect(link).toHaveAttribute("href", paperUrl(paper));
      expect(link).toHaveAttribute("download");
    }
  });

  it("closes the menu on a click elsewhere or on Escape", async () => {
    show("/navier-stokes");
    const user = userEvent.setup();
    const menu = document.querySelector("details.paper-downloads") as HTMLDetailsElement;
    await user.click(screen.getByText("Download the papers"));
    expect(menu.open).toBe(true);
    await user.click(document.body);
    expect(menu.open).toBe(false);
    await user.click(screen.getByText("Download the papers"));
    expect(menu.open).toBe(true);
    await user.keyboard("{Escape}");
    expect(menu.open).toBe(false);
  });

  it("names a file that is really served, for every paper of every proof", () => {
    for (const proof of PROOFS) {
      expect(proof.papers.length).toBeGreaterThan(0);
      for (const paper of proof.papers) {
        // Resolved from the Vitest root (web/frontend).
        const path = resolve(process.cwd(), "public", "papers", paper.file);
        expect(existsSync(path), `${paper.file} is missing from public/papers/`).toBe(true);
        expect(readFileSync(path).subarray(0, 5).toString()).toBe("%PDF-");
      }
    }
  });
});
