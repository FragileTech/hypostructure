import { fireEvent, render, screen, waitFor } from "@testing-library/react";
import { MemoryRouter } from "react-router-dom";
import { afterEach, describe, expect, it, vi } from "vitest";

import App from "./App";
import { syntheticCertifiedProofRun } from "./test-proof-run";
import type { PageView, SiteView } from "./v2-types";

const site: SiteView = {
  name: "Hypostructure",
  tagline: "Verified proof architecture",
  navigation: [
    { label: "Problem", href: "/docs/problems" },
    { label: "DAG", href: "/docs/dags" },
    { label: "Strategies", href: "/strategies" },
  ],
  snapshot: "test-snapshot",
  searchEnabled: true,
  verification: { state: "verified", label: "Verified", summary: "Kernel checked" },
};

function page(id: string, title: string): PageView {
  return {
    id,
    title,
    eyebrow: "Hypostructure",
    summary: "A ready-to-render view model supplied by Flask.",
    sections: [
      {
        id: "overview",
        title: "Overview",
        blocks: [{ kind: "callout", tone: "trust", title: "Kernel checked", body: "Fresh evidence." }],
      },
    ],
  };
}

function json(value: unknown, status = 200): Response {
  return new Response(JSON.stringify(value), {
    status,
    headers: { "Content-Type": "application/json" },
  });
}

afterEach(() => vi.unstubAllGlobals());

describe("Hypostructure application", () => {
  it("renders the home page from the v2 page endpoint", async () => {
    const fetchMock = vi.fn((input: RequestInfo | URL) => {
      const path = String(input);
      if (path === "/api/v2/site") return Promise.resolve(json(site));
      if (path === "/api/v2/pages/home") return Promise.resolve(json(page("home", "Proofs as typed programs")));
      return Promise.resolve(json({ title: "Not found" }, 404));
    });
    vi.stubGlobal("fetch", fetchMock);

    render(<MemoryRouter initialEntries={["/"]}><App /></MemoryRouter>);

    expect(await screen.findByRole("heading", { level: 1, name: "Proofs as typed programs" })).toBeVisible();
    expect(screen.getByRole("navigation", { name: "Main navigation" })).toBeVisible();
    expect(screen.getByText("Kernel checked")).toBeVisible();
    expect(fetchMock).toHaveBeenCalledWith("/api/v2/pages/home", expect.any(Object));
  });

  it("loads a strategy detail without constructing strategy data in the browser", async () => {
    const fetchMock = vi.fn((input: RequestInfo | URL) => {
      const path = String(input);
      if (path === "/api/v2/site") return Promise.resolve(json(site));
      if (path === "/api/v2/strategies/response-classifier") {
        return Promise.resolve(json(page("response-classifier", "Response classifier")));
      }
      return Promise.resolve(json({ title: "Not found" }, 404));
    });
    vi.stubGlobal("fetch", fetchMock);

    render(<MemoryRouter initialEntries={["/strategies/response-classifier"]}><App /></MemoryRouter>);

    expect(await screen.findByRole("heading", { level: 1, name: "Response classifier" })).toBeVisible();
    expect(fetchMock).toHaveBeenCalledWith("/api/v2/strategies/response-classifier", expect.any(Object));
  });

  it("renders the normalized DAG from a certified reduction", async () => {
    const erdosPage = page("erdos", "A resolved semantic proof run");
    const fetchMock = vi.fn((input: RequestInfo | URL) => {
      const path = String(input);
      if (path === "/api/v2/site") return Promise.resolve(json(site));
      if (path === "/api/v2/examples/erdos") return Promise.resolve(json(erdosPage));
      if (path === "/api/v2/proof-runs/erdos") {
        return Promise.resolve(json(syntheticCertifiedProofRun));
      }
      return Promise.resolve(json({ title: "Not found" }, 404));
    });
    vi.stubGlobal("fetch", fetchMock);

    render(
      <MemoryRouter initialEntries={["/examples/erdos?selected=node%3Av0"]}>
        <App />
      </MemoryRouter>,
    );

    expect(await screen.findByRole("heading", { name: "A resolved semantic proof run" })).toBeVisible();
    expect(screen.getByRole("heading", { name: "Normalized strategy DAG" })).toBeVisible();
    expect(screen.getByRole("heading", { name: "Kernel-certified reduction" })).toBeVisible();
    expect(screen.getByText("Synthetic certified reduction fixture")).toBeVisible();
    expect(screen.getAllByText("Retained residuals").length).toBeGreaterThan(0);
    expect(screen.getAllByText("finite_density_budget:0").length).toBeGreaterThan(0);
    expect(screen.getAllByText("certificate decision").length).toBeGreaterThan(0);
    expect(screen.getAllByText("ordered_witness_scan:0").length).toBeGreaterThan(0);
    expect(screen.getByRole("link", { name: "Open raw JSON ↗" })).toHaveAttribute(
      "href",
      "/api/v2/proof-runs/erdos",
    );
    fireEvent.click(screen.getByRole("button", { name: "Semantic routes" }));
    expect(screen.getByRole("heading", { name: "Resolved semantic autoroutes" })).toBeVisible();
    expect(fetchMock).toHaveBeenCalledWith("/api/v2/proof-runs/erdos", expect.any(Object));
  });

  it("inspects resolved selection and bridge provenance without reconstructing a Program", async () => {
    const erdosPage = page("erdos", "A resolved semantic proof run");
    const fetchMock = vi.fn((input: RequestInfo | URL) => {
      const path = String(input);
      if (path === "/api/v2/site") return Promise.resolve(json(site));
      if (path === "/api/v2/examples/erdos") return Promise.resolve(json(erdosPage));
      if (path === "/api/v2/proof-runs/erdos") {
        return Promise.resolve(json(syntheticCertifiedProofRun));
      }
      return Promise.resolve(json({ title: "Not found" }, 404));
    });
    vi.stubGlobal("fetch", fetchMock);

    render(<MemoryRouter initialEntries={["/examples/erdos"]}><App /></MemoryRouter>);

    fireEvent.click(await screen.findByRole("button", { name: "Semantic routes" }));
    const routeButton = await screen.findByRole("button", {
      name: /synthetic literal transport v0 → v1/i,
    });
    fireEvent.click(routeButton);
    expect(screen.getByRole("heading", {
      name: "Synthetic literal transport",
    })).toBeVisible();
    expect(screen.getByText("deepest_most_restrictive")).toBeVisible();
    expect(screen.getByText("smallest_stable_structural_id")).toBeVisible();
    expect(screen.getByText("BridgeCertificate.residual_eq")).toBeVisible();
    expect(screen.getByText("Hypostructure.Core.Residual.Ledger.Extension")).toBeVisible();
    expect(screen.getByText("Cosmetic route commentary retained in the JSON fixture.")).toBeVisible();
  });

  it("renders an allowlisted source excerpt inside the application", async () => {
    const fetchMock = vi.fn((input: RequestInfo | URL) => {
      const path = String(input);
      if (path === "/api/v2/site") return Promise.resolve(json(site));
      if (path === "/api/v2/sources/core-source/excerpt?start=2&end=3") {
        return Promise.resolve(json({
          sourceId: "core-source",
          path: "hypostructure/Hypostructure/Core/Problem.lean",
          sha256: "a".repeat(64),
          startLine: 2,
          endLine: 3,
          totalLines: 12,
          content: "structure Problem where\n  target : Nat",
        }));
      }
      return Promise.resolve(json({ title: "Not found" }, 404));
    });
    vi.stubGlobal("fetch", fetchMock);

    render(
      <MemoryRouter initialEntries={["/source/core-source?start=2&end=3"]}>
        <App />
      </MemoryRouter>,
    );

    expect(await screen.findByRole("heading", {
      level: 1,
      name: "hypostructure/Hypostructure/Core/Problem.lean",
    })).toBeVisible();
    expect(screen.getByText("structure Problem where")).toBeVisible();
    expect(screen.getByRole("button", { name: "Copy source excerpt" })).toBeVisible();
    expect(screen.getByRole("link", { name: "Next lines →" })).toHaveAttribute(
      "href",
      "/source/core-source?start=4&end=12",
    );
    expect(fetchMock).toHaveBeenCalledWith(
      "/api/v2/sources/core-source/excerpt?start=2&end=3",
      expect.any(Object),
    );
  });

  it("uses the backend site identity and respects disabled search", async () => {
    const configuredSite: SiteView = {
      ...site,
      name: "Configured Hypostructure",
      tagline: "Backend-owned proof documentation",
      searchEnabled: false,
    };
    const fetchMock = vi.fn((input: RequestInfo | URL) => {
      const path = String(input);
      if (path === "/api/v2/site") return Promise.resolve(json(configuredSite));
      if (path === "/api/v2/pages/home") return Promise.resolve(json(page("home", "Home")));
      return Promise.resolve(json({ title: "Not found" }, 404));
    });
    vi.stubGlobal("fetch", fetchMock);

    render(<MemoryRouter initialEntries={["/"]}><App /></MemoryRouter>);

    expect(await screen.findByRole("link", { name: "Configured Hypostructure home" })).toBeVisible();
    expect(screen.getAllByText("Backend-owned proof documentation").length).toBeGreaterThan(0);
    await waitFor(() => expect(screen.queryByRole("search")).not.toBeInTheDocument());
  });

  it("shows a real 404 for an unknown route", async () => {
    vi.stubGlobal("fetch", vi.fn(() => Promise.resolve(json(site))));
    render(<MemoryRouter initialEntries={["/old-framework"]}><App /></MemoryRouter>);
    expect(await screen.findByRole("heading", { name: "This route does not exist." })).toBeVisible();
    expect(screen.getByRole("link", { name: "Search the reference" })).toHaveAttribute("href", "/search");
  });

  it("does not redirect obsolete Erdős routes", async () => {
    vi.stubGlobal("fetch", vi.fn(() => Promise.resolve(json(site))));
    render(<MemoryRouter initialEntries={["/erdos/legacy-node"]}><App /></MemoryRouter>);
    expect(await screen.findByRole("heading", { name: "This route does not exist." })).toBeVisible();
  });

  it("announces the backend-ranked search result count", async () => {
    const fetchMock = vi.fn((input: RequestInfo | URL) => {
      const path = String(input);
      if (path === "/api/v2/site") return Promise.resolve(json(site));
      if (path === "/api/v2/search?q=routing") {
        return Promise.resolve(json({
          query: "routing",
          total: 2,
          page: 1,
          pageSize: 20,
          facets: [],
          results: [
            { id: "one", title: "First route", summary: "A route.", href: "/core/routes/one", kind: "route" },
            { id: "two", title: "Second route", summary: "Another route.", href: "/core/routes/two", kind: "route" },
          ],
        }));
      }
      return Promise.resolve(json({ title: "Not found" }, 404));
    });
    vi.stubGlobal("fetch", fetchMock);

    render(<MemoryRouter initialEntries={["/search?q=routing"]}><App /></MemoryRouter>);

    expect(await screen.findByText((_, element) => (
      element?.getAttribute("role") === "status"
      && element.textContent === "2 results for “routing”"
    ))).toHaveAttribute("aria-live", "polite");
  });
});
