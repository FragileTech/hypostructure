import { useEffect, useId, useRef, useState, type ReactNode } from "react";
import { Link, NavLink, useLocation, useNavigate } from "react-router-dom";

import { fetchSite } from "../api";
import { useApiResource } from "../hooks/useApiResource";

const fallbackNavigation = [
  { label: "Start", href: "/docs/getting-started" },
  { label: "Problem", href: "/docs/problems" },
  { label: "DAG", href: "/docs/dags" },
  { label: "Strategies", href: "/strategies" },
  { label: "Examples", href: "/examples" },
  { label: "Reference", href: "/reference" },
];

export function AppShell({ children }: { children: ReactNode }) {
  const site = useApiResource((signal) => fetchSite(signal), []);
  const location = useLocation();
  const navigate = useNavigate();
  const [menuOpen, setMenuOpen] = useState(false);
  const [query, setQuery] = useState("");
  const mainRef = useRef<HTMLElement>(null);
  const navId = useId();
  const navigation = site.state === "ready" ? site.data.navigation : fallbackNavigation;
  const siteName = site.state === "ready" ? site.data.name : "Hypostructure";
  const tagline = site.state === "ready"
    ? site.data.tagline
    : "Define the problem. Compose the proof.";
  const searchEnabled = site.state === "ready" && site.data.searchEnabled;
  const brandInitial = siteName.trim().charAt(0).toUpperCase() || "H";

  useEffect(() => {
    setMenuOpen(false);
    mainRef.current?.focus();
  }, [location.pathname]);

  return (
    <div className="app-frame">
      <a className="skip-link" href="#main-content">
        Skip to content
      </a>
      <header className="site-header">
        <div className="header-inner">
          <Link className="brand" to="/" aria-label={`${siteName} home`}>
            <span className="brand-mark" aria-hidden="true">
              {brandInitial}
            </span>
            <span>
              <strong>{siteName}</strong>
              <small>{tagline}</small>
            </span>
          </Link>
          <button
            className="menu-button"
            type="button"
            aria-expanded={menuOpen}
            aria-controls={navId}
            onClick={() => setMenuOpen((open) => !open)}
          >
            <span aria-hidden="true">{menuOpen ? "×" : "☰"}</span>
            <span className="sr-only">Toggle navigation</span>
          </button>
          <nav id={navId} className={menuOpen ? "main-nav is-open" : "main-nav"} aria-label="Main navigation">
            {navigation.map((item) => (
              <NavLink key={item.href} to={item.href}>
                {item.label}
              </NavLink>
            ))}
          </nav>
          {searchEnabled ? (
            <form
              className="header-search"
              role="search"
              onSubmit={(event) => {
                event.preventDefault();
                const normalized = query.trim();
                navigate(normalized ? `/search?q=${encodeURIComponent(normalized)}` : "/search");
              }}
            >
              <label className="sr-only" htmlFor="site-search">
                Search declarations and guides
              </label>
              <input
                id="site-search"
                value={query}
                onChange={(event) => setQuery(event.target.value)}
                placeholder="Search"
                type="search"
              />
              <button type="submit" aria-label="Submit search">
                ↗
              </button>
            </form>
          ) : null}
        </div>
      </header>
      <main id="main-content" ref={mainRef} tabIndex={-1}>
        {children}
      </main>
      <footer className="site-footer">
        <div>
          <span className="brand-footer">{siteName}</span>
          <p>{tagline}</p>
        </div>
        <div className="footer-links">
          <Link to="/docs/getting-started">Start a proof</Link>
          <Link to="/strategies">Strategy catalog</Link>
          <Link to="/reference">API reference</Link>
        </div>
        {site.state === "ready" ? (
          <p className="snapshot">Snapshot {site.data.snapshot}</p>
        ) : null}
      </footer>
    </div>
  );
}
