import { NavLink, Outlet, useLocation } from "react-router-dom";

import { useProof } from "../hooks/useProof";
import { PROOFS } from "../proofs/registry";

export function AppShell() {
  const proof = useProof();
  const { pathname } = useLocation();
  // Keep the reader on the same kind of page when they change proof.
  const section = pathname.split("/")[2] ?? "";

  return (
    <div className="app">
      <header className="app-header">
        <NavLink to="/" className="app-mark">
          <span aria-hidden="true" className="app-mark-glyph">
            {proof?.glyph ?? "∎"}
          </span>
          <span>
            <strong>{proof ? proof.name : "Proof explorer"}</strong>
            <small>{proof ? "a walk through the proof" : "pick a proof to walk through"}</small>
          </span>
        </NavLink>

        {proof ? (
          <nav aria-label="Sections">
            <NavLink to={`/${proof.slug}`} end>
              Overview
            </NavLink>
            <NavLink to={`/${proof.slug}/explore`}>Explore the proof</NavLink>
            <NavLink to={`/${proof.slug}/notation`}>Notation</NavLink>
          </nav>
        ) : null}

        <nav className="proof-switcher" aria-label="Proof">
          {PROOFS.map((entry) => (
            <NavLink
              key={entry.slug}
              to={section ? `/${entry.slug}/${section}` : `/${entry.slug}`}
              className={entry.slug === proof?.slug ? "active" : undefined}
            >
              {entry.name}
            </NavLink>
          ))}
        </nav>
      </header>
      <main className="app-main">
        <Outlet />
      </main>
    </div>
  );
}
