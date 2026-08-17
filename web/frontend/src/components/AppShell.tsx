import { useEffect, useRef } from "react";
import { NavLink, Outlet, useLocation } from "react-router-dom";

import { DOCS_ROOT } from "../docs/registry";
import { useProof } from "../hooks/useProof";
import { PROOFS, paperUrl, type PaperFile } from "../proofs/registry";

/**
 * The manuscripts behind the proof, to download. One paper is a plain link;
 * several fold into a small menu so the header stays one row.
 */
function PaperDownloads({ papers }: { papers: PaperFile[] }) {
  const menu = useRef<HTMLDetailsElement>(null);

  // A native <details> only closes when its summary is clicked again; a menu
  // should also go away on a click elsewhere, on Escape, and once a paper is
  // chosen.
  useEffect(() => {
    const close = (event: MouseEvent | KeyboardEvent) => {
      const element = menu.current;
      if (!element?.open) return;
      if (event instanceof KeyboardEvent) {
        if (event.key === "Escape") element.open = false;
        return;
      }
      const target = event.target as Node;
      if (!element.contains(target) || (target as Element).closest?.("a")) element.open = false;
    };
    document.addEventListener("click", close);
    document.addEventListener("keydown", close);
    return () => {
      document.removeEventListener("click", close);
      document.removeEventListener("keydown", close);
    };
  }, []);

  if (papers.length === 0) return null;
  if (papers.length === 1) {
    return (
      <a className="paper-download" href={paperUrl(papers[0])} download>
        <DownloadGlyph />
        Download the paper
      </a>
    );
  }
  return (
    <details className="paper-downloads" ref={menu}>
      <summary className="paper-download">
        <DownloadGlyph />
        Download the papers
      </summary>
      <ul>
        {papers.map((paper) => (
          <li key={paper.file}>
            <a href={paperUrl(paper)} download>
              {paper.title}
              <small>PDF</small>
            </a>
          </li>
        ))}
      </ul>
    </details>
  );
}

function DownloadGlyph() {
  return (
    <svg aria-hidden="true" width="14" height="14" viewBox="0 0 16 16" fill="none">
      <path
        d="M8 2v8m0 0 3-3m-3 3L5 7M3 12v1.5h10V12"
        stroke="currentColor"
        strokeWidth="1.6"
        strokeLinecap="round"
        strokeLinejoin="round"
      />
    </svg>
  );
}

export function AppShell() {
  const proof = useProof();
  const { pathname } = useLocation();
  const onDocs = pathname === DOCS_ROOT || pathname.startsWith(`${DOCS_ROOT}/`);
  // Keep the reader on the same kind of page when they change proof.
  const section = proof ? pathname.split("/")[2] ?? "" : "";

  const mark = proof
    ? { glyph: proof.glyph, name: proof.name, hint: "a walk through the proof" }
    : onDocs
      ? { glyph: "λ", name: "Hypostructure", hint: "the framework reference" }
      : { glyph: "∎", name: "Proof explorer", hint: "pick a proof to walk through" };

  return (
    <div className="app">
      <header className="app-header">
        <NavLink to="/" className="app-mark">
          <span aria-hidden="true" className="app-mark-glyph">
            {mark.glyph}
          </span>
          <span>
            <strong>{mark.name}</strong>
            <small>{mark.hint}</small>
          </span>
        </NavLink>

        {proof ? (
          <nav aria-label="Sections">
            {/* The sections scroll sideways on a narrow screen rather than
                wrapping; the downloads menu stays outside that strip, so its
                list is not clipped by the scroll container. */}
            <div className="app-sections">
              <NavLink to={`/${proof.slug}`} end>
                Overview
              </NavLink>
              <NavLink to={`/${proof.slug}/explore`}>Explore the proof</NavLink>
              <NavLink to={`/${proof.slug}/tables`}>Tables</NavLink>
              <NavLink to={`/${proof.slug}/notation`}>Notation</NavLink>
            </div>
            <PaperDownloads papers={proof.papers} />
          </nav>
        ) : null}

        <div className="app-header-end">
          <nav className="framework-link" aria-label="Framework">
            <NavLink to={DOCS_ROOT}>Lean Framework</NavLink>
          </nav>
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
        </div>
      </header>
      <main className="app-main">
        <Outlet />
      </main>
    </div>
  );
}
