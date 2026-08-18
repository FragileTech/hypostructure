import { useEffect } from "react";
import { Link, useLocation } from "react-router-dom";

import {
  METHODOLOGY_ID,
  MethodologySection,
  scrollToMethodology,
} from "../components/MethodologySection";
import { DOCS_ROOT } from "../docs/registry";
import { PROOFS } from "../proofs/registry";

export function LandingPage() {
  // The header offers the methodology from every page; arriving from there
  // lands here first and asks, through the navigation state, for the jump.
  const { state, key } = useLocation();
  useEffect(() => {
    if ((state as { scrollTo?: string } | null)?.scrollTo === METHODOLOGY_ID) {
      scrollToMethodology();
    }
  }, [state, key]);

  return (
    <div className="page page-landing">
      <header className="hero">
        <p className="hero-eyebrow">Proof explorer</p>
        <h1>Two long proofs, laid out so you can walk them</h1>
        <p className="hero-lead">
          Each of these papers draws its own argument as a dependency diagram of
          numbered steps. Here those diagrams are navigable: pick a step and see
          what it asserts, which results stand behind it, and where the argument
          goes next.
        </p>
        <p className="hero-actions">
          <button type="button" className="button button-quiet" onClick={scrollToMethodology}>
            Read the methodology
          </button>
        </p>
      </header>

      <ul className="proof-grid">
        {PROOFS.map((proof) => (
          <li key={proof.slug}>
            <Link to={`/${proof.slug}`}>
              <span className="proof-grid-glyph" aria-hidden="true">
                {proof.glyph}
              </span>
              <h2>{proof.name}</h2>
              <p className="proof-grid-question">{proof.question}</p>
              <p className="proof-grid-tagline">{proof.tagline}</p>
            </Link>
          </li>
        ))}
      </ul>

      <aside className="framework-callout">
        <span className="proof-grid-glyph" aria-hidden="true">
          λ
        </span>
        <div>
          <h2>Hypostructure</h2>
          <p>
            The reference for formalizing structural exhaustion proofs in Lean
            with the Hypostructure framework: the ledger that carries a branch,
            how a problem is defined, how steps, decisions and closures
            assemble into the theorem, and every public declaration as it
            stands.
          </p>
        </div>
        <Link to={DOCS_ROOT} className="button">
          Read the docs
        </Link>
      </aside>

      <MethodologySection />
    </div>
  );
}
