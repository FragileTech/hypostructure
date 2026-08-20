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
    const target = (state as { scrollTo?: string } | null)?.scrollTo;
    if (target?.startsWith(METHODOLOGY_ID)) {
      scrollToMethodology(target);
    }
  }, [state, key]);

  return (
    <div className="page page-landing">
      <header className="hero">
        <p className="hero-eyebrow">LLM-assisted research</p>
        <h1>An interactive structural analysis of difficult mathematical problems</h1>
        <div className="hero-lead hero-lead-stack">
          <p>
            This site presents an LLM-assisted, interactive analysis of the
            structures underlying difficult problems in combinatorics and
            partial differential equations. Each argument is decomposed into a
            case-by-case study of its structural alternatives, showing how
            established mathematical techniques interact and how individual
            results depend on one another. Navigable proof diagrams let readers
            inspect each step, trace its supporting results, and follow the
            subsequent branches of the argument.
          </p>
          <p>
            Hypostructure is an ongoing research project with two closely
            connected goals. The first is to build a detailed structural survey
            that exposes recurring mechanisms and hidden relationships,
            providing a foundation for developing new mathematical techniques.
            The second is to create a Lean library for formalizing and automating
            long structural-exhaustion arguments, so that their underlying
            strategies can be abstracted, reused, and eventually applied to new
            problems.
          </p>
          <p>
            The project is evolving, and its analyses and formalizations remain
            open to refinement. We warmly welcome mathematicians, formal-methods
            researchers, and other interested members of the community to
            explore the work, identify gaps, suggest improvements, and contribute
            new perspectives.
          </p>
        </div>
        <p className="hero-actions">
          <button
            type="button"
            className="button button-quiet"
            onClick={() => scrollToMethodology()}
          >
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
