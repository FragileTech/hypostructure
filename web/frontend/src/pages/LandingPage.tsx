import { Link } from "react-router-dom";

import { PROOFS } from "../proofs/registry";

export function LandingPage() {
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
    </div>
  );
}
