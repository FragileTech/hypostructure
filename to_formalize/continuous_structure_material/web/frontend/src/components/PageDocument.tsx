import { Link, NavLink } from "react-router-dom";

import { useDocumentMetadata } from "../hooks/useDocumentMetadata";
import type { PageView } from "../v2-types";
import { ContentBlocks } from "./ContentBlocks";

const documentationGroups = [
  {
    label: "Learn",
    items: [
      { label: "Getting started", href: "/docs/getting-started" },
      { label: "Define a Problem", href: "/docs/problems" },
      { label: "Build the DAG", href: "/docs/dags" },
    ],
  },
  {
    label: "Strategies",
    items: [
      { label: "Catalog", href: "/strategies" },
      { label: "Ordered witness scan", href: "/strategies/ordered-witness-scan" },
      { label: "Response classifier", href: "/strategies/response-classifier" },
      { label: "Capacity ledger", href: "/strategies/capacity-ledger" },
      { label: "Support localization", href: "/strategies/support-localization" },
      { label: "Rank and budget", href: "/strategies/rank-budget" },
      { label: "Closed code", href: "/strategies/closed-code" },
      { label: "Dichotomy", href: "/strategies/dichotomy" },
      { label: "Target or avoid", href: "/strategies/target-or-avoid" },
    ],
  },
  {
    label: "Apply",
    items: [
      { label: "Worked examples", href: "/examples" },
      { label: "API reference", href: "/reference" },
    ],
  },
];

const guideSequence = [
  { label: "Getting started", href: "/docs/getting-started" },
  { label: "Define a Problem", href: "/docs/problems" },
  { label: "Build the DAG", href: "/docs/dags" },
  { label: "Strategy catalog", href: "/strategies" },
  { label: "Worked examples", href: "/examples" },
  { label: "API reference", href: "/reference" },
];

function DocumentationSidebar() {
  return (
    <aside className="docs-sidebar" aria-label="Documentation sections">
      <nav>
        {documentationGroups.map((group) => (
          <div className="docs-nav-group" key={group.label}>
            <h2>{group.label}</h2>
            {group.items.map((item) => (
              <NavLink key={item.href} to={item.href}>{item.label}</NavLink>
            ))}
          </div>
        ))}
      </nav>
    </aside>
  );
}

function PageNavigator({ path }: { path?: string | null }) {
  const index = guideSequence.findIndex((item) => item.href === path);
  if (index < 0) return null;
  const previous = guideSequence[index - 1];
  const next = guideSequence[index + 1];
  return (
    <nav className="page-navigator" aria-label="Guide pagination">
      {previous ? <Link to={previous.href}><small>Previous</small><strong>← {previous.label}</strong></Link> : <span />}
      {next ? <Link to={next.href}><small>Next</small><strong>{next.label} →</strong></Link> : <span />}
    </nav>
  );
}

export function PageDocument({ page }: { page: PageView }) {
  useDocumentMetadata(page.title, page.summary, page.canonicalPath);

  return (
    <article className={`page page-${page.id}`}>
      <header className="page-hero">
        <div className="hero-orbit orbit-one" aria-hidden="true" />
        <div className="hero-orbit orbit-two" aria-hidden="true" />
        <div className="hero-content">
          {page.breadcrumbs?.length ? (
            <nav className="breadcrumbs" aria-label="Breadcrumb">
              <ol>
                {page.breadcrumbs.map((item, index) => (
                  <li key={`${item.label}-${index}`}>
                    {item.href ? <Link to={item.href}>{item.label}</Link> : <span aria-current="page">{item.label}</span>}
                  </li>
                ))}
              </ol>
            </nav>
          ) : null}
          {page.eyebrow ? <p className="hero-eyebrow">{page.eyebrow}</p> : null}
          <h1>{page.title}</h1>
          <p className="hero-summary">{page.summary}</p>
          {page.description ? <p className="hero-description">{page.description}</p> : null}
          {page.metrics?.length ? (
            <dl className="hero-metrics">
              {page.metrics.map((metric) => (
                <div key={metric.label}>
                  <dt>{metric.label}</dt>
                  <dd>{metric.value}</dd>
                  {metric.detail ? <small>{metric.detail}</small> : null}
                </div>
              ))}
            </dl>
          ) : null}
        </div>
      </header>
      <div className={page.id === "home" ? "page-layout page-layout-home" : "page-layout"}>
        {page.id === "home" ? null : <DocumentationSidebar />}
        <div className="page-body">
        {page.verification ? (
          <details className={`verification verification-${page.verification.state}`}>
            <summary>
              <span aria-hidden="true">{page.verification.state === "verified" ? "✓" : "!"}</span>
              <strong>{page.verification.label}</strong>
              <span>{page.verification.summary}</span>
            </summary>
            {page.verification.details?.length ? (
              <dl>
                {page.verification.details.map((detail) => (
                  <div key={detail.label}><dt>{detail.label}</dt><dd>{detail.value}</dd></div>
                ))}
              </dl>
            ) : null}
          </details>
        ) : null}
        {page.sections.map((section) => (
          <section className="content-section" id={section.id} key={section.id}>
            {section.eyebrow ? <p className="section-eyebrow">{section.eyebrow}</p> : null}
            {section.title ? <h2>{section.title}</h2> : null}
            {section.summary ? <p className="section-summary">{section.summary}</p> : null}
            <ContentBlocks blocks={section.blocks} />
          </section>
        ))}
          <PageNavigator path={page.canonicalPath} />
        </div>
        {page.id === "home" ? null : (
          <aside className="page-toc" aria-label="On this page">
            <strong>On this page</strong>
            <ol>
              {page.sections.filter((section) => section.title).map((section) => (
                <li key={section.id}><a href={`#${section.id}`}>{section.title}</a></li>
              ))}
            </ol>
          </aside>
        )}
      </div>
    </article>
  );
}
