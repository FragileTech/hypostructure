import { Link, useParams } from "react-router-dom";

import { NotFoundPage } from "../pages/NotFoundPage";
import { docsNeighbours, docsPath, findDocsPage } from "./registry";

/** One documentation page, chosen by its slug, with the pager beneath it. */
export function DocsPage() {
  const { page: slug } = useParams();
  const page = findDocsPage(slug);
  if (!page) return <NotFoundPage />;
  const { previous, next } = docsNeighbours(page.slug);
  return (
    <article className="docs-article" key={page.slug}>
      <page.Content />
      <nav className="docs-pager" aria-label="Neighbouring pages">
        {previous ? (
          <Link to={docsPath(previous)} rel="prev">
            <small>Previous</small>
            {previous.title}
          </Link>
        ) : (
          <span />
        )}
        {next ? (
          <Link to={docsPath(next)} rel="next" className="is-next">
            <small>Next</small>
            {next.title}
          </Link>
        ) : null}
      </nav>
    </article>
  );
}
