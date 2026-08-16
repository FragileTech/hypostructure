import { NavLink, Outlet } from "react-router-dom";

import { DOCS_GROUPS, DOCS_PAGES, DOCS_ROOT, docsPath } from "./registry";

/** The docs section: a rail of pages on the left, the page on the right. */
export function DocsLayout() {
  return (
    <div className="page page-docs">
      <nav className="docs-rail" aria-label="Hypostructure docs">
        <p className="docs-rail-lead">
          The reference for formalizing structural exhaustion proofs with the
          hypostructure framework.
        </p>
        <ul>
          <li>
            <NavLink to={DOCS_ROOT} end className={railClass}>
              Overview
            </NavLink>
          </li>
        </ul>
        {DOCS_GROUPS.map((group) => (
          <div key={group.id}>
            <h2>{group.title}</h2>
            <ul>
              {DOCS_PAGES.filter((page) => page.group === group.id).map((page) => (
                <li key={page.slug}>
                  <NavLink to={docsPath(page)} className={railClass}>
                    {page.title}
                  </NavLink>
                </li>
              ))}
            </ul>
          </div>
        ))}
      </nav>
      <div className="docs-content">
        <Outlet />
      </div>
    </div>
  );
}

function railClass({ isActive }: { isActive: boolean }) {
  return isActive ? "is-current" : undefined;
}
