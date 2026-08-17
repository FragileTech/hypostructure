import { NavLink, Outlet } from "react-router-dom";

import { SidebarRail } from "../components/SidebarRail";
import { railPageClass, useSidebar } from "../hooks/useSidebar";
import { DOCS_GROUPS, DOCS_PAGES, DOCS_ROOT, docsPath } from "./registry";

/** The docs section: a rail of pages on the left, the page on the right. */
export function DocsLayout() {
  const sidebar = useSidebar("proof-explorer:docs-rail");
  return (
    <div className={railPageClass("page page-docs", sidebar)}>
      <SidebarRail
        sidebar={sidebar}
        label="Hypostructure docs"
        id="docs-rail"
        className="docs-rail"
      >
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
      </SidebarRail>
      <div className="docs-content">
        <Outlet />
      </div>
    </div>
  );
}

function railClass({ isActive }: { isActive: boolean }) {
  return isActive ? "is-current" : undefined;
}
