import { L, LeanCode } from "../LeanCode";

export interface ApiEntry {
  name: string;
  kind: "def" | "theorem" | "structure" | "class" | "inductive" | "abbrev" | "instance";
  /** Who may call it. */
  audience: "application" | "framework";
  signature: string;
  note: string;
}

export interface ApiModule {
  title: string;
  /** One or more source files, repo-relative. */
  paths: string[];
  intro: string;
  entries: ApiEntry[];
}

function slugify(name: string) {
  return name.toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/(^-|-$)/g, "");
}

/** The site uses a hash router, so an in-page anchor must scroll by hand. */
function jumpTo(id: string) {
  document.getElementById(id)?.scrollIntoView({ behavior: "smooth", block: "start" });
}

/** The badge that says who may call a declaration. */
export function AudienceBadge({ audience }: { audience: ApiEntry["audience"] }) {
  return (
    <span className={`docs-badge${audience === "framework" ? " is-framework" : ""}`}>
      {audience === "framework" ? "framework-only" : "application"}
    </span>
  );
}

/** The shared header note of every reference page. */
export function ReferenceLegend() {
  return (
    <p className="docs-legend">
      <AudienceBadge audience="application" /> may be used from a proof module.{" "}
      <AudienceBadge audience="framework" /> takes a <L>FrameworkToken</L> and elaborates
      only inside <L>Hypostructure.*</L>.
    </p>
  );
}

/** A module table of contents followed by every module's entries. */
export function ApiReference({ modules }: { modules: ApiModule[] }) {
  return (
    <>
      <nav className="docs-toc" aria-label="Modules">
        <ul>
          {modules.map((module) => (
            <li key={module.title}>
              <button type="button" onClick={() => jumpTo(slugify(module.title))}>
                {module.title}
              </button>
              <small>{module.entries.length} declarations</small>
            </li>
          ))}
        </ul>
      </nav>

      {modules.map((module) => (
        <section key={module.title} id={slugify(module.title)} className="docs-module">
          <h2>{module.title}</h2>
          <p className="docs-module-path">
            {module.paths.map((path) => (
              <code key={path}>{path}</code>
            ))}
          </p>
          <p>{module.intro}</p>
          {module.entries.map((entry) => (
            <div key={entry.name} className="docs-entry" id={slugify(entry.name)}>
              <h3>
                <span className="docs-entry-kind">{entry.kind}</span>
                <code>{entry.name}</code>
                <AudienceBadge audience={entry.audience} />
              </h3>
              <LeanCode>{entry.signature}</LeanCode>
              <p>{entry.note}</p>
            </div>
          ))}
        </section>
      ))}
    </>
  );
}
