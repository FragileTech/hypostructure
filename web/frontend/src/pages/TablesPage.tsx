import { useCallback, useMemo } from "react";
import { useNavigate, useSearchParams } from "react-router-dom";

import {
  Latex,
  MathProvider,
  TableView,
  createReferenceResolver,
  indexDocument,
  type ProofTable,
} from "../graph-explorer";
import { useProof } from "../hooks/useProof";
import { useProofDocument } from "../hooks/useProofDocument";
import { ErrorPanel, LoadingPanel } from "../components/RequestPanels";
import { NotFoundPage } from "./NotFoundPage";

/** The tables, in the order the paper prints them, under their own headings. */
function shelve(tables: ProofTable[], chapterName: (id?: string) => string) {
  const shelves: { key: string; label: string; tables: ProofTable[] }[] = [];
  for (const table of tables) {
    const label = [chapterName(table.chapter), table.group].filter(Boolean).join(" · ");
    const last = shelves[shelves.length - 1];
    if (last && last.label === label) last.tables.push(table);
    else shelves.push({ key: `${label}:${table.id}`, label, tables: [table] });
  }
  return shelves;
}

export function TablesPage() {
  const proof = useProof();
  const navigate = useNavigate();
  const [parameters, setParameters] = useSearchParams();
  const request = useProofDocument(proof?.slug ?? "");

  const update = useCallback(
    (patch: Record<string, string | null>) => {
      setParameters(
        (current) => {
          const next = new URLSearchParams(current);
          for (const [key, value] of Object.entries(patch)) {
            if (value) next.set(key, value);
            else next.delete(key);
          }
          return next;
        },
        { replace: true },
      );
    },
    [setParameters],
  );

  const document = request.status === "ready" ? request.document : undefined;
  const index = useMemo(() => (document ? indexDocument(document) : undefined), [document]);

  // A step is numbered within its own paper, so a link needs that paper's prefix.
  const explore = useCallback(
    (search: string) => navigate(`/${proof?.slug}/explore?${search}`),
    [navigate, proof],
  );

  const references = useMemo(
    () => (document && index ? createReferenceResolver(document, index) : undefined),
    [document, index],
  );

  if (!proof) return <NotFoundPage />;
  if (request.status === "loading") return <LoadingPanel />;
  if (request.status === "error") return <ErrorPanel error={request.error} />;
  if (!document || !index || !references) return <LoadingPanel />;

  const chapterName = (id?: string) =>
    document.chapters?.length ? (id ? index.chapterById.get(id)?.shortTitle ?? "" : "") : "";

  const shelves = shelve(document.tables, chapterName);
  const selected =
    document.tables.find((table) => table.id === parameters.get("table")) ?? document.tables[0];
  const prefix = selected.chapter
    ? index.chapterById.get(selected.chapter)?.prefix ?? ""
    : "";

  return (
    <MathProvider
      macros={document.macros}
      resolveReference={references.resolve}
      onReference={(key) => {
        const named = references.target(key);
        const holders = named.item ? index.nodesByItem.get(named.item) : undefined;
        if (named.item && holders?.length) {
          explore(`step=${holders[0]}&result=${encodeURIComponent(named.item)}`);
        }
      }}
      onNode={(number) => explore(`step=${prefix}${number}`)}
    >
      <div className="page page-tables">
        <nav className="table-rail" aria-label="Tables">
          <p className="table-rail-lead">
            The paper's own index of the argument. Every step number and every
            result links into the diagram.
          </p>
          {shelves.map((shelf) => (
            <div key={shelf.key}>
              {shelf.label ? <h2>{shelf.label}</h2> : null}
              <ul>
                {shelf.tables.map((table) => (
                  <li key={table.id}>
                    <button
                      type="button"
                      className={table.id === selected.id ? "is-current" : undefined}
                      onClick={() => update({ table: table.id, q: null })}
                    >
                      <span>
                        <Latex value={table.title} />
                      </span>
                      <small>{table.rows.length}</small>
                    </button>
                  </li>
                ))}
              </ul>
            </div>
          ))}
        </nav>

        <TableView
          table={selected}
          query={parameters.get("q") ?? ""}
          onQueryChange={(query) => update({ q: query || null })}
        />
      </div>
    </MathProvider>
  );
}
