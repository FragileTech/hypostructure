import { useMemo } from "react";

import { Latex } from "./Latex";
import { latexToPlainText } from "./latex";
import type { ProofTable } from "./types";

export interface TableViewProps {
  table: ProofTable;
  /** Only rows containing every term are shown; empty shows all of them. */
  query?: string;
  onQueryChange?: (query: string) => void;
}

/**
 * One of a paper's cross-reference tables, as written.
 *
 * Cells are rendered as the paper set them — mathematics through KaTeX,
 * `\cref` as the result it names, and bracketed integers as steps you can
 * follow — so the table doubles as an index into the diagram.
 */
export function TableView({ table, query = "", onQueryChange }: TableViewProps) {
  const searchable = useMemo(
    () => table.rows.map((row) => row.map(latexToPlainText).join(" ").toLowerCase()),
    [table],
  );

  const rows = useMemo(() => {
    const terms = query.trim().toLowerCase().split(/\s+/).filter(Boolean);
    if (!terms.length) return table.rows.map((row, index) => ({ row, index }));
    return table.rows
      .map((row, index) => ({ row, index }))
      .filter(({ index }) => terms.every((term) => searchable[index].includes(term)));
  }, [query, searchable, table]);

  return (
    <section className="table-view" aria-label={table.title}>
      <header className="table-view-header">
        <div>
          {table.group ? <p className="table-view-group">{table.group}</p> : null}
          <h2>
            <Latex value={table.title} />
          </h2>
        </div>
        {onQueryChange ? (
          <label className="field field-search">
            <span>Filter rows</span>
            <input
              type="search"
              value={query}
              placeholder="a step, a result, a word…"
              onChange={(event) => onQueryChange(event.target.value)}
            />
          </label>
        ) : null}
      </header>

      <p className="table-view-count" role="status">
        {rows.length === table.rows.length
          ? `${table.rows.length} rows`
          : `${rows.length} of ${table.rows.length} rows`}
      </p>

      <div className="table-view-scroll">
        <table className="data-table">
          <thead>
            <tr>
              {table.headers.map((heading, column) => (
                <th key={column} scope="col">
                  <Latex value={heading} />
                </th>
              ))}
            </tr>
          </thead>
          <tbody>
            {rows.map(({ row, index }) => (
              <tr key={index}>
                {row.map((value, column) => (
                  <td key={column}>
                    <Latex value={value} nodes />
                  </td>
                ))}
              </tr>
            ))}
          </tbody>
        </table>
      </div>

      {rows.length === 0 ? (
        <p className="table-view-empty">No row mentions that.</p>
      ) : null}
    </section>
  );
}
