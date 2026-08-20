import { Link } from "react-router-dom";

import { KIND_LABELS } from "../graph-explorer/DetailParts";
import { Latex } from "../graph-explorer/Latex";
import { indexDocument } from "../graph-explorer/index-document";
import { locate } from "../graph-explorer/locate";
import type { ProofGraphDocument, ProofItem } from "../graph-explorer/types";
import {
  ALL_STRUCTURAL_PROPERTIES,
  EG_INVARIANT_BINDINGS,
  STRUCTURAL_SURVEY_PART_ANCHOR,
  STRUCTURAL_TECHNIQUES,
  propertyAnchor,
  techniqueAnchor,
  type PropertyId,
  type TechniqueId,
} from "./data";

const RESULT_KINDS = new Set(["theorem", "proposition", "lemma", "corollary"]);

type MethodologyCoordinate =
  | { id: PropertyId; kind: "property" }
  | { id: TechniqueId; kind: "technique" };

function MethodologyLink({ id, kind }: MethodologyCoordinate) {
  const target = kind === "property" ? propertyAnchor(id) : techniqueAnchor(id);
  return (
    <Link
      className={`survey-coordinate is-${kind}`}
      to="/"
      state={{ scrollTo: target }}
      title={`Open ${kind} ${id} in the problem-independent survey`}
    >
      {id}
    </Link>
  );
}

function ResultLink({ item, document }: { item: ProofItem; document: ProofGraphDocument }) {
  const where = locate(document, item.chapter, item.key);
  return where ? (
    <a href={where.url} target="_blank" rel="noreferrer">
      <span className="survey-result-kind">
        {KIND_LABELS[item.kind]} {where.location.number}
      </span>{" "}
      <Latex value={item.title || item.key} />
    </a>
  ) : (
    <span>
      <span className="survey-result-kind">{KIND_LABELS[item.kind]}</span>{" "}
      <Latex value={item.title || item.key} />
    </span>
  );
}

export function EGStructuralSurvey({ document }: { document: ProofGraphDocument }) {
  if (document.slug !== "erdos-gyarfas") return null;

  const index = indexDocument(document);
  const invariantByNumber = new Map(document.invariants.map((invariant) => [invariant.number, invariant]));
  const propertyById = new Map(ALL_STRUCTURAL_PROPERTIES.map((property) => [property.id, property]));
  const techniqueById = new Map(STRUCTURAL_TECHNIQUES.map((technique) => [technique.id, technique]));

  return (
    <section className="panel eg-structural-survey" aria-labelledby="eg-structural-survey-title">
      <p className="hero-eyebrow">Structure × technique</p>
      <h2 id="eg-structural-survey-title">Structural survey of the Erdős–Gyárfás proof</h2>
      <p className="panel-lead">
        The manuscript tracks 38 structural invariants. This ledger relates each one to
        the problem-independent coordinates in the{" "}
        <Link to="/" state={{ scrollTo: STRUCTURAL_SURVEY_PART_ANCHOR }}>
          methodology survey
        </Link>
        , then identifies the proof nodes and labelled results that implement it.
      </p>

      <div className="eg-survey-table-wrap">
        <table className="eg-survey-table">
          <thead>
            <tr>
              <th scope="col">EG invariant</th>
              <th scope="col">General structure</th>
              <th scope="col">Technique</th>
              <th scope="col">Nodes</th>
              <th scope="col">Implementing result</th>
              <th scope="col">Page</th>
            </tr>
          </thead>
          <tbody>
            {EG_INVARIANT_BINDINGS.map((binding) => {
              const invariant = invariantByNumber.get(binding.number);
              const primary = index.itemByKey.get(binding.primaryItem);
              const primaryWhere = primary ? locate(document, primary.chapter, primary.key) : undefined;
              const additional = [...new Set(invariant?.usedBy ?? [])]
                .filter((key) => key !== binding.primaryItem)
                .map((key) => index.itemByKey.get(key))
                .filter(
                  (item): item is ProofItem => item !== undefined && RESULT_KINDS.has(item.kind),
                );

              return (
                <tr key={binding.number}>
                  <th scope="row">
                    <span className="eg-invariant-number">Inv. {binding.number}</span>
                    <strong>{invariant ? <Latex value={invariant.name} /> : `Invariant ${binding.number}`}</strong>
                    {invariant?.constraint ? (
                      <small><Latex value={invariant.constraint} /></small>
                    ) : null}
                  </th>
                  <td>
                    <span className="survey-coordinate-list">
                      {binding.propertyIds.map((id) => (
                        <MethodologyLink key={id} id={id} kind="property" />
                      ))}
                    </span>
                    <span className="eg-survey-coordinate-names">
                      {binding.propertyIds.map((id) => propertyById.get(id)?.name).filter(Boolean).join(" · ")}
                    </span>
                  </td>
                  <td>
                    <span className="survey-coordinate-list">
                      {binding.techniqueIds.map((id) => (
                        <MethodologyLink key={id} id={id} kind="technique" />
                      ))}
                    </span>
                    <span className="eg-survey-coordinate-names">
                      {binding.techniqueIds.map((id) => techniqueById.get(id)?.name).filter(Boolean).join(" · ")}
                    </span>
                  </td>
                  <td>
                    <span className="eg-survey-nodes">
                      {(invariant?.nodes ?? []).map((id) => (
                        <Link
                          key={id}
                          to={`/erdos-gyarfas/explore?step=${encodeURIComponent(id)}`}
                          className="chip chip-node"
                          title={`Open node [${id}]`}
                        >
                          {id}
                        </Link>
                      ))}
                    </span>
                  </td>
                  <td>
                    {primary ? <ResultLink item={primary} document={document} /> : <code>{binding.primaryItem}</code>}
                    {additional.length ? (
                      <details className="eg-survey-more">
                        <summary>{additional.length} more results</summary>
                        <ul>
                          {additional.map((item) => {
                            const where = locate(document, item.chapter, item.key);
                            return (
                              <li key={item.key}>
                                <ResultLink item={item} document={document} />
                                {where ? <span>p. {where.page}</span> : null}
                              </li>
                            );
                          })}
                        </ul>
                      </details>
                    ) : null}
                  </td>
                  <td className="eg-survey-page">
                    {primaryWhere ? (
                      <a href={primaryWhere.url} target="_blank" rel="noreferrer">
                        p. {primaryWhere.page}
                      </a>
                    ) : (
                      "—"
                    )}
                  </td>
                </tr>
              );
            })}
          </tbody>
        </table>
      </div>
    </section>
  );
}
