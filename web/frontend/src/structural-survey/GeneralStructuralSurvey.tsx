import {
  ALL_STRUCTURAL_PROPERTIES,
  STRUCTURAL_PROPERTY_GROUPS,
  STRUCTURAL_TECHNIQUES,
  propertyAnchor,
  techniqueAnchor,
  type PropertyId,
  type TechniqueId,
} from "./data";

function scrollTo(id: string) {
  document.getElementById(id)?.scrollIntoView({ behavior: "smooth", block: "center" });
}

function CoordinateButton({
  id,
  kind,
}: {
  id: PropertyId | TechniqueId;
  kind: "property" | "technique";
}) {
  const target = kind === "property" ? propertyAnchor(id as PropertyId) : techniqueAnchor(id as TechniqueId);
  return (
    <button
      type="button"
      className={`survey-coordinate is-${kind}`}
      onClick={() => scrollTo(target)}
      aria-label={`Go to ${kind} ${id}`}
    >
      {id}
    </button>
  );
}

export function GeneralStructuralSurvey() {
  return (
    <div className="general-structural-survey">
      <p>
        A structural survey separates the property of an object from the move used to
        evaluate it. The coordinates below are deliberately problem-independent: the same
        property can be measured by several techniques, and each technique may return a
        bound, witness, decomposition, obstruction, or replacement.
      </p>
      <p className="survey-scope-note">
        <strong>Coverage boundary.</strong> These 88 coordinates exhaust the structural
        content exercised by the Erdős–Gyárfás proof and form a reusable core for graph
        problems. A graph-theory-wide handbook would add separate modules for planarity,
        minors and width, coloring, matching and factors, expansion, genuine graph spectra,
        random structure, and directed or weighted graphs.
      </p>

      <dl className="survey-ontology" aria-label="The five layers of a structural survey">
        <div><dt>Property</dt><dd>Isomorphism-invariant structure of a graph or marked graph.</dd></div>
        <div><dt>Observable</dt><dd>A number, set, relation, or finite state recording that structure.</dd></div>
        <div><dt>Proof state</dt><dd>A hypothesis introduced by the argument, such as minimality.</dd></div>
        <div><dt>Technique</dt><dd>A reusable operation or theorem applied to the observable.</dd></div>
        <div><dt>Certificate</dt><dd>The bound, witness, decomposition, or obstruction returned.</dd></div>
      </dl>

      <h4>Technique register</h4>
      <p>
        The <code>T</code>-coordinates name textbook moves. Their final column points to
        every structural coordinate they can evaluate in this survey.
      </p>
      <div className="methodology-table-wrap survey-table-wrap">
        <table className="methodology-map survey-technique-table">
          <thead>
            <tr>
              <th scope="col">Code</th>
              <th scope="col">Technique</th>
              <th scope="col">Standard move</th>
              <th scope="col">Evaluates</th>
            </tr>
          </thead>
          <tbody>
            {STRUCTURAL_TECHNIQUES.map((technique) => {
              const properties = ALL_STRUCTURAL_PROPERTIES.filter((property) =>
                property.techniques.includes(technique.id),
              );
              return (
                <tr id={techniqueAnchor(technique.id)} key={technique.id}>
                  <th scope="row"><code className="survey-id">{technique.id}</code></th>
                  <td><strong>{technique.name}</strong></td>
                  <td>{technique.move}</td>
                  <td>
                    <span className="survey-coordinate-list">
                      {properties.map((property) => (
                        <CoordinateButton key={property.id} id={property.id} kind="property" />
                      ))}
                    </span>
                  </td>
                </tr>
              );
            })}
          </tbody>
        </table>
      </div>

      <h4>Structural invariant register</h4>
      <p>
        Each row names one atomic property, the observable used to see it, the moves that
        evaluate it, the certificate those moves can produce, and the information still
        missing afterward.
      </p>
      <div className="survey-property-groups">
        {STRUCTURAL_PROPERTY_GROUPS.map((group) => (
          <section className="survey-property-group" key={group.id} aria-labelledby={`survey-group-${group.id}`}>
            <header>
              <h5 id={`survey-group-${group.id}`}>{group.title}</h5>
              <span>{group.properties.length} coordinates</span>
            </header>
            <div className="methodology-table-wrap survey-table-wrap">
              <table className="methodology-map survey-property-table">
                <thead>
                  <tr>
                    <th scope="col">ID</th>
                    <th scope="col">Structural property</th>
                    <th scope="col">Observable</th>
                    <th scope="col">Techniques</th>
                    <th scope="col">Certificate</th>
                    <th scope="col">What remains unknown</th>
                  </tr>
                </thead>
                <tbody>
                  {group.properties.map((property) => (
                    <tr id={propertyAnchor(property.id)} key={property.id}>
                      <th scope="row"><code className="survey-id">{property.id}</code></th>
                      <td><strong>{property.name}</strong></td>
                      <td>{property.observable}</td>
                      <td>
                        <span className="survey-coordinate-list">
                          {property.techniques.map((id) => (
                            <CoordinateButton key={id} id={id} kind="technique" />
                          ))}
                        </span>
                      </td>
                      <td>{property.certificate}</td>
                      <td>{property.caveat}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </section>
        ))}
      </div>
    </div>
  );
}
