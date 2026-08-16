# Hypostructure API documentation

The website documents the application-facing Hypostructure API:

```text
Core.ProblemDefinition
  + Core.Strategy.Dag.Blueprint or Program
  -> ofDag%
  -> ProblemDeclaration.report
  -> report.statement.down
```

## Content authority

- Lean exports the strategy registry, declaration names, elaborated types,
  docstrings, dependencies, and source ranges from the compiled environment.
- `web/content/strategies.json` supplies curated selection guidance and examples.
  The data build fails if it drifts from the compiled registry.
- Guide pages live in `web/content/pages`; runnable examples live in
  `web/content/snippets`.
- The Erdős proof section at `/examples/erdos` consumes the validated
  `hypostructure_proof_run` export through the same Flask API as the rest of the
  site. Its Program and normalized DAG views do not infer proof state.
- The generated snapshot and every source excerpt are SHA-256 bound by the
  manifest before the backend serves them. The published Erdős run is likewise
  schema-validated, invariant-checked, and hash-bound to the snapshot.

The browser receives presentation-ready page models. It does not inspect Lean
sources, resolve strategy registrations, or infer proof state.

## Commands

```bash
make web-data   # export Lean declarations and build the verified snapshot
make web-test   # validate snippets, schemas, backend, frontend, and bundle
make web        # build and serve on the configured host/port
```

The frontend uses a responsive documentation portal with guide navigation,
strategy detail pages, an on-page table of contents, search, and verified source
links. The interactive Erdős section is served by this application—there is no
separate proof server or frontend bundle. Obsolete CT-, route-, and
application-status URLs redirect to the closest current guide.
