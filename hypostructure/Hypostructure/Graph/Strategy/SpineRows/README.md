# Developing individual spine rows

Each atomic row or decision has its own module. `Basic` contains the four shared
utilities. Declaration names remain in `Hypostructure.Graph.Strategy.Spine`;
`Hypostructure.Graph.Strategy.SpineRows` remains the compatibility import for
all rows.

From `proofs/hypostructure_erdos_64_eg`, check only the row being edited:

```sh
lake build Hypostructure.Graph.Strategy.SpineRows.ReturnAvoidance
lake build Hypostructure.Graph.Strategy.SpineRows.Route8WindowBlockers
```

Then check its application callers with `lake build` in the same directory.
The targeted command checks the row and its prerequisites; the application
build also checks affected downstream proofs. Keep the existing `.lake` cache.

Import a row's own module in callers. An import of the compatibility module
makes the caller depend on every row. In particular, never import the
compatibility module from a file in this directory.

Each row module carries its own scoped `omit` directives, attributes,
universes, variable declarations, manifest and proof body. Each row reads and
publishes exactly its facts through the sealed executor; there is no separate
proof-data interface.

See `DECLARATIONS.md` for the declaration-to-module index. A shared vocabulary change
affects all rows; changing an individual row does not recompile the other row
declarations.
