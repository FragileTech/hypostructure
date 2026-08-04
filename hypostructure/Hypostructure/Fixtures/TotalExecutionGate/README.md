# Total execution regression corpus

This corpus protects the migration from partial official execution to a total,
typed execution interface.

Run:

```sh
cd hypostructure
scripts/check_total_execution.py --self-test
scripts/check_total_execution.py
```

The self-test must always pass. The production scan is expected to fail while
the migration is incomplete, and becomes a green regression gate once the
reported Core/Graph/PDE execution-boundary occurrences have been removed.

Positive fixtures deliberately include ordinary mathematical `Option` use and
an intended total dispatcher shape. Negative fixtures independently cover:

- `Option (Decision ...)`;
- failure-bearing execution results;
- `unsupported`, `incompatibleJoin`, and `fuelExhausted` outcomes;
- wildcard production dispatch falling through to `none`.

The scanner removes Lean comments and strings before matching and scans only
official execution/compiler boundary filenames. It therefore does not ban
ordinary `Option`-valued mathematics in strategy feature modules.
