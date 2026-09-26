# Total execution regression corpus

This corpus protects the migration from partial official execution to a total,
typed execution interface.

Run:

```sh
cd hypostructure
scripts/check_total_execution.py --self-test
scripts/check_total_execution.py
```

The self-test must always pass. The production scan runs in `make lint` and
passes: no file under `Core`, `Graph` or `PDE` currently matches its boundary
filter, so it checks zero files and fails only if such a boundary file
reappears with a forbidden construct.

Positive fixtures deliberately include ordinary mathematical `Option` use and
an intended total dispatcher shape. Negative fixtures independently cover:

- `Option (Decision ...)`;
- failure-bearing execution results;
- `unsupported`, `incompatibleJoin`, and `fuelExhausted` outcomes;
- wildcard production dispatch falling through to `none`.

The scanner removes Lean comments and strings before matching and scans only
official execution/compiler boundary files: `Compiler.lean`,
`DependentExecutor.lean`, `Execution.lean`, `ExecutionJson.lean`,
`Executor.lean` and `Report.lean` inside an `Official` directory. It therefore
does not ban ordinary `Option`-valued mathematics in strategy feature modules.
