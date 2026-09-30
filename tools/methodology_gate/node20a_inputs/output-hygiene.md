# Worker output hygiene (operator note; no mathematics)

The controller keeps only `/output/record` and `/output/changes`, and it rejects any
symlink anywhere under `/output`. A Lake workspace or `build/` tree left in `/output`
therefore causes a rejection before review. This already happened once, to Stage 3b
attempt `89bb279b…`.

Put scratch builds and Lake workspaces under `/tmp`, or under a subdirectory of
`/output` that you delete before you finish. When you finish, `/output` must hold no
symlinks and no build products.
