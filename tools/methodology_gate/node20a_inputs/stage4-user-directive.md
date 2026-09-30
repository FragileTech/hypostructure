# Stage 4/5 directive from the user (operator-relayed; context, not a fact about G)

The accepted Stage 3 handle is a03. It fixes a concrete positive certificate `c` of
`glue ret_P O` and a concrete private passage `q` on it:
active label `a` → private internal `y` (y ∈ P∖N) → active label `b`.

1. Stage 3 rejected the required joint candidate partly because "R bag and chain
   bounds are not ledger premises". That reason is now stale. On g-repair-base at
   4519bdd they are ledger facts of G carried by the `[20a]` residual:
   * `K .remainderPathBounds` (idx 7211);
   * `K .inducedPathAttachment` (idx 7213);
   * the hub-link keys (idx 7217–7222);
   * `K .windowChargeKinds` (idx 7215).

   Their statements are in scope: `port-joint-register-excerpt.md` and
   `Graph/Statements/{JointHubs,HubLinks,PairArms}.lean`.
2. The Stage 4 move catalogue for the a03 question must test the passage `q` and
   the rest of the same `c` against these facts as premises, together with the
   local facts:
   * `windowPositionStubs` and `windowAttachmentGap`, on the segments where `c`
     crosses windows of `P₀`;
   * `inducedPathAttachment`, for `y`'s neighbours on induced P13s;
   * `remainderPathBounds`, for the segments of `c` inside `R`;
   * `threeRouteFan`, `threeRouteChain` and `portEndDegree`, at high vertices on `c`.

   This combination is attached to the concrete cycle `c` and the concrete
   passage `q`. It is not a free-floating spectrum argument, so the objection
   that the returns need not run b→a does not apply to it.
3. Stage 5: every authorized outcome must exclude a configuration in the weakest
   case, `c18_02 ∩ c16_04 ∩ c12_04 ∩ (c14_03 / c14_04)`. An outcome that only
   adds facts without excluding a configuration is not productive.
4. Do not repeat the approaches in `known-failed-approaches.md` (F1–F6) without
   the new ingredient that addresses exactly why each one failed.
