P7-int-lift — integration audit of accepted P6-S1-lift, on `node20a-stage3b-S1@7d3186b`.

The accepted exports satisfy child obligation 2 of `tools/methodology_gate/node20a_inputs/taskflow/stage3b-context.md` §3, line 71, on the retained tuple and exact child-1 interval. No statement or domain mismatch was found. This is an audit submission for controller review, not a branch closure or a Stage 3b publication.

Source locators below use `S1child2.lean` and `S1child1.lean` for the files in `tools/methodology_gate/node20a_inputs/taskflow/`, and `residual-record.md` for `tools/methodology_gate/node20a_inputs/residual-record.md`. All ten hashes in the supplied source manifest were checked and match. In particular, the accepted child-2 bytes have SHA-256 `3c434451d1d2fdc3ef6eb3a8c50288788fcf40ad066c68f8a90dbd807f655064`.

The fixed parameters are `G = selected.object`, `data = spineData.toParameters`, the f021 canonical `w` with `w.Spec`, `Z = w.support`, `O = w.outside`, and the original declared coordinates `w.first,w.second` with supports `A,B`. The f118 orientation identifies `(P,N)` with `(A,B)` or `(B,A)`; it does not introduce new supports (`Statements/SparseExitReadings.lean`, lines 116–122). The certificate has exactly the domain `CycleCertificate (glue (SupportAtom.retainedPiece G Z P) O) data.LengthOK`. Its supplied `pl,pr` have type `(SupportAtom.boundary G Z).Vertex ⊕ SupportAtom.PieceInternal G Z`, and `y = SupportAtom.pieceDecode G Z pr`.

For an already bound tuple and interval, the integration entry point is `Hypostructure.Graph.S1child2.lift_on_residual`. Its complete declaration and proof are quoted verbatim from `S1child2.lean`, lines 534–561:

```lean
theorem lift_on_residual {selected : EGInput.{u}}
    (residual : Node20aOutcome selected)
    (w : SparseTargetDefectWitness spineData.{u}.toParameters selected.object)
    (_canonical : sparseTargetDefectWitness spineData.{u}.toParameters selected.object = some w)
    (spec : w.Spec) {P N : Finset selected.object.Vertex}
    (orientation : w.Orientation P N) (_separates : w.Separates P N)
    (_private : w.CyclesUsePrivateEdge P N)
    (c : CycleCertificate
      (glue (SupportAtom.retainedPiece selected.object w.support P) w.outside)
      spineData.{u}.toParameters.LengthOK)
    (pl pr : (SupportAtom.boundary selected.object w.support).Vertex ⊕
      SupportAtom.PieceInternal selected.object w.support)
    (supplied :
      s(pieceEmbedding (SupportAtom.retainedPiece selected.object w.support P) w.outside pl,
        pieceEmbedding (SupportAtom.retainedPiece selected.object w.support P) w.outside pr)
        ∈ c.walk.edges ∧
      selected.object.graph.Adj (SupportAtom.pieceDecode selected.object w.support pl)
        (SupportAtom.pieceDecode selected.object w.support pr) ∧
      SupportAtom.pieceDecode selected.object w.support pl ∈ P ∧
      SupportAtom.pieceDecode selected.object w.support pr ∈ P ∧
      SupportAtom.pieceDecode selected.object w.support pr ∉ N ∧
      SupportAtom.pieceDecode selected.object w.support pr ∉
        SupportAtom.cutBoundary selected.object w.support)
    (I : BoundaryInterval c
      (pieceEmbedding (SupportAtom.retainedPiece selected.object w.support P) w.outside pr)) :
    Node20aOutcome selected ∧ Nonempty (PositiveLift I) := by
  exact ⟨residual, restrict_interval I supplied.2.2.2.2.2
    (positive_subset_support w spec orientation)⟩
```

This accepts the original `c`, supplied `pl,pr` and their full f118 conjunction, and the exact `I`; it does not eliminate f118 again. The only additional inputs to `restrict_interval` are the supplied internality conclusion and `P ⊆ w.support`, already supplied by `positive_subset_support w spec orientation` (lines 519–527). Thus no extra hypothesis is owed by the retained branch. Canonicality, separation and the cycle-private universal remain parameters even though the local restriction only needs their already supplied consequences.

The dependent result type is quoted verbatim from `S1child2.lean`, lines 422–448:

```lean
structure PositiveLift {G : FiniteObject.{u}} {Z P : Finset G.Vertex}
    {O : OutsideContext (SupportAtom.boundary G Z)} {LengthOK : Nat → Prop}
    {c : CycleCertificate (glue (SupportAtom.retainedPiece G Z P) O) LengthOK}
    {pr : (SupportAtom.boundary G Z).Vertex ⊕ SupportAtom.PieceInternal G Z}
    (I : BoundaryInterval c (pieceEmbedding (SupportAtom.retainedPiece G Z P) O pr)) where
  piece_vertices : ∀ v ∈ I.q.support,
    ∃ p, pieceEmbedding (SupportAtom.retainedPiece G Z P) O p = v
  piece_edges : ∀ v z, s(v, z) ∈ I.q.edges →
    PieceOwns (SupportAtom.retainedPiece G Z P) O v z
  walk : (SupportAtom.retainedPiece G Z P).graph.Walk (.inl I.a) (.inl I.b)
  simple : walk.IsPath
  maps_to_q : walk.map (pieceHom (SupportAtom.retainedPiece G Z P) O) = I.q
  vertex_order : I.q.support =
    walk.support.map (pieceEmbedding (SupportAtom.retainedPiece G Z P) O)
  edge_order : I.q.edges =
    walk.edges.map (Sym2.map (pieceEmbedding (SupportAtom.retainedPiece G Z P) O))
  length_eq : walk.length = I.q.length
  length_two : 2 ≤ walk.length
  private_occurrence : walk.getVert I.private_index = pr
  decode_injective : Function.Injective (SupportAtom.pieceDecode G Z)
  decoded_simple : (walk.map (GluedReadings.readingHom Z P)).IsPath
  decoded_in_P : ∀ v ∈ (walk.map (GluedReadings.readingHom Z P)).support, v ∈ P
  decoded_in_Z : ∀ v ∈ (walk.map (GluedReadings.readingHom Z P)).support, v ∈ Z
  decoded_private_occurrence :
    (walk.map (GluedReadings.readingHom Z P)).getVert I.private_index =
      SupportAtom.pieceDecode G Z pr
  reading_subset : P ⊆ Z
```

The child-2 contract matches these fields as follows. The interval remains a `S1child1.BoundaryInterval` throughout.

| Required assertion at §3, child 2 | Accepted export and identity check |
| --- | --- |
| Every vertex of the same `q` is in the piece embedding; every edge is piece-owned | `piece_vertices` and `piece_edges`, lines 427–430, quantify over `I.q.support` and `I.q.edges`. |
| A simple retained-piece walk of that segment, with the same vertex and edge order | `walk`, `simple`, `maps_to_q`, `vertex_order`, `edge_order`, lines 431–437. `maps_to_q` is equality of walks to `I.q`; the next two equalities are ordered list equalities, not just equal lengths or sets. |
| Length at least two | `length_eq` and `length_two`, lines 438–439. |
| The same internal private occurrence | `private_occurrence`, line 440, uses `I.private_index` and the supplied `pr`; `decoded_private_occurrence`, lines 445–447, gives the same decoded `y`. |
| Injective decoding into `G`, with every vertex in `P ⊆ Z` | `decode_injective`, `decoded_simple`, `decoded_in_P`, `decoded_in_Z`, and `reading_subset`, lines 441–448. The ambient walk is the map of this very `walk` by `GluedReadings.readingHom Z P`. |

The original cyclic order is still present in `I`. The accepted `BoundaryInterval` fields give distinct labels, their occurrences on `c`, the actual walks `q,r`, `c.walk.rotate (.inl a) a_occurs = q.append r`, the length partition, properness, positive complementary length, simplicity, a strictly internal private index, and no internal boundary occurrence (`S1child1.lean`, lines 176–196; embedded in `S1child2.lean`, lines 179–199). This carries the original wraparound case and complementary arc into the lift. Neither the certificate nor its ordered passage is replaced.

The ownership argument is already accepted: `interval_piece_owned` applies `GluedReadings.arc_owned` to `I.q` with `I.distinct`, `I.simple` and the no-internal-label condition; the context-owned alternative cannot contain the supplied piece-internal occurrence (lines 376–401). `restrict_interval` uses the accepted `DefectGeometry.liftWalk` on that same `I.q`, with the original endpoint labels (lines 452–515). These observations match the prerequisite domains; they do not re-prove either accepted child.

For a consumer entering from the whole conjunction, the exported proposition and theorem signature are exactly the following (`S1child2.lean`, lines 566–595; all names are in `Hypostructure.Graph.S1child2`):

```lean
def CyclesHaveLiftedFirstContacts {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G) (P N : Finset G.Vertex) : Prop :=
  ∀ c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
      data.LengthOK,
    ∃ pl pr : (SupportAtom.boundary G w.support).Vertex ⊕ SupportAtom.PieceInternal G w.support,
      (s(pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pl,
         pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr) ∈ c.walk.edges ∧
       G.graph.Adj (SupportAtom.pieceDecode G w.support pl)
         (SupportAtom.pieceDecode G w.support pr) ∧
       SupportAtom.pieceDecode G w.support pl ∈ P ∧
       SupportAtom.pieceDecode G w.support pr ∈ P ∧
       SupportAtom.pieceDecode G w.support pr ∉ N ∧
       SupportAtom.pieceDecode G w.support pr ∉ SupportAtom.cutBoundary G w.support) ∧
      ∃ I : BoundaryInterval c
        (pieceEmbedding (SupportAtom.retainedPiece G w.support P) w.outside pr),
        Nonempty (PositiveLift I)

/-- Apply child 2 to the accepted child-1 witnesses on the whole original
conjunction, preserving its canonical witness, orientation, exclusions and
all supplied private-edge data for every original positive certificate. -/
theorem node20a_lift_firstContacts {selected : EGInput.{u}}
    (residual : Node20aOutcome selected) :
    Node20aOutcome selected ∧
    ∃ w : SparseTargetDefectWitness spineData.{u}.toParameters selected.object,
      sparseTargetDefectWitness spineData.{u}.toParameters selected.object = some w ∧ w.Spec ∧
      ∃ P N : Finset selected.object.Vertex,
        w.Orientation P N ∧ w.Separates P N ∧ w.CyclesUsePrivateEdge P N ∧
        ¬ ((SupportAtom.retainedPiece selected.object w.support P).graph ≤
          (SupportAtom.retainedPiece selected.object w.support N).graph) ∧
        CyclesHaveLiftedFirstContacts w P N := by
```

The aggregate proof obtains `kept,w,canonical,spec,P,N,orientation,separates,privateEdge,notLe,contacts` directly from accepted `S1child1.node20a_firstContacts residual`, and for each original `c` obtains `pl,pr,supplied,I` from `contacts c`. It then passes those exact terms to `lift_on_residual` (lines 596–603). The embedded child-1 proof binds `w` from f021, identifies the f118 witness with it using `Option.some.inj`, retains that orientation and `notLe`, and obtains `pl,pr,supplied` by applying `privateEdge` to the same `c` (lines 346–359). The aggregate existential therefore extends the accepted witnesses. For a consumer that has already fixed a particular `P,N,pl,pr,I`, the fixed-input entry point above is the precise interface; no uniqueness of the existential orientation, endpoints or interval is asserted or required.

Full residual retention is explicit, rather than a reconstruction from selected facts. `lift_on_residual` returns `⟨residual, ...⟩` (lines 559–561); `node20a_lift_firstContacts` returns the `kept` conjunction obtained from child 1 (lines 588 and 596–598), whose constructor returns the original `residual` (embedded line 354). `Node20aOutcome selected` is exactly the 128-conjunct abbreviation in `residual-record.md`, lines 25–281. Hence f001 selection/minimality and target avoidance, all exclusions, all independent witnesses, and f021–f128 remain at the same selected `G`. In particular f029 and f115 are retained even when not used by this restriction, and f118's orientation, separation, private-edge universal and `notLe` are also returned explicitly. The incoming alternative, accepted Stage 1–3 data, branch endpoint and empty accounts are unchanged.

The next consumer receives the complete conjunction together with the same canonical tuple and, for each original positive `c`, its f118 supplied conjunction, `I`, and `Nonempty (PositiveLift I)`. After eliminating that `Nonempty` in its proof, it has the concrete retained-piece walk between `.inl I.a` and `.inl I.b`, its length bound, its exact maps and ordered lists, the decoded simple `G`-walk in `P ⊆ Z`, and the original private occurrence. The fixed-input entry point supplies the same package for any interval already furnished by child 1.

The stated subsequent consumer in `stage3b-context.md`, line 73, is child 3 on these exact endpoints: it is to use the first and last edges of this lifted walk, reading-count positivity and retained f115, with the retained orientation, to establish active common labels and positive equal counts at `I.a,I.b`. Those endpoint conclusions are not fields of `PositiveLift` and are not claimed here. The Stage 3b owner can use this extraction-and-lift component in its S1 projection; the owner-local `FactInputs`/`ExactLedger` row and publication, and the remaining S1–S3 work, remain at their stated stage boundaries (context lines 42–52 and 73–75). This audit neither executes nor assigns that work.

There is no added assumption of exactly two boundary labels, a whole reading, high `y`, a realization of `O` or a reading, or a two-terminal spectrum path. The retained weakest-case setting in context line 87 remains in scope. `I.r` stays available as part of `I`; the accepted output asserts no lift or transfer for that complementary arc.

Verification for this audit consists of the pinned hash checks and the statement/interface comparisons above. The accepted P6 result supplies the kernel-checked status of `S1child2.lean`; its axiom-audit declarations are at lines 607–610. No new Lean implementation or kernel run was needed or performed, so this audit's `implementation_status` is `none`. There is no missing inference within this integration task, and no immediate subobligation is opened.

Side observation, recorded without follow-up: the standalone child-2 file embeds accepted child 1 verbatim because its compiled module is absent from the read-only cache (`S1child2.lean`, lines 1–3 and 367). This is an existing packaging choice; this audit changes no representation, domain, source, or account.
