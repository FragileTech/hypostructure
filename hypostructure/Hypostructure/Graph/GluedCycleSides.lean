import Hypostructure.Graph.GluedCrossingCycle

/-!
# Side alternation of glued cycles

`lem:typeA-pressure-token-two-carriers`' geometric core at an arbitrary
outside context: crossing between the piece side and the context side of a
gluing passes through a boundary label, and a cycle that meets both interiors
therefore visits **two distinct** boundary labels.  This is the paper's "a
cycle crosses a cut an even number of times, and a simple cycle cannot use one
cut edge twice", stated on the glued carrier itself so that it applies to the
realizations of a demand token whose context is not the actual exterior.
Everything is over the raw glued graph `glueGraph`, which is definitionally
the graph of `glue`; nothing here mentions a support, a token, or a
presentation constant.
-/

namespace Hypostructure.Graph.GluedCycleSides

open Hypostructure
open Hypostructure.Graph

universe u

variable {boundary : Boundary.{u}}
variable {piece : BoundaryPiece boundary} {outside : OutsideContext boundary}

/-- A context-owned adjacency never touches a piece-internal vertex. -/
theorem not_contextOwns_piece_internal {inner : piece.Internal}
    {other : GluedVertex piece outside}
    (owns : ContextOwns piece outside (.inr (.inl inner)) other) : False := by
  obtain ⟨contextLeft, _contextRight, _adj, leftEq, _rightEq⟩ := owns
  rcases contextLeft with label | context <;>
    simp [contextEmbedding] at leftEq

/-- A piece-owned adjacency never touches a context-internal vertex. -/
theorem not_pieceOwns_context_internal {inner : outside.Internal}
    {other : GluedVertex piece outside}
    (owns : PieceOwns piece outside (.inr (.inr inner)) other) : False := by
  obtain ⟨pieceLeft, _pieceRight, _adj, leftEq, _rightEq⟩ := owns
  rcases pieceLeft with label | inside <;>
    simp [pieceEmbedding] at leftEq

/-- **Crossing sides passes through a label**: a glued walk from a
piece-internal vertex to a context-internal vertex visits some boundary
label. -/
theorem exists_label_of_walk_sides :
    ∀ {start finish : GluedVertex piece outside}
      (walk : (glueGraph piece outside).Walk start finish),
      (∃ inner : piece.Internal, start = .inr (.inl inner)) →
      (∃ inner : outside.Internal, finish = .inr (.inr inner)) →
      ∃ label : boundary.Vertex,
        (Sum.inl label : GluedVertex piece outside) ∈ walk.support := by
  intro start finish walk
  induction walk with
  | nil =>
      rintro ⟨innerP, rfl⟩ ⟨innerC, equal⟩
      simp at equal
  | @cons u b v adjacent rest ih =>
      rintro ⟨innerP, rfl⟩ vContext
      rcases b with label | pieceOrContext
      · refine ⟨label, ?_⟩
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ rest.start_mem_support
      · rcases pieceOrContext with innerP' | innerC'
        · obtain ⟨label, member⟩ := ih ⟨innerP', rfl⟩ vContext
          refine ⟨label, ?_⟩
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ member
        · exfalso
          rcases (glueGraph_adj_iff piece outside _ _).mp adjacent with
            pieceOwn | contextOwn
          · obtain ⟨pieceLeft, pieceRight, _adj, _leftEq, rightEq⟩ := pieceOwn
            rcases pieceRight with label | inside <;>
              simp [pieceEmbedding] at rightEq
          · exact not_contextOwns_piece_internal contextOwn

/-- The mirror: from a context-internal vertex to a piece-internal vertex. -/
theorem exists_label_of_walk_sides'
    {start finish : GluedVertex piece outside}
    (walk : (glueGraph piece outside).Walk start finish)
    (startContext : ∃ inner : outside.Internal, start = .inr (.inr inner))
    (finishPiece : ∃ inner : piece.Internal, finish = .inr (.inl inner)) :
    ∃ label : boundary.Vertex,
      (Sum.inl label : GluedVertex piece outside) ∈ walk.support := by
  obtain ⟨label, member⟩ :=
    exists_label_of_walk_sides walk.reverse finishPiece startContext
  refine ⟨label, ?_⟩
  rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at member

/-- **A glued cycle meeting both interiors visits two distinct boundary
labels** (`lem:typeA-pressure-token-two-carriers`' cut parity at an arbitrary
outside context): rotating the cycle to the piece-internal vertex and
splitting at the context-internal vertex, each arc crosses sides through a
label, and the cycle's simplicity keeps the two labels distinct. -/
theorem exists_two_labels_of_cycle_sides
    {base : GluedVertex piece outside}
    {c : (glueGraph piece outside).Walk base base} (cycle : c.IsCycle)
    {pieceInner : piece.Internal} {contextInner : outside.Internal}
    (pieceMem : (Sum.inr (Sum.inl pieceInner) : GluedVertex piece outside) ∈
      c.support)
    (contextMem : (Sum.inr (Sum.inr contextInner) : GluedVertex piece outside) ∈
      c.support) :
    ∃ left right : boundary.Vertex, left ≠ right ∧
      (Sum.inl left : GluedVertex piece outside) ∈ c.support ∧
      (Sum.inl right : GluedVertex piece outside) ∈ c.support := by
  classical
  set rotated := c.rotate (Sum.inr (Sum.inl pieceInner)) pieceMem
    with rotatedDef
  have rotatedCycle : rotated.IsCycle := cycle.rotate pieceMem
  have QmemRot : (Sum.inr (Sum.inr contextInner) : GluedVertex piece outside) ∈
      rotated.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c _ pieceMem).mpr contextMem
  set w1 := rotated.takeUntil _ QmemRot with w1Def
  set w2 := rotated.dropUntil _ QmemRot with w2Def
  obtain ⟨l1, l1Mem⟩ := exists_label_of_walk_sides w1
    ⟨pieceInner, rfl⟩ ⟨contextInner, rfl⟩
  obtain ⟨l2, l2Mem⟩ := exists_label_of_walk_sides' w2
    ⟨contextInner, rfl⟩ ⟨pieceInner, rfl⟩
  have l1C : (Sum.inl l1 : GluedVertex piece outside) ∈ c.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c _ pieceMem).mp
      (SimpleGraph.Walk.support_takeUntil_subset_support rotated QmemRot l1Mem)
  have l2C : (Sum.inl l2 : GluedVertex piece outside) ∈ c.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c _ pieceMem).mp
      (SimpleGraph.Walk.support_dropUntil_subset_support rotated QmemRot l2Mem)
  refine ⟨l1, l2, ?_, l1C, l2C⟩
  intro same
  subst same
  have neP : (Sum.inl l1 : GluedVertex piece outside) ≠
      .inr (.inl pieceInner) := by simp
  have neQ : (Sum.inl l1 : GluedVertex piece outside) ≠
      .inr (.inr contextInner) := by simp
  have l1Tail : (Sum.inl l1 : GluedVertex piece outside) ∈
      w1.support.tail := by
    rcases (SimpleGraph.Walk.mem_support_iff w1).mp l1Mem with headEq | tailMem
    · exact absurd headEq neP
    · exact tailMem
  have l2Tail : (Sum.inl l1 : GluedVertex piece outside) ∈
      w2.support.tail := by
    rcases (SimpleGraph.Walk.mem_support_iff w2).mp l2Mem with headEq | tailMem
    · exact absurd headEq neQ
    · exact tailMem
  have spec := SimpleGraph.Walk.take_spec rotated QmemRot
  have supportSplit : rotated.support = w1.support ++ w2.support.tail := by
    conv_lhs => rw [← spec]
    exact SimpleGraph.Walk.support_append w1 w2
  have tailSplit : rotated.support.tail =
      w1.support.tail ++ w2.support.tail := by
    rw [supportSplit, SimpleGraph.Walk.support_eq_cons w1]
    rfl
  have nodup := rotatedCycle.support_nodup
  rw [tailSplit] at nodup
  exact ((List.nodup_append.mp nodup).2.2 _ l1Tail _ l2Tail) rfl

section Trichotomy

/-- **Walk lift or context label edge**: a glued walk between piece-side
vertices that avoids the context's internal vertices either lifts to the piece
— with matching length, support and edges — or uses a context-owned edge
between two distinct boundary labels, both visited. -/
theorem exists_pieceWalk_or_labelDart :
    ∀ {start finish : GluedVertex piece outside}
      (walk : (glueGraph piece outside).Walk start finish)
      {pieceStart pieceFinish : boundary.Vertex ⊕ piece.Internal},
      start = pieceEmbedding piece outside pieceStart →
      finish = pieceEmbedding piece outside pieceFinish →
      (∀ inner : outside.Internal,
        (Sum.inr (Sum.inr inner) : GluedVertex piece outside) ∉
          walk.support) →
      (∃ lifted : piece.graph.Walk pieceStart pieceFinish,
        lifted.length = walk.length ∧
          walk.support =
            lifted.support.map (pieceEmbedding piece outside) ∧
          walk.edges =
            lifted.edges.map (Sym2.map (pieceEmbedding piece outside))) ∨
      (∃ left right : boundary.Vertex, left ≠ right ∧
        (Sum.inl left : GluedVertex piece outside) ∈ walk.support ∧
        (Sum.inl right : GluedVertex piece outside) ∈ walk.support ∧
        outside.graph.Adj (.inl left) (.inl right) ∧
        s(Sum.inl left, Sum.inl right) ∈ walk.edges) := by
  intro start finish walk
  induction walk with
  | nil =>
      intro pieceStart pieceFinish startEq finishEq _noContext
      have same : pieceStart = pieceFinish :=
        (pieceEmbedding piece outside).injective
          (startEq.symm.trans finishEq)
      subst same
      refine Or.inl ⟨.nil, rfl, ?_, rfl⟩
      simp [startEq]
  | @cons u b v adjacent rest ih =>
      intro pieceStart pieceFinish startEq finishEq noContext
      have noContextRest : ∀ inner : outside.Internal,
          (Sum.inr (Sum.inr inner) : GluedVertex piece outside) ∉
            rest.support := by
        intro inner member
        refine noContext inner ?_
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ member
      -- the middle vertex is on the piece side
      obtain ⟨bPiece, bEq⟩ : ∃ bPiece : boundary.Vertex ⊕ piece.Internal,
          b = pieceEmbedding piece outside bPiece := by
        rcases b with label | pieceOrContext
        · exact ⟨.inl label, rfl⟩
        · rcases pieceOrContext with pieceInner | contextInner
          · exact ⟨.inr pieceInner, rfl⟩
          · exfalso
            refine noContext contextInner ?_
            rw [SimpleGraph.Walk.support_cons]
            exact List.mem_cons_of_mem _ rest.start_mem_support
      rcases (glueGraph_adj_iff piece outside _ _).mp adjacent with
        pieceOwn | contextOwn
      · obtain ⟨pieceLeft, pieceRight, adj, plEq, prEq⟩ := pieceOwn
        have plIs : pieceLeft = pieceStart :=
          (pieceEmbedding piece outside).injective (plEq.trans startEq)
        have prIs : pieceRight = bPiece :=
          (pieceEmbedding piece outside).injective (prEq.trans bEq)
        subst plIs
        subst prIs
        rcases ih bEq finishEq noContextRest with
          ⟨lifted, liftedLength, liftedSupport, liftedEdges⟩ | dart
        · refine Or.inl ⟨.cons adj lifted, ?_, ?_, ?_⟩
          · rw [SimpleGraph.Walk.length_cons,
              SimpleGraph.Walk.length_cons, liftedLength]
          · rw [SimpleGraph.Walk.support_cons,
              SimpleGraph.Walk.support_cons, liftedSupport, List.map_cons,
              startEq]
          · rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons,
              liftedEdges, List.map_cons, startEq, bEq]
            rfl
        · obtain ⟨left, right, distinct, leftMem, rightMem, contextAdj,
            edgeMem⟩ := dart
          refine Or.inr ⟨left, right, distinct, ?_, ?_, contextAdj, ?_⟩
          · rw [SimpleGraph.Walk.support_cons]
            exact List.mem_cons_of_mem _ leftMem
          · rw [SimpleGraph.Walk.support_cons]
            exact List.mem_cons_of_mem _ rightMem
          · rw [SimpleGraph.Walk.edges_cons]
            exact List.mem_cons_of_mem _ edgeMem
      · obtain ⟨contextLeft, contextRight, adj, clEq, crEq⟩ := contextOwn
        -- both endpoints of a context edge with no context internal in the
        -- support are boundary labels
        obtain ⟨leftLabel, clIs⟩ : ∃ label : boundary.Vertex,
            contextLeft = .inl label := by
          rcases contextLeft with label | inner
          · exact ⟨label, rfl⟩
          · exfalso
            refine noContext inner ?_
            have : u = .inr (.inr inner) := by
              simp [contextEmbedding] at clEq
              exact clEq.symm
            rw [SimpleGraph.Walk.support_cons]
            exact this ▸ List.mem_cons_self
        obtain ⟨rightLabel, crIs⟩ : ∃ label : boundary.Vertex,
            contextRight = .inl label := by
          rcases contextRight with label | inner
          · exact ⟨label, rfl⟩
          · exfalso
            refine noContext inner ?_
            have : b = .inr (.inr inner) := by
              simp [contextEmbedding] at crEq
              exact crEq.symm
            rw [SimpleGraph.Walk.support_cons]
            exact List.mem_cons_of_mem _ (this ▸ rest.start_mem_support)
        subst clIs
        subst crIs
        have uIs : u = .inl leftLabel := by
          simp [contextEmbedding] at clEq
          exact clEq.symm
        have bIs : b = .inl rightLabel := by
          simp [contextEmbedding] at crEq
          exact crEq.symm
        have distinct : leftLabel ≠ rightLabel := by
          intro same
          exact adjacent.ne (by rw [uIs, bIs, same])
        refine Or.inr ⟨leftLabel, rightLabel, distinct, ?_, ?_, adj, ?_⟩
        · rw [SimpleGraph.Walk.support_cons]
          exact uIs ▸ List.mem_cons_self
        · rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ (bIs ▸ rest.start_mem_support)
        · rw [SimpleGraph.Walk.edges_cons]
          have edgeEq : s(u, b) =
              s((Sum.inl leftLabel : GluedVertex piece outside),
                Sum.inl rightLabel) := by
            rw [uIs, bIs]
          rw [← edgeEq]
          exact List.mem_cons_self

/-- **General classification of a glued cycle**: it lifts to a piece cycle of
the same length, or it meets a context-internal vertex, or it uses a
context-owned edge between two distinct boundary labels, both visited. -/
theorem cycle_pieceLift_or_contextInternal_or_labelDart
    {base : GluedVertex piece outside}
    {c : (glueGraph piece outside).Walk base base} (cycle : c.IsCycle) :
    (∃ (pieceBase : boundary.Vertex ⊕ piece.Internal)
      (lifted : piece.graph.Walk pieceBase pieceBase),
        lifted.IsCycle ∧ lifted.length = c.length) ∨
    (∃ inner : outside.Internal,
      (Sum.inr (Sum.inr inner) : GluedVertex piece outside) ∈ c.support) ∨
    (∃ left right : boundary.Vertex, left ≠ right ∧
      (Sum.inl left : GluedVertex piece outside) ∈ c.support ∧
      (Sum.inl right : GluedVertex piece outside) ∈ c.support ∧
      outside.graph.Adj (.inl left) (.inl right) ∧
      s(Sum.inl left, Sum.inl right) ∈ c.edges) := by
  classical
  by_cases contextMeet : ∃ inner : outside.Internal,
      (Sum.inr (Sum.inr inner) : GluedVertex piece outside) ∈ c.support
  · exact Or.inr (Or.inl contextMeet)
  push_neg at contextMeet
  obtain ⟨pieceBase, baseEq⟩ : ∃ pieceBase : boundary.Vertex ⊕ piece.Internal,
      base = pieceEmbedding piece outside pieceBase := by
    rcases base with label | pieceOrContext
    · exact ⟨.inl label, rfl⟩
    · rcases pieceOrContext with pieceInner | contextInner
      · exact ⟨.inr pieceInner, rfl⟩
      · exact absurd c.start_mem_support (contextMeet contextInner)
  rcases exists_pieceWalk_or_labelDart c baseEq baseEq contextMeet with
    ⟨lifted, liftedLength, liftedSupport, liftedEdges⟩ | dart
  · refine Or.inl ⟨pieceBase, lifted, ?_, liftedLength⟩
    refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
    · have cEdgesNodup := cycle.edges_nodup
      rw [liftedEdges] at cEdgesNodup
      exact cEdgesNodup.of_map
    · intro liftedNil
      have liftedZero : lifted.length = 0 := by rw [liftedNil]; rfl
      have := cycle.three_le_length
      omega
    · have cTailNodup := cycle.support_nodup
      have tailEq : c.support.tail = lifted.support.tail.map
          (pieceEmbedding piece outside) := by
        rw [liftedSupport]
        simp only [List.map_tail]
      rw [tailEq] at cTailNodup
      exact cTailNodup.of_map
  · exact Or.inr (Or.inr dart)

end Trichotomy

section Corridor

/-! `def:typeA-two-terminal-pressure-records`' geometric core: the *actual
outside corridor*.  A glued cycle that leaves through the context side
contains a subwalk between two **distinct** boundary labels all of whose
other vertices are context-internal — the manuscript's pair of consecutive
boundary crossings bounding an outside subpath. -/

/-- **The context side exits through a label**: a glued walk from a
context-internal vertex to a boundary label has an initial stretch reaching
some label entirely through context-internal vertices, along walk edges. -/
theorem exists_context_lead_to_label :
    ∀ {start finish : GluedVertex piece outside}
      (walk : (glueGraph piece outside).Walk start finish),
      (∃ inner : outside.Internal, start = .inr (.inr inner)) →
      (∃ label : boundary.Vertex, finish = .inl label) →
      ∃ (label : boundary.Vertex)
        (lead : (glueGraph piece outside).Walk start (.inl label)),
        lead.edges ⊆ walk.edges ∧
        lead.support ⊆ walk.support ∧
        ∀ x ∈ lead.support,
          x = (Sum.inl label : GluedVertex piece outside) ∨
          ∃ inner : outside.Internal, x = .inr (.inr inner) := by
  intro start finish walk
  induction walk with
  | nil =>
      rintro ⟨inner, rfl⟩ ⟨label, equal⟩
      simp at equal
  | @cons u b v adjacent rest ih =>
      rintro ⟨inner, rfl⟩ finishLabel
      rcases b with label | pieceOrContext
      · -- immediate exit through the label
        refine ⟨label, .cons adjacent .nil, ?_, ?_, ?_⟩
        · intro e emem
          rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil]
            at emem
          rw [SimpleGraph.Walk.edges_cons]
          exact (List.mem_singleton.mp emem) ▸ List.mem_cons_self
        · intro x xmem
          rw [SimpleGraph.Walk.support_cons] at xmem
          rw [SimpleGraph.Walk.support_cons]
          rcases List.mem_cons.mp xmem with rfl | tailmem
          · exact List.mem_cons_self
          · rw [SimpleGraph.Walk.support_nil] at tailmem
            refine List.mem_cons_of_mem _ ?_
            rw [List.mem_singleton.mp tailmem]
            exact rest.start_mem_support
        · intro x xmem
          rw [SimpleGraph.Walk.support_cons] at xmem
          rcases List.mem_cons.mp xmem with rfl | tailmem
          · exact Or.inr ⟨inner, rfl⟩
          · rw [SimpleGraph.Walk.support_nil] at tailmem
            exact Or.inl (List.mem_singleton.mp tailmem)
      · rcases pieceOrContext with pieceInner | contextInner'
        · -- a context-internal vertex is never glue-adjacent to a
          -- piece-internal one
          exfalso
          rcases (glueGraph_adj_iff piece outside _ _).mp adjacent with
            pieceOwn | contextOwn
          · exact not_pieceOwns_context_internal pieceOwn
          · obtain ⟨_contextLeft, contextRight, _adj, _clEq, crEq⟩ :=
              contextOwn
            rcases contextRight with lab | ctx <;>
              simp [contextEmbedding] at crEq
        · -- continue through the context side
          obtain ⟨label, lead, leadEdges, leadSupport, leadChar⟩ :=
            ih ⟨contextInner', rfl⟩ finishLabel
          refine ⟨label, .cons adjacent lead, ?_, ?_, ?_⟩
          · intro e emem
            rw [SimpleGraph.Walk.edges_cons] at emem
            rw [SimpleGraph.Walk.edges_cons]
            rcases List.mem_cons.mp emem with rfl | tailmem
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (leadEdges tailmem)
          · intro x xmem
            rw [SimpleGraph.Walk.support_cons] at xmem
            rw [SimpleGraph.Walk.support_cons]
            rcases List.mem_cons.mp xmem with rfl | tailmem
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (leadSupport tailmem)
          · intro x xmem
            rw [SimpleGraph.Walk.support_cons] at xmem
            rcases List.mem_cons.mp xmem with rfl | tailmem
            · exact Or.inr ⟨inner, rfl⟩
            · exact leadChar x tailmem

/-- **The outside corridor inside a duplicate-free label-to-label walk**: a
walk between two boundary labels with no repeated vertex that visits a
context-internal vertex contains a corridor — a subwalk between two
**distinct** labels all of whose other vertices are context-internal. -/
theorem exists_corridor_of_path_labels {A B : boundary.Vertex}
    (p : (glueGraph piece outside).Walk (.inl A) (.inl B))
    (nodup : p.support.Nodup)
    {contextInner : outside.Internal}
    (contextMem : (Sum.inr (Sum.inr contextInner) : GluedVertex piece outside)
      ∈ p.support) :
    ∃ left right : boundary.Vertex, left ≠ right ∧
      ∃ corridor : (glueGraph piece outside).Walk (.inl left) (.inl right),
        corridor.edges ⊆ p.edges ∧
        ∀ x ∈ corridor.support,
          x = (Sum.inl left : GluedVertex piece outside) ∨
          x = (Sum.inl right : GluedVertex piece outside) ∨
          ∃ inner : outside.Internal, x = .inr (.inr inner) := by
  classical
  obtain ⟨leftL, lead1, lead1Edges, lead1Support, lead1Char⟩ :=
    exists_context_lead_to_label
      (p.takeUntil (.inr (.inr contextInner)) contextMem).reverse
      ⟨contextInner, rfl⟩ ⟨A, rfl⟩
  obtain ⟨rightL, lead2, lead2Edges, lead2Support, lead2Char⟩ :=
    exists_context_lead_to_label
      (p.dropUntil (.inr (.inr contextInner)) contextMem)
      ⟨contextInner, rfl⟩ ⟨B, rfl⟩
  have leftMem1 : (Sum.inl leftL : GluedVertex piece outside) ∈
      (p.takeUntil (.inr (.inr contextInner)) contextMem).support := by
    have := lead1Support lead1.end_mem_support
    rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this
  have rightMem2 : (Sum.inl rightL : GluedVertex piece outside) ∈
      (p.dropUntil (.inr (.inr contextInner)) contextMem).support :=
    lead2Support lead2.end_mem_support
  have supportEq : p.support =
      (p.takeUntil (.inr (.inr contextInner)) contextMem).support ++
        (p.dropUntil (.inr (.inr contextInner)) contextMem).support.tail := by
    conv_lhs => rw [← SimpleGraph.Walk.take_spec p contextMem]
    exact SimpleGraph.Walk.support_append _ _
  have distinct : leftL ≠ rightL := by
    intro same
    have nodup' := nodup
    rw [supportEq] at nodup'
    have rightTail : (Sum.inl rightL : GluedVertex piece outside) ∈
        (p.dropUntil (.inr (.inr contextInner)) contextMem).support.tail := by
      rcases (SimpleGraph.Walk.mem_support_iff _).mp rightMem2 with
        headEq | tailMem
      · exact absurd headEq (by simp)
      · exact tailMem
    exact ((List.nodup_append.mp nodup').2.2 _ (same ▸ leftMem1) _
      rightTail) rfl
  refine ⟨leftL, rightL, distinct, lead1.reverse.append lead2, ?_, ?_⟩
  · intro e emem
    rw [SimpleGraph.Walk.edges_append] at emem
    rcases List.mem_append.mp emem with mem1 | mem2
    · have inLead : e ∈ lead1.edges := by
        rwa [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at mem1
      have inTake := lead1Edges inLead
      rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at inTake
      exact SimpleGraph.Walk.edges_takeUntil_subset_edges p contextMem inTake
    · exact SimpleGraph.Walk.edges_dropUntil_subset_edges p contextMem
        (lead2Edges mem2)
  · intro x xmem
    rw [SimpleGraph.Walk.support_append] at xmem
    rcases List.mem_append.mp xmem with mem1 | mem2
    · have inLead : x ∈ lead1.support := by
        rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at mem1
      rcases lead1Char x inLead with lab | ctx
      · exact Or.inl lab
      · exact Or.inr (Or.inr ctx)
    · rcases lead2Char x (List.mem_of_mem_tail mem2) with lab | ctx
      · exact Or.inr (Or.inl lab)
      · exact Or.inr (Or.inr ctx)

/-- **The outside corridor at a context-internal visit of a glued cycle**
(`lem:typeA-pressure-records-canonical`, the actual-record corridor): a glued
cycle visiting a context-internal vertex and two distinct boundary labels
carries a corridor between two distinct labels, along cycle edges, with every
other vertex context-internal. -/
theorem exists_corridor_of_cycle_contextInternal
    {base : GluedVertex piece outside}
    {c : (glueGraph piece outside).Walk base base} (cycle : c.IsCycle)
    {contextInner : outside.Internal}
    (contextMem : (Sum.inr (Sum.inr contextInner) : GluedVertex piece outside)
      ∈ c.support)
    {la lb : boundary.Vertex} (labelsDistinct : la ≠ lb)
    (laMem : (Sum.inl la : GluedVertex piece outside) ∈ c.support)
    (lbMem : (Sum.inl lb : GluedVertex piece outside) ∈ c.support) :
    ∃ left right : boundary.Vertex, left ≠ right ∧
      ∃ corridor : (glueGraph piece outside).Walk (.inl left) (.inl right),
        corridor.edges ⊆ c.edges ∧
        ∀ x ∈ corridor.support,
          x = (Sum.inl left : GluedVertex piece outside) ∨
          x = (Sum.inl right : GluedVertex piece outside) ∨
          ∃ inner : outside.Internal, x = .inr (.inr inner) := by
  classical
  set rotated := c.rotate (Sum.inl la) laMem with rotatedDef
  have rotatedCycle : rotated.IsCycle := cycle.rotate laMem
  have lbMemRot : (Sum.inl lb : GluedVertex piece outside) ∈
      rotated.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c _ laMem).mpr lbMem
  have contextMemRot : (Sum.inr (Sum.inr contextInner) :
      GluedVertex piece outside) ∈ rotated.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c _ laMem).mpr contextMem
  set w1 := rotated.takeUntil _ lbMemRot with w1Def
  set w2 := rotated.dropUntil _ lbMemRot with w2Def
  have supportSplit : rotated.support = w1.support ++ w2.support.tail := by
    conv_lhs => rw [← SimpleGraph.Walk.take_spec rotated lbMemRot]
    exact SimpleGraph.Walk.support_append w1 w2
  have tailSplit : rotated.support.tail =
      w1.support.tail ++ w2.support.tail := by
    rw [supportSplit, SimpleGraph.Walk.support_eq_cons w1]
    rfl
  have tailNodup := rotatedCycle.support_nodup
  rw [tailSplit] at tailNodup
  have edgesBack : ∀ {e : Sym2 (GluedVertex piece outside)},
      e ∈ rotated.edges → e ∈ c.edges := by
    intro e emem
    exact ((SimpleGraph.Walk.rotate_edges c _ laMem).mem_iff).mp emem
  rcases List.mem_append.mp (supportSplit ▸ contextMemRot) with v1 | v2
  · -- the context-internal visit lies in the first half `la → lb`
    have w1Nodup : w1.support.Nodup := by
      rw [SimpleGraph.Walk.support_eq_cons w1]
      refine List.nodup_cons.mpr ⟨?_, (List.nodup_append.mp tailNodup).1⟩
      intro laTail1
      have laTail2 : (Sum.inl la : GluedVertex piece outside) ∈
          w2.support.tail := by
        rcases (SimpleGraph.Walk.mem_support_iff w2).mp
            w2.end_mem_support with headEq | tailMem
        · exact absurd (Sum.inl.inj headEq) labelsDistinct
        · exact tailMem
      exact ((List.nodup_append.mp tailNodup).2.2 _ laTail1 _ laTail2) rfl
    obtain ⟨left, right, distinct, corridor, corridorEdges, corridorChar⟩ :=
      exists_corridor_of_path_labels w1 w1Nodup v1
    refine ⟨left, right, distinct, corridor, ?_, corridorChar⟩
    intro e emem
    exact edgesBack
      (SimpleGraph.Walk.edges_takeUntil_subset_edges rotated lbMemRot
        (corridorEdges emem))
  · -- the context-internal visit lies in the second half `lb → la`
    have v2' : (Sum.inr (Sum.inr contextInner) :
        GluedVertex piece outside) ∈ w2.support :=
      List.mem_of_mem_tail v2
    have w2Nodup : w2.support.Nodup := by
      rw [SimpleGraph.Walk.support_eq_cons w2]
      refine List.nodup_cons.mpr ⟨?_, (List.nodup_append.mp tailNodup).2.1⟩
      intro lbTail2
      have lbTail1 : (Sum.inl lb : GluedVertex piece outside) ∈
          w1.support.tail := by
        rcases (SimpleGraph.Walk.mem_support_iff w1).mp
            w1.end_mem_support with headEq | tailMem
        · exact absurd (Sum.inl.inj headEq).symm labelsDistinct
        · exact tailMem
      exact ((List.nodup_append.mp tailNodup).2.2 _ lbTail1 _ lbTail2) rfl
    obtain ⟨left, right, distinct, corridor, corridorEdges, corridorChar⟩ :=
      exists_corridor_of_path_labels w2 w2Nodup v2'
    refine ⟨left, right, distinct, corridor, ?_, corridorChar⟩
    intro e emem
    exact edgesBack
      (SimpleGraph.Walk.edges_dropUntil_subset_edges rotated lbMemRot
        (corridorEdges emem))

end Corridor

section PieceRestriction

variable (smaller : SimpleGraph (boundary.Vertex ⊕ piece.Internal))
variable (decide : DecidableRel smaller.Adj)

/-- **Walk transfer into a label-edge-preserving restriction**: a glued walk
whose support avoids the piece's internal vertices uses only context-owned
edges and piece edges between two boundary labels, so it lives in the gluing
of any restriction that keeps every label-incident edge. -/
theorem exists_walk_restriction_of_avoids_piece_internal
    (keepsLabelEdges : ∀ (label : boundary.Vertex)
      (other : boundary.Vertex ⊕ piece.Internal),
      piece.graph.Adj (.inl label) other → smaller.Adj (.inl label) other) :
    ∀ {start finish : GluedVertex piece outside}
      (walk : (glueGraph piece outside).Walk start finish),
      (∀ inner : piece.Internal,
        (Sum.inr (Sum.inl inner) : GluedVertex piece outside) ∉ walk.support) →
      ∃ walk' : (glueGraph
          { piece with graph := smaller, decideAdj := decide }
          outside).Walk start finish,
        walk'.support = walk.support ∧ walk'.edges = walk.edges := by
  intro start finish walk
  induction walk with
  | nil =>
      intro _avoids
      exact ⟨.nil, rfl, rfl⟩
  | @cons u b v adjacent rest ih =>
      intro avoids
      have avoidsRest : ∀ inner : piece.Internal,
          (Sum.inr (Sum.inl inner) : GluedVertex piece outside) ∉
            rest.support := by
        intro inner member
        refine avoids inner ?_
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ member
      obtain ⟨rest', restSupport, restEdges⟩ := ih avoidsRest
      have adjacent' : (glueGraph
          { piece with graph := smaller, decideAdj := decide }
          outside).Adj u b := by
        rcases (glueGraph_adj_iff piece outside _ _).mp adjacent with
          pieceOwn | contextOwn
        · obtain ⟨pieceLeft, pieceRight, adj, leftEq, rightEq⟩ := pieceOwn
          rcases pieceLeft with leftLabel | leftInner
          · rcases pieceRight with rightLabel | rightInner
            · exact (glueGraph_adj_iff _ outside _ _).mpr
                (Or.inl ⟨.inl leftLabel, .inl rightLabel,
                  keepsLabelEdges leftLabel _ adj, leftEq, rightEq⟩)
            · exfalso
              refine avoids rightInner ?_
              have bEq : b = .inr (.inl rightInner) := by
                simp [pieceEmbedding] at rightEq
                exact rightEq.symm
              rw [SimpleGraph.Walk.support_cons]
              exact List.mem_cons_of_mem _ (bEq ▸ rest.start_mem_support)
          · exfalso
            refine avoids leftInner ?_
            have uEq : u = .inr (.inl leftInner) := by
              simp [pieceEmbedding] at leftEq
              exact leftEq.symm
            rw [SimpleGraph.Walk.support_cons]
            exact uEq ▸ List.mem_cons_self
        · obtain ⟨contextLeft, contextRight, adj, leftEq, rightEq⟩ := contextOwn
          exact (glueGraph_adj_iff _ outside _ _).mpr
            (Or.inr ⟨contextLeft, contextRight, adj, leftEq, rightEq⟩)
      refine ⟨.cons adjacent' rest', ?_, ?_⟩
      · rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
          restSupport]
      · rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons,
          restEdges]

/-- **Cycle-certificate transfer into a label-edge-preserving restriction**:
an accepted glued cycle avoiding the piece's internal vertices is an accepted
cycle of the restricted gluing. -/
theorem hasCycleWithLength_restriction_of_avoids_piece_internal
    (keepsLabelEdges : ∀ (label : boundary.Vertex)
      (other : boundary.Vertex ⊕ piece.Internal),
      piece.graph.Adj (.inl label) other → smaller.Adj (.inl label) other)
    {LengthOK : Nat → Prop}
    {base : GluedVertex piece outside}
    {c : (glueGraph piece outside).Walk base base} (cycle : c.IsCycle)
    (lengthOk : LengthOK c.length)
    (avoids : ∀ inner : piece.Internal,
      (Sum.inr (Sum.inl inner) : GluedVertex piece outside) ∉ c.support) :
    HasCycleWithLength LengthOK
      (glue { piece with graph := smaller, decideAdj := decide } outside) := by
  classical
  obtain ⟨c', supportEq, edgesEq⟩ :=
    exists_walk_restriction_of_avoids_piece_internal
      (piece := piece) (outside := outside) smaller decide keepsLabelEdges c
      avoids
  have lengthEq : c'.length = c.length := by
    have := congrArg List.length edgesEq
    rwa [SimpleGraph.Walk.length_edges, SimpleGraph.Walk.length_edges] at this
  have isCycle' : c'.IsCycle := by
    refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
    · rw [edgesEq]
      exact cycle.edges_nodup
    · intro isNil
      have zeroLength : c'.length = 0 := by rw [isNil]; rfl
      have := cycle.three_le_length
      omega
    · rw [supportEq]
      exact cycle.support_nodup
  refine ⟨⟨show (glue { piece with graph := smaller, decideAdj := decide }
      outside).Vertex from base, c', isCycle', ?_⟩⟩
  have accepted := lengthOk
  rw [← lengthEq] at accepted
  exact accepted

end PieceRestriction

end Hypostructure.Graph.GluedCycleSides
