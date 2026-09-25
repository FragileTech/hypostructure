# Exact retained context declarations for Node 20 Stage 3

Verbatim, line-numbered source excerpts. These state the retained implication and its hypotheses; they do not assert its applicability to the bound defective pair.

## `hypostructure/Hypostructure/Graph/Response.lean:49-105`

```lean
49: def ContextEquivalentOn {boundary : Boundary.{u}}
50:     (Target : InterfaceTarget boundary)
51:     (left right : BoundaryPiece boundary) : Prop :=
52:   forall outside : OutsideContext boundary,
53:     Target left outside <-> Target right outside
54: 
55: /-- Two pieces with the same labelled boundary have identical target response
56: against every literal outside context.  This is symbolic universal coverage;
57: no context family is enumerated.
58: 
59: This is the specialization of `ContextEquivalentOn` at
60: `InterfaceTarget.ofObject`; it is definitionally the old statement, so every
61: existing caller is unaffected. -/
62: def ContextEquivalent {boundary : Boundary.{u}}
63:     (Target : FiniteObject.{u} -> Prop)
64:     (left right : BoundaryPiece boundary) : Prop :=
65:   ContextEquivalentOn (InterfaceTarget.ofObject Target) left right
66: 
67: theorem contextEquivalent_iff {boundary : Boundary.{u}}
68:     {Target : FiniteObject.{u} -> Prop} {left right : BoundaryPiece boundary} :
69:     ContextEquivalent Target left right ↔
70:       forall outside : OutsideContext boundary,
71:         Target (glue left outside) <-> Target (glue right outside) :=
72:   Iff.rfl
73: 
74: /-- Exact graph target-completeness combines equality in a caller-selected
75: immutable profile fibre with universal target response.  Context equivalence
76: alone is not a target-complete identification. -/
77: structure TargetComplete {boundary : Boundary.{u}}
78:     {Profile : Type uProfile} (profile : BoundaryPiece boundary -> Profile)
79:     (Target : FiniteObject.{u} -> Prop)
80:     (left right : BoundaryPiece boundary) : Prop where
81:   profile_eq : profile left = profile right
82:   contextEquivalent : ContextEquivalent Target left right
83: 
84: /-- Target completeness against an interface-aware target.  `TargetComplete` is
85: its specialization at `InterfaceTarget.ofObject`. -/
86: structure TargetCompleteOn {boundary : Boundary.{u}}
87:     {Profile : Type uProfile} (profile : BoundaryPiece boundary -> Profile)
88:     (Target : InterfaceTarget boundary)
89:     (left right : BoundaryPiece boundary) : Prop where
90:   profile_eq : profile left = profile right
91:   contextEquivalent : ContextEquivalentOn Target left right
92: 
93: /-- One literal outside context witnessing failure of interface-aware target
94: equivalence. -/
95: def TargetDefectOn {boundary : Boundary.{u}}
96:     (Target : InterfaceTarget boundary)
97:     (left right : BoundaryPiece boundary) : Prop :=
98:   exists outside : OutsideContext boundary,
99:     Not (Target left outside <-> Target right outside)
100: 
101: /-- One literal outside context witnessing failure of target equivalence. -/
102: def TargetDefect {boundary : Boundary.{u}}
103:     (Target : FiniteObject.{u} -> Prop)
104:     (left right : BoundaryPiece boundary) : Prop :=
105:   exists outside : OutsideContext boundary,
```

## `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean:8340-8363`

```lean
8340:   | .degreeProfileFibres, object =>
8341:       ∀ (support : Finset object.Vertex)
8342:         (left right : Graph.BoundaryPiece
8343:           (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object
8344:             support)),
8345:         Graph.Response.TargetComplete
8346:             Graph.BoundaryPiece.boundaryDegreeProfile
8347:             (Graph.HasCycleWithLength data.LengthOK) left right →
8348:           left.boundaryDegreeProfile = right.boundaryDegreeProfile
8349:   | .targetCompleteContextUniversality, object =>
8350:       ∀ (support : Finset object.Vertex)
8351:         (left right : Graph.BoundaryPiece
8352:           (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object
8353:             support)),
8354:         Graph.Response.TargetComplete
8355:             Graph.BoundaryPiece.boundaryDegreeProfile
8356:             (Graph.HasCycleWithLength data.LengthOK) left right →
8357:           Graph.Response.ContextEquivalent
8358:             (Graph.HasCycleWithLength data.LengthOK) left right
8359:   | .replacementExclusion, object =>
8360:       (∀ support : Finset object.Vertex,
8361:         ¬ Graph.Strategy.InterfaceReplacement.ReplacementSupport
8362:             (Graph.MinimumDegreeAtLeast data.threshold)
8363:             (Graph.HasCycleWithLength data.LengthOK) object support)
```

## `hypostructure/Hypostructure/Graph/Strategy/SpineRows/TargetCompleteContextUniversality.lean:18-49`

```lean
18: 
19: /-! ## Node `[12]`: context-universality
20: 
21: `lem:context-universality`.  Condition (b) of
22: `def:target-complete-quotient` says that every target-complete identification
23: has the same target response in every outside context.  Like node `[11]`, this
24: is a field projection from the paper's target-completeness hypothesis.  The
25: row is source-free, publishes exactly that semantic fact, and appends it to the
26: literal ledger. -/
27: omit [FactSystem (Input BranchState Presentation presentation data)] in
28: @[reducible] noncomputable def targetCompleteContextUniversalityRow :
29:     @AtomicStrategy (Input BranchState Presentation presentation data) _
30:       (instFactSystem (BranchState := BranchState)
31:         (Presentation := Presentation) (presentation := presentation)
32:         (data := data)) :=
33:   letI : FactSystem (Input BranchState Presentation presentation data) :=
34:     instFactSystem (BranchState := BranchState) (Presentation := Presentation)
35:       (presentation := presentation) (data := data)
36:   @factOnly (Input BranchState Presentation presentation data) _
37:     (instFactSystem (BranchState := BranchState)
38:       (Presentation := Presentation) (presentation := presentation)
39:       (data := data))
40:     `Hypostructure.Graph.Strategy.Spine.targetCompleteContextUniversality
41:     (sourceFreeManifest (K .targetCompleteContextUniversality))
42:     (fun inputs =>
43:       .cons (key := K .targetCompleteContextUniversality)
44:         (show Value BranchState Presentation presentation data
45:             .targetCompleteContextUniversality inputs.current from
46:           ⟨fun _support _left _right complete => complete.contextEquivalent⟩)
47:         .nil)
48:     0 0
49: 
```
