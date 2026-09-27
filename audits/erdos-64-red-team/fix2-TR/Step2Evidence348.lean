/-
fix2-TR step 2: the user-approved construction attempt for [348] (tex 15362).
Scratch evidence, not part of the build.  Compile from `hypostructure/` with
`lake env lean <this file>`.

`CompressibleSupport Baseline Target G S` (InterfaceReplacement.lean:415) is
  ∃ (connected : ConnectedOn G S) (proper : ∃ v, v ∉ S),
    let atom := properAtom G S connected proper
    ∃ replacement : BoundaryPiece atom.decomposition.interface,
      replacement.boundaryDegreeProfile = atom.decomposition.piece.boundaryDegreeProfile ∧
      Baseline (glue replacement atom.decomposition.outside) ∧          -- min degree ≥ 3
      (glue replacement atom.decomposition.outside).LexicographicallySmaller G ∧
      ∀ outside, Target (glue replacement outside) ↔ Target (glue atom.decomposition.piece outside)

Construction at an entry ξ = (X, w, u, B_u) of G's unified set with (b):
S := B_u; replacement := the interior fold `identifyInternal keep remove` of
B_u's piece (the smaller representative; it realizes the quotient when no
retained declared support contains keep or remove).  `fold_clauses` checks
the clauses: connected, proper, profile, baseline, smaller all hold (given a
fold pair with no common neighbour); the response clause FAILS
(`response_clause_fails_at_G_context`, `fold_not_fullTarget_complete`).
-/
import Hypostructure.Graph.Contracts.RouteEight.EntryCensus

open Hypostructure Hypostructure.Graph

universe u

namespace F2TRStep2

/-- (E2) At G's own outside context of any connected proper basin `B_u`, EVERY
smaller baseline representative `R` fails the response-preserving clause of
`CompressibleSupport` (full target `HasCycleWithLength`): minimality gives
`R ⊕ Y_G` an accepted cycle, while `B_u ⊕ Y_G ≅ G` has none. -/
theorem response_clause_fails_at_G_context
    {object : FiniteObject.{u}} {threshold : Nat} {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold representative →
      HasCycleWithLength LengthOK representative)
    {basin : Finset object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (R : BoundaryPiece (Strategy.InterfaceReplacement.SupportAtom.properAtom
      object basin connected proper).decomposition.interface)
    (baseline : MinimumDegreeAtLeast threshold (glue R
      (Strategy.InterfaceReplacement.SupportAtom.properAtom object basin
        connected proper).decomposition.outside))
    (smaller : (glue R (Strategy.InterfaceReplacement.SupportAtom.properAtom
      object basin connected proper).decomposition.outside).LexicographicallySmaller
        object) :
    let atom := Strategy.InterfaceReplacement.SupportAtom.properAtom object basin
      connected proper
    ¬ (HasCycleWithLength LengthOK (glue R atom.decomposition.outside) ↔
        HasCycleWithLength LengthOK
          (glue atom.decomposition.piece atom.decomposition.outside)) := by
  intro atom same
  have rCycle := minimality _ smaller baseline
  have pieceCycle := same.mp rCycle
  exact avoids (((cycleTargetInterface LengthOK).isomorphismInvariant.iff_of_iso
    ⟨atom.decomposition.reconstructionIso⟩).mp pieceCycle)

/-- (E1) For the explicit smaller representative (interior fold of `B_u`), G's
`K .uncompressible` refutes full-target completeness outright. -/
theorem fold_not_fullTarget_complete
    {object : FiniteObject.{u}} {threshold : Nat} (two : 2 ≤ threshold)
    {LengthOK : Nat → Prop} {basin : Finset object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (keep remove :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (baseline : MinimumDegreeAtLeast threshold object)
    (noCommon : ∀ x,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
            (.inr keep) x ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
          (.inr remove) x))
    (uncompressible : ∀ candidate : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.CompressibleSupport
          (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
          candidate) :
    ¬ Response.TargetComplete BoundaryPiece.boundaryDegreeProfile
      (HasCycleWithLength LengthOK)
      ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).identifyInternal
        keep remove different)
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin) :=
  Route8.PresentedEntry.not_targetComplete_foldRealization object basin threshold
    two LengthOK connected proper keep remove different baseline noCommon
    uncompressible

/-- (E3) What alternative (b) gives at that same context: only the declared
`u`-supported algebra, which is FALSE at `B_u ⊕ Y_G` (a visible declared event
needs an accepted cycle of `B_u ⊕ Y_G ≅ G`).  So (b)'s clause at `Y_G` only
asks `¬ declaredAlgebra R Y_G`, consistent with E2's accepted cycle of
`R ⊕ Y_G`: the cycle minimality supplies need not pass through a boundary
label on a retained core crossing event. -/
theorem declaredAlgebra_false_at_G_context
    {object : FiniteObject.{u}} {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    {support basin : Finset object.Vertex} {threshold : Nat}
    {receiver load : object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin) :
    let atom := Strategy.InterfaceReplacement.SupportAtom.properAtom object basin
      connected proper
    ¬ Route8.TraceBasin.declaredAlgebra object support basin threshold LengthOK
        receiver load atom.decomposition.piece atom.decomposition.outside := by
  intro atom holds
  obtain ⟨_, _, _, _, _, _, certificate, _⟩ := holds
  exact avoids (((cycleTargetInterface LengthOK).isomorphismInvariant.iff_of_iso
    ⟨atom.decomposition.reconstructionIso⟩).mp ⟨certificate⟩)

end F2TRStep2

#print axioms F2TRStep2.response_clause_fails_at_G_context
#print axioms F2TRStep2.fold_not_fullTarget_complete
#print axioms F2TRStep2.declaredAlgebra_false_at_G_context

namespace F2TRStep2

/-- Clause check for the explicit fold representative at `B_u`: every clause
of `CompressibleSupport` except the response clause holds, the fold is a
realization of the quotient, and alternative (b) gives only declared-algebra
equivalence for it. -/
theorem fold_clauses
    {object : FiniteObject.{u}} {support basin : Finset object.Vertex}
    {threshold : Nat} (two : 2 ≤ threshold) {LengthOK : Nat → Prop}
    {receiver load : object.Vertex}
    {retained : Finset (Route8.PresentedEntry.TraceCoordinate object support)}
    (quotient : Route8.TraceBasin.TraceResponseQuotient object support threshold
      LengthOK receiver load basin
      (Route8.TraceBasin.ResponseQuotient.forgetting retained))
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (baseline : MinimumDegreeAtLeast threshold object)
    (keep remove :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (noCommon : ∀ x,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
            (.inr keep) x ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
          (.inr remove) x))
    (undeclared : ∀ coordinate ∈ retained,
      keep.1 ∉ Route8.PresentedEntry.traceDeclaredSupport object support threshold
          receiver load coordinate ∧
        remove.1 ∉ Route8.PresentedEntry.traceDeclaredSupport object support
          threshold receiver load coordinate) :
    let fold := (Strategy.InterfaceReplacement.SupportAtom.piece object
      basin).identifyInternal keep remove different
    let atom := Strategy.InterfaceReplacement.SupportAtom.properAtom object basin
      connected proper
    -- profile clause
    fold.boundaryDegreeProfile =
        (Strategy.InterfaceReplacement.SupportAtom.piece object
          basin).boundaryDegreeProfile ∧
      -- baseline clause (min degree ≥ threshold)
      MinimumDegreeAtLeast threshold (glue fold atom.decomposition.outside) ∧
      -- strictly smaller clause
      (glue fold atom.decomposition.outside).LexicographicallySmaller object ∧
      -- the fold realizes the quotient
      Route8.TraceBasin.QuotientRealization object support basin threshold
        receiver load (Route8.TraceBasin.ResponseQuotient.forgetting retained)
        fold ∧
      -- what (b) gives: declared-algebra equivalence only, at
      -- profile-compatible contexts
      ∀ outside, Route8.TraceBasin.ProfileCompatible object basin threshold
          outside →
        (Route8.TraceBasin.declaredAlgebra object support basin threshold
            LengthOK receiver load fold outside ↔
          Route8.TraceBasin.declaredAlgebra object support basin threshold
            LengthOK receiver load
            (Strategy.InterfaceReplacement.SupportAtom.piece object basin)
            outside) := by
  intro fold atom
  have realizes := Route8.TraceBasin.quotientRealization_identifyInternal object
    support basin threshold receiver load retained keep remove different
    (fun label common => noCommon (.inl label) common) undeclared
  obtain ⟨dBaseline, dSmaller⟩ :=
    Route8.PresentedEntry.foldRealization_baseline_and_smaller object basin
      threshold two connected proper keep remove different baseline noCommon
  exact ⟨realizes.1, dBaseline, dSmaller, realizes, quotient.2.2 fold realizes⟩

end F2TRStep2

#print axioms F2TRStep2.fold_clauses

/-!
## Step 2b: what closes (b) at G, and the one missing implication

At G's own outside context `Y_G` of the basin:
* `Y_G` is profile-compatible (`profileCompatible_G_context`), so (b)
  applies there;
* (b) forces `¬ declaredAlgebra R Y_G` for every realization `R`
  (`b_at_G_context`, from `declaredAlgebra_false_at_G_context`);
* for the fold `R`, minimality forces an accepted cycle in `R ⊕ Y_G`.
So (b) at a fold-realizable entry closes EXACTLY when the accepted cycle of
`R ⊕ Y_G` is visible to the declared algebra (`Visibility` below):
`closes_of_visibility`.  No inventoried fact of G gives `Visibility`:
[12] (`TargetCompleteContextUniversalityStatement`, Statements/Spine.lean:2635)
needs a full-target (`HasCycleWithLength`, all contexts) identification of an
admissible rank quotient as hypothesis, which (b) does not supply; its
"consequently" clause concludes target-DEFECT from a separating context, it
never concludes response equality at `Y_G`; [11] only separates boundary-degree
fibres (the fold with no common label stays in the fibre, so it gives nothing);
the declared-family completeness sentence (tex 10738-10741) speaks only of
declared events.
-/

namespace F2TRStep2

/-- `Y_G` (the outside of the basin in G) is compatible with the profile. -/
theorem profileCompatible_G_context
    {object : FiniteObject.{u}} {threshold : Nat}
    (baseline : MinimumDegreeAtLeast threshold object)
    {basin : Finset object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin) :
    let atom := Strategy.InterfaceReplacement.SupportAtom.properAtom object basin
      connected proper
    Route8.TraceBasin.ProfileCompatible object basin threshold
      atom.decomposition.outside := by
  intro atom label
  have glued : MinimumDegreeAtLeast threshold
      (glue atom.decomposition.piece atom.decomposition.outside) :=
    ((minimumDegreeAtLeast_isomorphismInvariant threshold).iff_of_iso
      ⟨atom.decomposition.reconstructionIso⟩).mpr baseline
  exact le_trans glued (FiniteObject.minDegree_le_degree _ _)

/-- (b) at `Y_G`: no realization of the quotient carries a visible declared
event against G's own outside context. -/
theorem b_at_G_context
    {object : FiniteObject.{u}} {support basin : Finset object.Vertex}
    {threshold : Nat} {LengthOK : Nat → Prop} {receiver load : object.Vertex}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (baseline : MinimumDegreeAtLeast threshold object)
    {quotient : Route8.TraceBasin.ResponseQuotient object support basin}
    (b : Route8.TraceBasin.TraceResponseQuotient object support threshold
      LengthOK receiver load basin quotient)
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (R : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin))
    (realizes : Route8.TraceBasin.QuotientRealization object support basin
      threshold receiver load quotient R) :
    let atom := Strategy.InterfaceReplacement.SupportAtom.properAtom object basin
      connected proper
    ¬ Route8.TraceBasin.declaredAlgebra object support basin threshold LengthOK
        receiver load R atom.decomposition.outside := by
  intro atom visible
  exact declaredAlgebra_false_at_G_context (support := support)
    (threshold := threshold) (receiver := receiver) (load := load) avoids
    connected proper
    ((b.2.2 R realizes atom.decomposition.outside
      (profileCompatible_G_context baseline connected proper)).mp visible)

/-- **The missing implication, as a formula about G** at the entry's basin
and the fold `R`: every accepted cycle of `R ⊕ Y_G` is a visible declared
`u`-supported event. -/
def Visibility {object : FiniteObject.{u}} (support basin : Finset object.Vertex)
    (threshold : Nat) (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (R : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin)) : Prop :=
  let atom := Strategy.InterfaceReplacement.SupportAtom.properAtom object basin
    connected proper
  HasCycleWithLength LengthOK (glue R atom.decomposition.outside) →
    Route8.TraceBasin.declaredAlgebra object support basin threshold LengthOK
      receiver load R atom.decomposition.outside

/-- **Conditional closure of (b) at G**: with a fold pair off the retained
declared supports and `Visibility` for the fold, (b) contradicts G's
minimality.  This is the whole content the paper's step at tex 15362 needs. -/
theorem closes_of_visibility
    {object : FiniteObject.{u}} {support basin : Finset object.Vertex}
    {threshold : Nat} (two : 2 ≤ threshold) {LengthOK : Nat → Prop}
    {receiver load : object.Vertex}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (baseline : MinimumDegreeAtLeast threshold object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold representative →
      HasCycleWithLength LengthOK representative)
    {retained : Finset (Route8.PresentedEntry.TraceCoordinate object support)}
    (b : Route8.TraceBasin.TraceResponseQuotient object support threshold
      LengthOK receiver load basin
      (Route8.TraceBasin.ResponseQuotient.forgetting retained))
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (keep remove :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (noCommon : ∀ x,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
            (.inr keep) x ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
          (.inr remove) x))
    (undeclared : ∀ coordinate ∈ retained,
      keep.1 ∉ Route8.PresentedEntry.traceDeclaredSupport object support threshold
          receiver load coordinate ∧
        remove.1 ∉ Route8.PresentedEntry.traceDeclaredSupport object support
          threshold receiver load coordinate)
    (visibility : Visibility support basin threshold LengthOK receiver load
      connected proper
      ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).identifyInternal
        keep remove different)) :
    False := by
  have realizes := Route8.TraceBasin.quotientRealization_identifyInternal object
    support basin threshold receiver load retained keep remove different
    (fun label common => noCommon (.inl label) common) undeclared
  obtain ⟨dBaseline, dSmaller⟩ :=
    Route8.PresentedEntry.foldRealization_baseline_and_smaller object basin
      threshold two connected proper keep remove different baseline noCommon
  exact b_at_G_context avoids baseline b connected proper _ realizes
    (visibility (minimality _ dSmaller dBaseline))

end F2TRStep2

#print axioms F2TRStep2.profileCompatible_G_context
#print axioms F2TRStep2.b_at_G_context
#print axioms F2TRStep2.closes_of_visibility

/-!
## Step 2b (continued): why [11]/[12] cannot supply the response equality

`TargetCompleteContextUniversalityStatement` part 1 (key 2301) is stated for
`CurvatureQuotient = DeclaredQuotient` (`DeclaredRankQuotient.lean`), and a
`DeclaredQuotient` carries `contextUniversal` -- full `HasCycleWithLength`
equivalence of identified realizations in every context -- as a FIELD.  To
bring the (b)-quotient under [12] one must build that field for the fold
`R` and `B_u`, which is the missing equality itself.  [11] only asks the
boundary-degree fibre, which the fold (no common label) already satisfies.

The explicit configuration at G: at an entry with (b) and a fold pair, the fold
`R` glued to G's own context carries an accepted cycle (minimality) that is
NOT a visible declared event (`invisibleCycle_of_b`).  That accepted cycle is
exactly what the standard argument would need to be declared-visible.
-/

namespace F2TRStep2

theorem invisibleCycle_of_b
    {object : FiniteObject.{u}} {support basin : Finset object.Vertex}
    {threshold : Nat} (two : 2 ≤ threshold) {LengthOK : Nat → Prop}
    {receiver load : object.Vertex}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (baseline : MinimumDegreeAtLeast threshold object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold representative →
      HasCycleWithLength LengthOK representative)
    {retained : Finset (Route8.PresentedEntry.TraceCoordinate object support)}
    (b : Route8.TraceBasin.TraceResponseQuotient object support threshold
      LengthOK receiver load basin
      (Route8.TraceBasin.ResponseQuotient.forgetting retained))
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (keep remove :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (noCommon : ∀ x,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
            (.inr keep) x ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
          (.inr remove) x))
    (undeclared : ∀ coordinate ∈ retained,
      keep.1 ∉ Route8.PresentedEntry.traceDeclaredSupport object support threshold
          receiver load coordinate ∧
        remove.1 ∉ Route8.PresentedEntry.traceDeclaredSupport object support
          threshold receiver load coordinate) :
    let fold := (Strategy.InterfaceReplacement.SupportAtom.piece object
      basin).identifyInternal keep remove different
    let atom := Strategy.InterfaceReplacement.SupportAtom.properAtom object basin
      connected proper
    HasCycleWithLength LengthOK (glue fold atom.decomposition.outside) ∧
      ¬ Route8.TraceBasin.declaredAlgebra object support basin threshold LengthOK
          receiver load fold atom.decomposition.outside := by
  intro fold atom
  have realizes := Route8.TraceBasin.quotientRealization_identifyInternal object
    support basin threshold receiver load retained keep remove different
    (fun label common => noCommon (.inl label) common) undeclared
  obtain ⟨dBaseline, dSmaller⟩ :=
    Route8.PresentedEntry.foldRealization_baseline_and_smaller object basin
      threshold two connected proper keep remove different baseline noCommon
  exact ⟨minimality _ dSmaller dBaseline,
    b_at_G_context avoids baseline b connected proper _ realizes⟩

end F2TRStep2

#print axioms F2TRStep2.invisibleCycle_of_b
