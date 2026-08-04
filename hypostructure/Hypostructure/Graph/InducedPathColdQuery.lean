import Hypostructure.Graph.InducedPathCold
import Hypostructure.Core.Residual.Query

/-!
# Residual-query ergonomics for cold induced-path data

These constructors are the public node-facing surface.  They derive every
window, incidence, and branch-excess schedule from typed predecessor queries;
the node never accepts a graph copy, a manually selected window, or a detached
ledger payload.
-/

namespace Hypostructure.Graph.InducedPathCold.QuerySurface

open Hypostructure.Core
open Hypostructure.Core.Residual
open Hypostructure.Core.Finite
open Hypostructure.Graph.InducedPathMaximalPacking

universe uPrevious u

variable {Previous : Sort uPrevious}

abbrev ObjectQuery :=
  Query Previous (fun _previous => FiniteObject.{u})

noncomputable def selectedWindowsQuery {order : Nat}
    (object : ObjectQuery)
    (packing : Query Previous
      (fun previous => Profile (object.read previous) order)) :
    Query Previous (fun previous =>
      Enumeration (Window (object.read previous) order)) :=
  packing.map fun previous profile => by
    letI : DecidableEq (Window (object.read previous) order) :=
      Classical.decEq _
    exact Enumeration.ofNodupList profile.selected profile.selected_nodup

noncomputable def tokenScheduleQuery {order : Nat}
    (object : ObjectQuery)
    (window : Query Previous (fun previous =>
      Window (object.read previous) order)) :
    Query Previous (fun previous =>
      Enumeration (Token (object.read previous) order (window.read previous))) :=
  window.dependentMap fun _previous activeWindow => tokenSchedule activeWindow

noncomputable def branchExcessQuery {order : Nat}
    (object : ObjectQuery)
    (window : Query Previous (fun previous =>
      Window (object.read previous) order))
    (transit : Query Previous (fun _previous => Nat)) :
    Query Previous (fun previous =>
      List (Token (object.read previous) order (window.read previous))) :=
  window.dependentMap fun previous activeWindow =>
    branchExcess activeWindow (transit.read previous)

/-! The aggregate cold schedule is likewise a dependent query.  The packing
profile is read from the predecessor ledger; Core's query map then computes
the selected branch-excess family without copying the profile or accepting a
caller-supplied list. -/
noncomputable def selectedBranchExcessQuery
    (object : ObjectQuery)
    (packing : Query Previous
      (fun previous =>
        Profile (object.read previous) 13)) :
    Query Previous (fun previous =>
      List (BranchExcessOccurrence (object.read previous) 13)) :=
  packing.dependentMap fun _previous profile => selectedBranchExcess profile

noncomputable def selectedBranchExcessScheduleQuery
    (object : ObjectQuery)
    (packing : Query Previous
      (fun previous =>
        Profile (object.read previous) 13)) :
    Query Previous (fun previous =>
      Enumeration (BranchExcessOccurrence (object.read previous) 13)) :=
  packing.dependentMap fun _previous profile => selectedBranchExcessSchedule profile

/-- Restrict the exact predecessor-owned packing schedule to its
ambient-cubic owners.  This is a dependent query of the packing ledger: it
does not select a second packing or accept an independently supplied window
family. -/
noncomputable def ambientCubicScheduledExteriorBranchesQuery
    (object : ObjectQuery)
    (packing : Query Previous
      (fun previous =>
        Profile (object.read previous) 13)) :
    Query Previous (fun previous =>
      Enumeration
        (AmbientCubicScheduledExteriorBranch (packing.read previous))) :=
  packing.dependentMap fun _previous profile =>
    ambientCubicScheduledExteriorBranches profile

/-- The exact fifteen-stub identity for every member of the active
ambient-cubic schedule.  This is a dependent theorem query of the packing
ledger, not a registered scalar or a copied count. -/
noncomputable def ambientCubicExternalStubCountQuery
    (object : ObjectQuery)
    (packing : Query Previous
      (fun previous => Profile (object.read previous) 13)) :
    Query Previous (fun previous =>
      ∀ owner : AmbientCubicScheduledExteriorBranch
          (packing.read previous),
        externalStubCount owner.1.1.1.1 = 15) :=
  packing.dependentMap fun _previous _profile owner =>
    ambientCubicOwner_externalStubCount owner

/-- The exact thirteen-unit branch-excess identity for every member of the
same active ambient-cubic schedule.  The transit subtraction and count are
proved by the graph backend and remain indexed by the literal packing. -/
noncomputable def ambientCubicBranchExcessLengthQuery
    (object : ObjectQuery)
    (packing : Query Previous
      (fun previous => Profile (object.read previous) 13)) :
    Query Previous (fun previous =>
      ∀ owner : AmbientCubicScheduledExteriorBranch
          (packing.read previous),
        (branchExcess owner.1.1.1.1 2).length = 13) :=
  packing.dependentMap fun _previous _profile owner =>
    ambientCubicOwner_branchExcessLength owner

noncomputable def branchExcessChecksQuery {order : Nat}
    (object : ObjectQuery)
    (window : Query Previous (fun previous =>
      Window (object.read previous) order)) :
    Query Previous (fun _previous => Nat) :=
  window.map fun _previous activeWindow =>
    branchExcessChecks activeWindow

noncomputable def regularityDecisionQuery {order baseline : Nat}
    (object : ObjectQuery)
    (window : Query Previous (fun previous =>
      Window (object.read previous) order)) :
    Query Previous (fun previous =>
      Decidable (Regularity (object.read previous) order baseline
        (window.read previous))) :=
  window.dependentMap fun _previous activeWindow =>
    regularityDecidable (baseline := baseline) activeWindow

/-! The complete cold-corridor family is derived dependently from the exact
packing query.  The result remains indexed by that same packing value, so a
later strategy cannot substitute a detached window or occurrence list. -/
noncomputable def canonicalFamilyProducerQuery {order : Nat}
    (object : ObjectQuery)
    (packing : Query Previous
      (fun previous => Profile (object.read previous) order))
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Query Previous fun _ => Enumeration Handoff)
    (handoffSupport : (previous : Previous) → Handoff →
      Finset (object.read previous).Vertex) :
    Query Previous (fun previous =>
      Core.Finite.ColdCorridor.Producer.FamilyProducer
        (AmbientCubicScheduledExteriorBranch (packing.read previous))) :=
  packing.dependentMap fun previous activePacking =>
    canonicalFamilyProducer activePacking CycleLengthOK
      cycleLengthDecidable Target decideTarget
      (handoffItems.read previous) (handoffSupport previous)

end Hypostructure.Graph.InducedPathCold.QuerySurface
