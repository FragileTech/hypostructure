import Hypostructure.Graph.Node20aStructure

namespace Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph CyclePassage S1child3 Classical
open Strategy.InterfaceReplacement
universe u

/-- The selected structure at the canonical witness: one separating orientation,
and a dependent passage signature for every original positive certificate. -/
def OriginalCyclePassageAtWitness {data : Parameters} {G : FiniteObject.{u}}
    (w : SparseTargetDefectWitness data G) : Prop :=
  ∃ P N : Finset G.Vertex, w.Orientation P N ∧ w.Separates P N ∧
    w.CyclesUsePrivateEdge P N ∧
    ¬ ((SupportAtom.retainedPiece G w.support P).graph ≤
      (SupportAtom.retainedPiece G w.support N).graph) ∧
    ∀ c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
      data.LengthOK, Nonempty (Passage w P N c)

/-- The one new fact. The canonical equation preserves the incoming residual's
witness; no cycle, pair, support, context or realization domain is replaced. -/
def OriginalCyclePassageStatement (data : Parameters) (G : FiniteObject.{u}) : Prop :=
  ∃ w : SparseTargetDefectWitness data G,
    sparseTargetDefectWitness data G = some w ∧ w.Spec ∧ OriginalCyclePassageAtWitness w

namespace OriginalCyclePassageStatement

/-- S1, including the connected-component consequence. The dependent passage
contains the exact rotation equality, simple lift and internal private index. -/
theorem S1 {data : Parameters} {G : FiniteObject.{u}}
    (h : OriginalCyclePassageStatement data G) :
    ∃ w : SparseTargetDefectWitness data G,
      sparseTargetDefectWitness data G = some w ∧ w.Spec ∧
      ∃ P N : Finset G.Vertex, w.Orientation P N ∧ w.Separates P N ∧
        ∀ c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
          data.LengthOK, ∃ p : Passage w P N c,
          ActiveEndpoints w p.interval p.lift ∧
          (SupportAtom.retainedPiece G w.support P).graph.Reachable (.inl p.interval.a) p.pr ∧
          (SupportAtom.retainedPiece G w.support P).graph.Reachable p.pr (.inl p.interval.b) ∧
          (G.graph ⊓ SimpleGraph.fromRel (fun x y => x ∈ P ∧ y ∈ P)).Reachable
            p.interval.a.1 (SupportAtom.pieceDecode G w.support p.pr) ∧
          (G.graph ⊓ SimpleGraph.fromRel (fun x y => x ∈ P ∧ y ∈ P)).Reachable
            (SupportAtom.pieceDecode G w.support p.pr) p.interval.b.1 := by
  obtain ⟨w, canonical, spec, P, N, orientation, separates, _, _, cycles⟩ := h
  refine ⟨w, canonical, spec, P, N, orientation, separates, ?_⟩
  intro c
  obtain ⟨p⟩ := cycles c
  exact ⟨p, p.active, p.contacts.1, p.contacts.2, p.ambient_contacts⟩

/-- S2 projects the two edges, their original-cycle incidence, private support,
piece exclusivity, and the same omitted vertex's negative-gluing isolation. -/
theorem S2 {data : Parameters} {G : FiniteObject.{u}}
    (h : OriginalCyclePassageStatement data G) :
    ∃ w : SparseTargetDefectWitness data G,
      sparseTargetDefectWitness data G = some w ∧ w.Spec ∧
      ∃ P N : Finset G.Vertex, w.Orientation P N ∧ w.Separates P N ∧
        ∀ c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
          data.LengthOK, ∃ p : Passage w P N c, PrivateWedge w N p.interval p.lift := by
  obtain ⟨w, canonical, spec, P, N, orientation, separates, _, _, cycles⟩ := h
  refine ⟨w, canonical, spec, P, N, orientation, separates, ?_⟩
  intro c
  obtain ⟨p⟩ := cycles c
  exact ⟨p, p.private_wedge⟩

/-- S3 projects f007 on the same two edges; high private vertices force both
neighbours tight, without assuming that the private vertex is high. -/
theorem S3 {data : Parameters} {G : FiniteObject.{u}}
    (h : OriginalCyclePassageStatement data G) :
    ∃ w : SparseTargetDefectWitness data G,
      sparseTargetDefectWitness data G = some w ∧ w.Spec ∧
      ∃ P N : Finset G.Vertex, w.Orientation P N ∧ w.Separates P N ∧
        ∀ c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
          data.LengthOK, ∃ p : Passage w P N c, TightWedge w p.interval p.lift := by
  obtain ⟨w, canonical, spec, P, N, orientation, separates, _, _, cycles⟩ := h
  refine ⟨w, canonical, spec, P, N, orientation, separates, ?_⟩
  intro c
  obtain ⟨p⟩ := cycles c
  exact ⟨p, p.tight_wedge⟩

/-- Checked weakest-case projection: three-label, both-nonwhole cycles retain
all three claims together. No realization or high-vertex premise is required,
so unrealized contexts and an all-tight wedge are included. -/
theorem weakest_case {data : Parameters} {G : FiniteObject.{u}}
    (h : OriginalCyclePassageStatement data G) :
    ∃ w : SparseTargetDefectWitness data G,
      sparseTargetDefectWitness data G = some w ∧ w.Spec ∧
      ∃ P N : Finset G.Vertex, w.Orientation P N ∧ w.Separates P N ∧
        (∀ c : CycleCertificate (glue (SupportAtom.retainedPiece G w.support P) w.outside)
            data.LengthOK, ∃ p : Passage w P N c,
            ActiveEndpoints w p.interval p.lift ∧ PrivateWedge w N p.interval p.lift ∧
              TightWedge w p.interval p.lift) := by
  obtain ⟨w, canonical, spec, P, N, orientation, separates, _, _, cycles⟩ := h
  refine ⟨w, canonical, spec, P, N, orientation, separates, ?_⟩
  intro c
  obtain ⟨p⟩ := cycles c
  exact ⟨p, p.active, p.private_wedge, p.tight_wedge⟩

end OriginalCyclePassageStatement
end Hypostructure.Graph.Strategy.Spine
