import Hypostructure.Graph.Strategy.SpineRows.Basic

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Nodes `[33]` and `[35]`: minimal curvature-dependence support

The rank-drop arm already contains a concrete proper determination.  Following
`lem:curvature-dependence-routing`, this row chooses, for its fixed determined
coordinate, a certificate whose connected declared support is inclusion-minimal.
All candidates are local mathematical objects; the sole proof-data input and
output are the exact-ledger facts named in the manifest.

Part III of the manuscript repeats the Branch-D state of node `[33]` verbatim
at node `[35]`, with the incoming edge labelled `from [33]`.  Hence `[35]`
does not publish a second `branchDependence` fact.  It does, however, carry the
separate labelled fact `lem:separated-testers`; `separatedTestersRow` below
appends exactly that fact before node `[36]` tests the same certificate. -/
@[reducible] noncomputable def branchDependenceRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) := by
  classical
  exact
    factOnly `Hypostructure.Graph.Strategy.Spine.branchDependence
      (rowManifest (K .curvatureRankDrop) (K .branchDependence)
        (by simp [K_eq_iff]))
      (fun inputs =>
        let inherited := (inputs.get (K .curvatureRankDrop)).down
        .cons (key := K .branchDependence)
          ⟨by
            letI : Fintype inputs.current.object.Vertex :=
              @FinEnum.instFintype _ inputs.current.object.vertices
            rcases inherited with
              ⟨packing, valid, packingCard, below, test, testMember,
                determiners, determinersSubset, finite, proper, declared,
                functional, reducing, determines⟩
            let support := inputs.current.object.remainderSupport packing
            let family := inputs.current.object.internalWedgeFamily support
            let supportData := family
            have supportDataCarried : ∀ coordinate ∈ supportData,
                Graph.FiniteObject.internalWedgeSupport
                    (region := support) coordinate ⊆ declared.support := by
              intro coordinate coordinateMember
              exact declared.carries coordinate coordinateMember
            have certified :
                DeterminationCertificate data inputs.current.object packing test
                  determiners declared supportData :=
              ⟨testMember, determinersSubset, finite, proper, functional,
                reducing, determines, rfl, supportDataCarried⟩
            refine ⟨packing, valid, packingCard, below, test, ?_⟩
            dsimp only
            set Supports :=
              inputs.current.object.vertexFinset.powerset.filter
                fun candidateSupport =>
                  ∃ basis candidate,
                    candidate.support = candidateSupport ∧
                      ∃ candidateSupportData,
                        DeterminationCertificate data inputs.current.object
                          packing test basis candidate candidateSupportData
            change ∃ selectedDeterminers selectedQuotient selectedSupportData,
              DeterminationCertificate data inputs.current.object packing test
                    selectedDeterminers selectedQuotient selectedSupportData ∧
                ∀ smaller : Finset inputs.current.object.Vertex,
                  smaller ⊂ selectedQuotient.support →
                    ∀ narrower : remainderQuotient data inputs.current.object packing,
                      narrower.support = smaller →
                        ∀ narrowerDeterminers narrowerSupportData,
                          ¬ DeterminationCertificate data inputs.current.object
                            packing test narrowerDeterminers narrower
                              narrowerSupportData
            have inhabited : declared.support ∈ Supports := by
              simp only [Supports, Finset.mem_filter, Finset.mem_powerset]
              exact ⟨by intro vertex _; simp, determiners, declared, rfl,
                supportData, certified⟩
            obtain ⟨leastSupport, leastMember, least⟩ :=
              Finset.exists_min_image Supports Finset.card ⟨_, inhabited⟩
            have leastInSupports := leastMember
            simp only [Supports, Finset.mem_filter, Finset.mem_powerset]
              at leastInSupports
            rcases leastInSupports with ⟨_, leastInSupports⟩
            obtain ⟨chosenDeterminers, chosen, supportEq,
              chosenSupportData, chosenCertified⟩ := leastInSupports
            subst leastSupport
            refine ⟨chosenDeterminers, chosen, chosenSupportData,
              chosenCertified, ?_⟩
            intro smaller strict narrower narrowerSupport narrowerDeterminers
              narrowerSupportData narrowerCertified
            have carried : smaller ∈ Supports := by
              simp only [Supports, Finset.mem_filter, Finset.mem_powerset]
              exact ⟨by intro vertex _; simp, narrowerDeterminers, narrower,
                narrowerSupport, narrowerSupportData, narrowerCertified⟩
            have minimum := least smaller carried
            exact absurd (Finset.card_lt_card strict) (by omega)⟩
          .nil)

end Hypostructure.Graph.Strategy.Spine
