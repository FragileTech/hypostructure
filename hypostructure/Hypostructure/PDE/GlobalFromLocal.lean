import Hypostructure.Core.Assembly.Amalgamation
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Global regularity assembled from local estimates

This is the closing step of every localization argument, done once for the
framework:

> Let `region` be a set, and suppose every point of `region` carries a nested
> pair of windows `place ∈ inner ⋐ outer ⋐ region` on which the local theorem
> applies.  Then the conclusion holds on all of `region`.

The classical proof is one sentence: each point gets a neighbourhood on which
the property holds, the property is *local*, and those neighbourhoods cover
the region.  The only mathematical content is therefore the word "local", and
this module is organised around making that word a hypothesis rather than an
appeal to intuition.

* `LocalityProfile` is exactly that hypothesis: a property of sets that passes
  to subsets and that can be recognised on an open cover.  A domain supplies
  one profile per property it wants to globalize and gets the globalization
  for free.
* `HoldsLocallyOn` is the cover premise and `LocalityProfile.holds` is the
  one-line proof.
* `NestedWindow` is the paper's `place ∈ inner ⋐ outer ⋐ region` tower.  The
  assembly reads only the openness of the inner window: compact containment is
  what the *local* theorem needs in order to produce its estimate, not what
  the *gluing* needs in order to combine the results.  It is recorded anyway
  so that the hypothesis a domain discharges is literally the one its local
  theorem states.
* The concrete corollary is smoothness: a map that is `ContDiffOn` near every
  point of a set is `ContDiffOn` on it.  Mathlib already owns the locality of
  `ContDiffOn` --- `contDiffOn_of_locally_contDiffOn` *is* the
  `LocalityProfile` for smoothness --- so nothing analytic is reproved here.
* The compact variant is the second half of the classical proof: on a compact
  subset finitely many windows suffice, so the maximum of the finitely many
  local constants is a uniform constant.  `IsCompact.elim_nhds_subcover`
  supplies the subcover.
* Finally the profile is wired to Core.  `localToGlobalProfile` turns any such
  property into an `AtomContextAssembly.LocalToGlobalProfile`, which is what
  `LocalToGlobalProfile.run`, `node`, `globalize` and `globalizeOpenResult`
  already consume; and `contDiffOn_amalgamate` does the same for Core's
  `CompatibleFamily`, so per-window local *witnesses* amalgamate into a single
  global witness that is smooth on the whole region.

Nothing here names an equation, an operator, a problem, or a dimension.
-/

namespace Hypostructure.PDE

open Set
open scoped ContDiff

universe uPlace uSite uAmbient uBranch

/-! ## Locality as an explicit hypothesis -/

section Locality

variable {Place : Type uPlace} [TopologicalSpace Place]

/--
A *local* property of subsets of `Place`.

The two fields are the two things "local" is ever used to mean in an analytic
argument, and the globalization below needs exactly them:

* `holds_of_subset` --- a property holding on a region holds on any smaller
  one.  This is what lets a point's window be shrunk to fit inside the region
  under study.
* `holds_of_localWindows` --- if every point of a region has an open window on
  which the property holds relative to the region, then it holds on the whole
  region.  This is the direction with content, and the direction a domain must
  justify: it fails for global statements such as boundedness or
  integrability, which is precisely why it is a hypothesis and not a lemma.
-/
structure LocalityProfile (Holds : Set Place → Prop) where
  /-- The property passes to subsets. -/
  holds_of_subset : ∀ {small large : Set Place}, small ⊆ large → Holds large → Holds small
  /-- The property is recognised on an open cover of the region. -/
  holds_of_localWindows : ∀ region : Set Place,
    (∀ place ∈ region, ∃ window : Set Place,
      IsOpen window ∧ place ∈ window ∧ Holds (region ∩ window)) →
    Holds region

/--
The cover premise: every point of `region` has an open window on which the
property already holds relative to `region`.  This is what a local theorem
discharges, one point at a time.
-/
def HoldsLocallyOn (Holds : Set Place → Prop) (region : Set Place) : Prop :=
  ∀ place ∈ region, ∃ window : Set Place,
    IsOpen window ∧ place ∈ window ∧ Holds (region ∩ window)

/--
**Global from local, in its bare form.**

A local property holding locally at every point of a region holds on the
region.  This is the profile's own recognition field, named so that consumers
never unfold the structure.
-/
theorem LocalityProfile.holds {Holds : Set Place → Prop}
    (profile : LocalityProfile Holds) {region : Set Place}
    (locally : HoldsLocallyOn Holds region) : Holds region :=
  profile.holds_of_localWindows region locally

/--
The nested window tower `place ∈ inner ⋐ outer ⋐ region` of the classical
statement.

`closure_inner_subset_outer` is the compact containment `⋐`.  The
globalization never reads it: it is the local theorem, not the assembly, that
needs room between the windows.  Carrying it keeps the hypothesis a domain
discharges identical to the one its local theorem states, and makes
`inner ⊆ region` derivable instead of assumed a second time.
-/
structure NestedWindow (place : Place) (region : Set Place) where
  /-- The window on which the local theorem delivers its conclusion. -/
  inner : Set Place
  /-- The larger window whose data the local theorem may use. -/
  outer : Set Place
  /-- The inner window is a neighbourhood of the point. -/
  inner_open : IsOpen inner
  /-- The point sits in its own inner window. -/
  mem_inner : place ∈ inner
  /-- Compact containment of the inner window in the outer one. -/
  closure_inner_subset_outer : closure inner ⊆ outer
  /-- No estimate ever uses data outside the outer window, which stays inside
  the region. -/
  outer_subset_region : outer ⊆ region

namespace NestedWindow

variable {place : Place} {region : Set Place}

/-- The inner window lies in the region, through the outer one. -/
theorem inner_subset_region (window : NestedWindow place region) :
    window.inner ⊆ region :=
  fun _ mem =>
    window.outer_subset_region
      (window.closure_inner_subset_outer (subset_closure mem))

end NestedWindow

/--
The nested-window premise implies the cover premise.

Only two things are used: the inner window is open and contains the point, and
`region ∩ inner ⊆ inner`, so the local conclusion transports down by
`holds_of_subset`.
-/
theorem holdsLocallyOn_of_nestedWindows {Holds : Set Place → Prop}
    (profile : LocalityProfile Holds) {region : Set Place}
    (windows : ∀ place ∈ region,
      ∃ window : NestedWindow place region, Holds window.inner) :
    HoldsLocallyOn Holds region := by
  intro place mem
  obtain ⟨window, holds⟩ := windows place mem
  exact ⟨window.inner, window.inner_open, window.mem_inner,
    profile.holds_of_subset inter_subset_right holds⟩

/--
**Global regularity assembled from local estimates.**

If every point of `region` carries a nested window tower on whose inner window
the property already holds, then the property holds on all of `region`.

This is the source theorem with the equation removed.  Note that `region` is
not required to be open: openness is what lets a domain *produce* the towers,
so it belongs to the hypothesis being discharged and not to the assembly step.
-/
theorem holds_of_nestedWindows {Holds : Set Place → Prop}
    (profile : LocalityProfile Holds) {region : Set Place}
    (windows : ∀ place ∈ region,
      ∃ window : NestedWindow place region, Holds window.inner) :
    Holds region :=
  profile.holds (holdsLocallyOn_of_nestedWindows profile windows)

end Locality

/-! ## The compact variant: finitely many windows, one constant

The second half of the classical proof.  On a compact subset of the region the
cover thins to a finite one, and any quantity controlled window by window is
then controlled uniformly by the maximum of the local bounds.
-/

section Compactness

variable {Place : Type uPlace} [TopologicalSpace Place]

/--
Finitely many windows suffice on a compact set.

The hypotheses are exactly what a local theorem produces at each centre: an
open window around it on which the property holds.  The conclusion keeps the
property at every selected centre, so the finite family is usable and not
merely a cover.
-/
theorem exists_finite_windows {Holds : Set Place → Prop}
    {compactPart : Set Place} (compact : IsCompact compactPart)
    (window : Place → Set Place)
    (window_open : ∀ centre ∈ compactPart, IsOpen (window centre))
    (window_mem : ∀ centre ∈ compactPart, centre ∈ window centre)
    (window_holds : ∀ centre ∈ compactPart, Holds (window centre)) :
    ∃ centres : Finset Place,
      compactPart ⊆ (⋃ centre ∈ centres, window centre) ∧
        ∀ centre ∈ centres, Holds (window centre) := by
  obtain ⟨centres, centres_mem, cover⟩ :=
    compact.elim_nhds_subcover window fun centre mem =>
      (window_open centre mem).mem_nhds (window_mem centre mem)
  exact ⟨centres, cover,
    fun centre mem => window_holds centre (centres_mem centre mem)⟩

/--
**The maximum of the local constants.**

A quantity bounded on each window by that window's own constant is bounded on
a compact set by a single constant: pass to a finite subcover and take the
maximum of the finitely many local bounds.

`0` is thrown into the maximum only because the finite family may be empty ---
the compact set itself may be, and then there is no local constant to maximize
over.
-/
theorem exists_uniform_bound {compactPart : Set Place}
    (compact : IsCompact compactPart) (window : Place → Set Place)
    (window_open : ∀ centre ∈ compactPart, IsOpen (window centre))
    (window_mem : ∀ centre ∈ compactPart, centre ∈ window centre)
    (size localBound : Place → ℝ)
    (bounded : ∀ centre ∈ compactPart, ∀ place ∈ window centre,
      size place ≤ localBound centre) :
    ∃ uniform : ℝ, ∀ place ∈ compactPart, size place ≤ uniform := by
  classical
  obtain ⟨centres, centres_mem, cover⟩ :=
    compact.elim_nhds_subcover window fun centre mem =>
      (window_open centre mem).mem_nhds (window_mem centre mem)
  refine ⟨(insert (0 : ℝ) (centres.image localBound)).max'
    ⟨0, Finset.mem_insert_self _ _⟩, fun place mem => ?_⟩
  obtain ⟨centre, centre_mem, place_mem⟩ := mem_iUnion₂.1 (cover mem)
  refine le_trans
    (bounded centre (centres_mem centre centre_mem) place place_mem) ?_
  exact Finset.le_max' _ _
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem localBound centre_mem))

/--
The compact variant fed directly by the nested-window premise.

The windows are not supplied as a function here but produced point by point by
the local theorem, so a single classical choice names them.  The conclusion is
a genuinely finite object: a finite set of centres, one explicit window at
each, and the local conclusion on every one of them.
-/
theorem exists_finite_nestedWindows {Holds : Set Place → Prop}
    {region compactPart : Set Place} (compact : IsCompact compactPart)
    (contained : compactPart ⊆ region)
    (windows : ∀ place ∈ region,
      ∃ window : NestedWindow place region, Holds window.inner) :
    ∃ (centres : Finset Place) (chosen : Place → Set Place),
      compactPart ⊆ (⋃ centre ∈ centres, chosen centre) ∧
        ∀ centre ∈ centres,
          IsOpen (chosen centre) ∧ chosen centre ⊆ region ∧
            Holds (chosen centre) := by
  classical
  choose window window_holds using windows
  obtain ⟨chosen, chosen_eq⟩ :
      ∃ chosen : Place → Set Place,
        ∀ (place : Place) (mem : place ∈ region),
          chosen place = (window place mem).inner :=
    ⟨fun place => if mem : place ∈ region then (window place mem).inner else ∅,
      fun _ mem => dif_pos mem⟩
  obtain ⟨centres, centres_mem, cover⟩ :=
    compact.elim_nhds_subcover chosen fun centre mem => by
      rw [chosen_eq centre (contained mem)]
      exact ((window centre (contained mem)).inner_open).mem_nhds
        (window centre (contained mem)).mem_inner
  refine ⟨centres, chosen, cover, fun centre mem => ?_⟩
  have inside : centre ∈ region := contained (centres_mem centre mem)
  rw [chosen_eq centre inside]
  exact ⟨(window centre inside).inner_open,
    (window centre inside).inner_subset_region, window_holds centre inside⟩

end Compactness

/-! ## The concrete corollary: smoothness

Smoothness is the local property the source theorem globalizes, and mathlib
already proves it is one.  Instantiating `LocalityProfile` with
`contDiffOn_of_locally_contDiffOn` is therefore the entire analytic content,
and every statement below is a specialization of the generic theorems above.
-/

section Smoothness

variable {Field : Type*} [NontriviallyNormedField Field]
  {Domain : Type*} [NormedAddCommGroup Domain] [NormedSpace Field Domain]
  {Codomain : Type*} [NormedAddCommGroup Codomain] [NormedSpace Field Codomain]

/-- Smoothness of a fixed map is a local property of sets.  Both fields are
mathlib lemmas; nothing is reproved. -/
def contDiffLocality (smoothness : WithTop ℕ∞) (map : Domain → Codomain) :
    LocalityProfile fun region : Set Domain =>
      ContDiffOn Field smoothness map region where
  holds_of_subset := fun subset holds => holds.mono subset
  holds_of_localWindows := fun _region locally =>
    contDiffOn_of_locally_contDiffOn locally

/--
**Global smoothness from local smoothness**, at any order and over any
nontrivially normed field.

Every point of the region carries a nested window tower on whose inner window
the map is `C^smoothness`; then it is `C^smoothness` on the region.
-/
theorem contDiffOn_of_nestedWindows (smoothness : WithTop ℕ∞)
    (map : Domain → Codomain) {region : Set Domain}
    (windows : ∀ place ∈ region, ∃ window : NestedWindow place region,
      ContDiffOn Field smoothness map window.inner) :
    ContDiffOn Field smoothness map region :=
  holds_of_nestedWindows (contDiffLocality smoothness map) windows

end Smoothness

section RealSmoothness

variable {Domain : Type*} [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  {Codomain : Type*} [NormedAddCommGroup Codomain] [NormedSpace ℝ Codomain]

/--
**The source theorem, with the equation removed.**

If every point of `region` has a neighbourhood on which `map` is `C^∞`, then
`map` is `C^∞` on `region`.  This is the exact content of "u ∈ C^∞(U),
∇p ∈ C^∞(U)": the local theorem is applied on each window of the cover, and
smoothness --- being local --- assembles.

The premise is stated as a plain neighbourhood rather than a `NestedWindow`
because that is the weakest thing the assembly uses; the nested-tower form is
`contDiffOn_of_nestedWindows`.
-/
theorem contDiffOn_top_of_locally (map : Domain → Codomain)
    {region : Set Domain}
    (windows : ∀ place ∈ region, ∃ window : Set Domain,
      IsOpen window ∧ place ∈ window ∧ ContDiffOn ℝ ∞ map window) :
    ContDiffOn ℝ ∞ map region := by
  refine (contDiffLocality (Field := ℝ) ∞ map).holds fun place mem => ?_
  obtain ⟨window, window_open, place_mem, smooth⟩ := windows place mem
  exact ⟨window, window_open, place_mem, smooth.mono inter_subset_right⟩

/--
The same conclusion from the paper's nested cylinders: a tower
`place ∈ inner ⋐ outer ⋐ region` at every point, with `C^∞` on each inner
window.
-/
theorem contDiffOn_top_of_nestedWindows (map : Domain → Codomain)
    {region : Set Domain}
    (windows : ∀ place ∈ region, ∃ window : NestedWindow place region,
      ContDiffOn ℝ ∞ map window.inner) :
    ContDiffOn ℝ ∞ map region :=
  contDiffOn_of_nestedWindows (Field := ℝ) ∞ map windows

end RealSmoothness

/-! ## Amalgamating per-window witnesses

`holds_of_nestedWindows` globalizes a property of *one* given map.  When each
window instead carries its own local witness, the witnesses have to be glued
first, and that is Core's `CompatibleFamily`.  Smoothness of the amalgamation
on each window is Core's `amalgamate_property` plus mathlib's
`ContDiffOn.congr`; smoothness on the whole region is then the locality
profile again.  No new gluing machinery is introduced.
-/

section Amalgamation

variable {Site : Type uSite} {Field : Type*} [NontriviallyNormedField Field]
  {Domain : Type*} [NormedAddCommGroup Domain] [NormedSpace Field Domain]
  {Codomain : Type*} [NormedAddCommGroup Codomain] [NormedSpace Field Codomain]

/-- The region owned by one site of a compatible family, as a set. -/
def siteWindow (family : Core.CompatibleFamily Site Domain Codomain)
    (site : Site) : Set Domain :=
  {place | family.Mem site place}

/--
The amalgamated witness is as smooth on each window as that window's own local
witness.

The only input is that `ContDiffOn` depends on a map solely through its values
on the set in question, which is `ContDiffOn.congr`; the transport itself is
Core's `amalgamate_property`.
-/
theorem contDiffOn_amalgamate
    (family : Core.CompatibleFamily Site Domain Codomain)
    (smoothness : WithTop ℕ∞)
    (localSmooth : ∀ site : Site, ContDiffOn Field smoothness
      (family.localSection site) (siteWindow family site))
    (site : Site) :
    ContDiffOn Field smoothness family.amalgamate (siteWindow family site) :=
  family.amalgamate_property
    (Property := fun site map =>
      ContDiffOn Field smoothness map (siteWindow family site))
    (fun _site _left _right agree holds =>
      holds.congr fun place mem => (agree place mem).symm)
    localSmooth site

/--
**A globally smooth witness out of per-window witnesses.**

Local witnesses attached to open windows, agreeing on overlaps and each smooth
on its own window, amalgamate into one witness that is smooth on every region
their windows cover.  This is the sheaf form of the source theorem: the
regularity is produced window by window and the object itself is produced by
the gluing.
-/
theorem contDiffOn_amalgamate_of_cover
    (family : Core.CompatibleFamily Site Domain Codomain)
    (smoothness : WithTop ℕ∞)
    (window_open : ∀ site : Site, IsOpen (siteWindow family site))
    (localSmooth : ∀ site : Site, ContDiffOn Field smoothness
      (family.localSection site) (siteWindow family site))
    {region : Set Domain}
    (covered : ∀ place ∈ region, ∃ site : Site, family.Mem site place) :
    ContDiffOn Field smoothness family.amalgamate region := by
  refine (contDiffLocality smoothness family.amalgamate).holds fun place mem => ?_
  obtain ⟨site, site_mem⟩ := covered place mem
  exact ⟨siteWindow family site, window_open site, site_mem,
    (contDiffOn_amalgamate family smoothness localSmooth site).mono
      inter_subset_right⟩

end Amalgamation

/-! ## Wiring to Core's local-to-global closure

`AtomContextAssembly.LocalToGlobalProfile` is the framework's registration
point for "pointwise local facts imply a global one", and it is deliberately
topology-free: its sites are the exact sites of one ambient object.  A
topological property does fit it, provided the domain says which region of
`Place` each object occupies and which window each site owns.  Once that is
said, this construction discharges the profile's obligation using the locality
hypothesis alone, and the resulting profile is consumed by the existing
`run` / `node` / `globalize` / `globalizeOpenResult` API without change.
-/

section CoreBridge

variable {Place : Type uPlace} [TopologicalSpace Place]
  {P : Core.Problem.{uAmbient, uBranch}} {E : Core.SemanticEquivalence P}

/--
Register a topological locality theorem as a Core local-to-global profile.

`window` says which open piece of `Place` a site owns and `covered` says the
windows of an object's sites cover its region.  `window_holds` is the local
theorem: the atom/context fact stored at a site implies the property on that
site's window.  The global conclusion is the property on the whole region, and
its proof is `holds_of_localWindows` applied to the pointwise certificate.
-/
def localToGlobalProfile {Holds : Set Place → Prop}
    (profile : LocalityProfile Holds)
    (assembly : Core.AtomContextAssembly P E)
    (LocalFact : assembly.LocalProperty)
    (region : P.Ambient → Set Place)
    (window : (object : P.Ambient) → assembly.Site object → Set Place)
    (window_open : ∀ (object : P.Ambient) (site : assembly.Site object),
      IsOpen (window object site))
    (covered : ∀ (object : P.Ambient), ∀ place ∈ region object,
      ∃ site : assembly.Site object, place ∈ window object site)
    (window_holds : ∀ (object : P.Ambient) (site : assembly.Site object),
      LocalFact (assembly.atom object site) (assembly.context object site) →
        Holds (window object site)) :
    assembly.LocalToGlobalProfile LocalFact fun object => Holds (region object) where
  close := fun object certificate =>
    profile.holds fun place mem => by
      obtain ⟨site, site_mem⟩ := covered object place mem
      exact ⟨window object site, window_open object site, site_mem,
        profile.holds_of_subset inter_subset_right
          (window_holds object site (certificate.localAt site))⟩

end CoreBridge

end Hypostructure.PDE

