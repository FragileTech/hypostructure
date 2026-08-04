import Hypostructure.Core.Assembly.LocalToGlobal

/-!
# Amalgamation of overlapping local sections

`Locality` gives restriction and `AtomContextAssembly.LocalToGlobalProfile`
turns pointwise *propositions* into a global one.  Neither builds a global
*witness* out of local ones, and a pointwise certificate over an infinite
family of overlapping windows usually only exists once such a witness does:
the local data have to be amalgamated first.

This module is that missing sheaf step, and it is completely domain
independent --- no problem, no equation, no locality, no window.  A family of
local sections indexed by abstract sites, agreeing wherever two sites
overlap, amalgamates into one global section restricting to each.  Any
property that depends only on the values taken on a single site transports
from the local sections to the amalgamation.

`Hypostructure.Core.DependentOwnerGlueCapacity` is a different abstraction:
it glues *independent* per-owner choices and exists to bound cardinality.
This one is about overlap compatibility and carries no counting data.
-/

namespace Hypostructure.Core

universe uSite uPlace uValue

/--
A family of local sections that agree wherever their sites overlap.

`Mem site place` says `place` lies in the region of `site`.  `fallback` is
used only off the covered region and is never observed at a place that some
site contains.
-/
structure CompatibleFamily (Site : Type uSite) (Place : Type uPlace)
    (Value : Type uValue) where
  Mem : Site → Place → Prop
  localSection : Site → Place → Value
  compatible : ∀ (left right : Site) (place : Place),
    Mem left place → Mem right place →
      localSection left place = localSection right place
  fallback : Value

namespace CompatibleFamily

variable {Site : Type uSite} {Place : Type uPlace} {Value : Type uValue}
  (family : CompatibleFamily Site Place Value)

/-- The amalgamated global section. -/
noncomputable def amalgamate : Place → Value :=
  fun place =>
    open scoped Classical in
    if covered : ∃ site : Site, family.Mem site place then
      family.localSection covered.choose place
    else
      family.fallback

/-- On each site the amalgamation is that site's own local section.  This is
the only property of `amalgamate` a consumer needs. -/
theorem amalgamate_eq {site : Site} {place : Place}
    (mem : family.Mem site place) :
    family.amalgamate place = family.localSection site place := by
  classical
  have covered : ∃ site : Site, family.Mem site place := ⟨site, mem⟩
  rw [amalgamate, dif_pos covered]
  exact family.compatible _ _ place covered.choose_spec mem

/-- Off the cover the amalgamation is the declared fallback. -/
theorem amalgamate_eq_fallback {place : Place}
    (uncovered : ∀ site : Site, ¬ family.Mem site place) :
    family.amalgamate place = family.fallback := by
  classical
  have covered : ¬ ∃ site : Site, family.Mem site place := by
    rintro ⟨site, mem⟩
    exact uncovered site mem
  rw [amalgamate, dif_neg covered]

/--
A property depending only on the values taken on one site transports from
that site's local section to the amalgamation.

This is the step that turns per-window local facts into a pointwise
certificate over the whole cover, which is exactly what
`AtomContextAssembly.LocalToGlobalProfile` consumes.
-/
theorem amalgamate_property
    {Property : Site → (Place → Value) → Prop}
    (congruent : ∀ (site : Site) (left right : Place → Value),
      (∀ place, family.Mem site place → left place = right place) →
        Property site left → Property site right)
    (localProperty : ∀ site : Site, Property site (family.localSection site))
    (site : Site) : Property site family.amalgamate :=
  congruent site _ _ (fun _place mem => (family.amalgamate_eq mem).symm)
    (localProperty site)

end CompatibleFamily

end Hypostructure.Core
