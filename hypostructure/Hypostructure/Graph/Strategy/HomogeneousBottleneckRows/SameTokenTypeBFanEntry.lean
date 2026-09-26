import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[65]`, the literal same-token Type B handoff lane.**  Read the
decorated envelope produced at `[144]` from the current `ExactLedger` and append
the common Type B entry for those same objects.  The packing, core, envelope,
decorations, and all arm/fan-safety fields are retained verbatim; this row does
not manufacture a canonical negative component or an indexed cold-corridor
carrier. -/
@[reducible] noncomputable def sameTokenTypeBFanEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenTypeBFanEntry
    { Requires := [K .typeBHandoff]
      Produces := [K .typeBFanEntry]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let handoff := (inputs.get (K .typeBHandoff)).down
      .cons (key := K .typeBFanEntry)
        ⟨by
          -- Work over the abstract current object so the retained handoff
          -- witness is destructured without unfolding the input record.
          have handoffFact := handoff
          revert handoffFact
          generalize inputs.current.object = object
          intro handoffFact
          obtain ⟨_active, capacity, _activationEq, _cubic, _certified, _token,
              _role, _tokenMem, _positive, _excess, _forced, _sourceClass,
              _classified, _root, _rootEq, routed⟩ := handoffFact
          have envelopeOf :
              ∀ envelope : Graph.DecoratedHandoff.Envelope
                  object data.LengthOK
                  (handoffHighDegree data object)
                  (handoffAbsorbing data object capacity.packing),
                envelope.decorations.Nonempty →
                  SameTokenTypeBHandoffEnvelopeStatement data
                    object :=
            fun envelope decorated =>
              ⟨capacity.packing, capacity.packingValid, capacity.packingMaximal,
                envelope.core, envelope, rfl, decorated⟩
          apply Or.inr
          apply Or.inr
          rcases routed with ⟨_pattern, _subset, _shape, _routed, source⟩ |
              ⟨_centre, _pattern, _subset, _shape, _routed, source⟩ <;>
          · exact
              match source with
              | ⟨_p, _hp, _q, _hq, _pq, _dp, _hdp, _dq, _hdq, _label, _rp,
                  _rq, _validP, _validQ, _maximal, _h, _a, _b, _common, _tailP,
                  _tailQ, _decompP, _decompQ, _different, _armP, _armQ, _entryP,
                  _entryQ, _adjP, _adjQ, _issuedP, _issuedQ, _chainP, _chainQ,
                  _nodupP, _nodupQ, _landsP, _landsQ, _interiorP, _interiorQ,
                  _high, _avoids, _denied, _deniedSwap, envelope, envelopeEq,
                  _escape⟩ =>
                envelopeOf envelope (by
                  rw [envelopeEq]
                  simp [Graph.DecoratedHandoff.envelopeOfFirstSeparator])⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
