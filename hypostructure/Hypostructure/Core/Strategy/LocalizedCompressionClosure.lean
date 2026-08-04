import Hypostructure.Core.Strategy.Data
import Hypostructure.CT3.Theorems

/-!
# Reusable strategy: localized exhaustive compression closure

Domain-generic (Graph and PDE alike): the recurring minimal-counterexample
pattern "a rank-type quantity has dropped, so localize to a schedule of
candidate regions and search them for one that admits an exact, verified
compression to a smaller/simpler representative, closing the branch by
minimality." Given a per-input schedule of regions (e.g. the connected
components of a localized support, for Graph; the analogous localized
pieces of a domain, for PDE) and a registered exact-response-compression
capability for each scheduled region, this strategy searches the whole
schedule and closes the branch to the registered target as soon as ANY
region compresses.

The one domain-specific input this file can use, if the caller has it, is a
`bridge` proof connecting a compression certificate to the registered
`Target`; that proof (never invented here) is supplied by the caller.  It is
optional: registering the real region schedule and running the real
compression search does not require already having the closing argument —
a caller with real candidates but no closing theorem yet registers `bridge
:= none` and gets a genuine, still-open search rather than being forced to
fabricate either the search data or the closure.  Everything else — the
exhaustive per-region scan, the classification, and (when `bridge` is
supplied) the closure derivation — is generic and reuses only the
underlying exact response-compression executor's own already axiom-free
soundness theorems (`Hypostructure.CT3.Theorems`). -/

namespace Hypostructure.Core.Strategy

open Hypostructure.Core.Residual

universe uAmbient uBranch uComponent uPrevious uRepresentative uContext
  uCoordinate uValue uCandidate uRow

/-- Extract the compression certificate from a CT3 execution result already
known to have terminated at `.compression` — the only constructor `Outcome`
admits once its terminal index is fixed.  Fully generic over `Previous`
(independent of any registered problem), so it applies to any CT3 run. -/
def certificateOfCompression {Previous : Type uPrevious}
    {spec : Hypostructure.CT3.Spec.{uPrevious, uRepresentative,
      uContext, uCoordinate, uValue, uCandidate, uRow} Previous}
    {capability : Hypostructure.CT3.Capability spec}
    (result : Hypostructure.CT3.ExecutionResult spec capability)
    (h : result.terminal = Hypostructure.CT3.Terminal.compression) :
    Hypostructure.CT3.CompressionCertificate capability result.stage.previous :=
  match h ▸ result.outcome with
  | .compression certificate => certificate

variable {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}

/-- Localized exhaustive compression closure: run the exact-response
compression executor on every scheduled region of `input`, and close to the
registered target as soon as one compresses (via the caller-supplied
`bridge`).  The other side — no scheduled region compresses — is left as an
still-open residual; this strategy makes no claim about it. -/
noncomputable def localizedCompressionClosure
    (Component : Strategy.ProblemInput P -> Type uComponent)
    (schedule : (input : Strategy.ProblemInput P) ->
      Finite.Enumeration (Component input))
    (spec : (input : Strategy.ProblemInput P) -> Component input ->
      Hypostructure.CT3.Spec.{max uAmbient uBranch, uRepresentative, uContext,
        uCoordinate, uValue, uCandidate, uRow} (Strategy.ProblemInput P))
    (capability : (input : Strategy.ProblemInput P) -> (c : Component input) ->
      Hypostructure.CT3.Capability (spec input c))
    (bridge : Option (PLift ((input : Strategy.ProblemInput P) ->
      (c : Component input) ->
      Hypostructure.CT3.CompressionCertificate (capability input c) input ->
      T.Predicate input.object)) := none) :
    Core.DichotomyData P T where
  LeftPayload := fun input => PLift (∃ c ∈ (schedule input).values,
    (Hypostructure.CT3.run (spec input c) (capability input c) input).terminal =
      .compression)
  RightPayload := fun input => PLift (¬ ∃ c ∈ (schedule input).values,
    (Hypostructure.CT3.run (spec input c) (capability input c) input).terminal =
      .compression)
  classify := fun input =>
    open Classical in
    if h : ∃ c ∈ (schedule input).values,
        (Hypostructure.CT3.run (spec input c) (capability input c) input).terminal =
          .compression then
      Sum.inl ⟨h⟩
    else
      Sum.inr ⟨h⟩
  closeLeft := bridge.map fun bridge => ⟨fun input witness => by
    obtain ⟨c, _cMem, hCompression⟩ := witness.down
    exact bridge.down input c
      (certificateOfCompression
        (Hypostructure.CT3.run (spec input c) (capability input c) input)
        hCompression)⟩

/-- Minimal-counterexample closure by well-founded compression: the general
reusable pattern behind `localizedCompressionClosure`'s `bridge`, made
total.  A caller with a real search (`Component`/`schedule`/`spec`/
`capability`, exactly as above) plus the four genuinely mathematical
ingredients below gets an unconditional closure for every input, with ALL
well-founded recursion handled here — no caller-side induction boilerplate:
- `measure`: a `Nat` measure on inputs;
- `replacement`: the compressed candidate, repackaged as a fresh input
  (with its own registered baseline);
- `measureDecreases`: the replacement is strictly smaller;
- `transport`: the replacement's target transports to the original's
  (typically via the registered CT3 spec's own `target_iff`-style theorem);
- `baseCase`: when the search finds no compressing region at all, the
  target holds anyway (the actual base case of the induction — this is the
  one piece of real mathematical content this pattern cannot supply itself,
  since it is exactly the "why does the argument terminate" fact specific to
  the application; everything else here is pure recursion plumbing). -/
noncomputable def wellFoundedCompressionClosure
    (Component : Strategy.ProblemInput P -> Type uComponent)
    (schedule : (input : Strategy.ProblemInput P) ->
      Finite.Enumeration (Component input))
    (spec : (input : Strategy.ProblemInput P) -> Component input ->
      Hypostructure.CT3.Spec.{max uAmbient uBranch, uRepresentative, uContext,
        uCoordinate, uValue, uCandidate, uRow} (Strategy.ProblemInput P))
    (capability : (input : Strategy.ProblemInput P) -> (c : Component input) ->
      Hypostructure.CT3.Capability (spec input c))
    (measure : Strategy.ProblemInput P -> Nat)
    (replacement : (input : Strategy.ProblemInput P) -> (c : Component input) ->
      Hypostructure.CT3.CompressionCertificate (capability input c) input ->
      Strategy.ProblemInput P)
    (measureDecreases : (input : Strategy.ProblemInput P) -> (c : Component input) ->
      (cert : Hypostructure.CT3.CompressionCertificate (capability input c) input) ->
      measure (replacement input c cert) < measure input)
    (transport : (input : Strategy.ProblemInput P) -> (c : Component input) ->
      (cert : Hypostructure.CT3.CompressionCertificate (capability input c) input) ->
      T.Predicate (replacement input c cert).object -> T.Predicate input.object)
    (baseCase : (input : Strategy.ProblemInput P) ->
      (¬ ∃ c ∈ (schedule input).values,
        (Hypostructure.CT3.run (spec input c) (capability input c) input).terminal =
          .compression) -> T.Predicate input.object) :
    (input : Strategy.ProblemInput P) -> T.Predicate input.object
  | input =>
    open Classical in
    if h : ∃ c ∈ (schedule input).values,
        (Hypostructure.CT3.run (spec input c) (capability input c) input).terminal =
          .compression then
      let c := h.choose
      let cert := certificateOfCompression
        (Hypostructure.CT3.run (spec input c) (capability input c) input)
        h.choose_spec.2
      transport input c cert
        (wellFoundedCompressionClosure Component schedule spec capability measure
          replacement measureDecreases transport baseCase (replacement input c cert))
    else
      baseCase input h
termination_by input => measure input
decreasing_by exact measureDecreases input _ _

end Hypostructure.Core.Strategy
