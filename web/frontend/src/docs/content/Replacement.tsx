import { Link } from "react-router-dom";

import { L, LeanCode } from "../LeanCode";

export function ReplacementPage() {
  return (
    <>
      <header className="docs-header">
        <p className="hero-eyebrow">Assembling a proof</p>
        <h1>Interface replacement</h1>
        <p className="docs-lead">
          Core ships one reusable theorem about minimal counterexamples: at any
          site of a selected minimal counterexample, a strict interface-local
          replacement is impossible. A domain supplies a semantic equivalence,
          the invariance of its target under it, and an interface-indexed
          atom/context decomposition; Core derives the exclusion. The result is
          mathematics that becomes a fact value — it carries no ledger,
          executor or history.
        </p>
      </header>

      <section>
        <h2>Semantic equivalence and target invariance</h2>
        <p>
          Representations may reconstruct an ambient object only up to a
          domain-provided equivalence. Baseline and target transport are
          recorded independently so one ambient problem can support several
          targets.
        </p>
        <LeanCode source="Hypostructure/Core/SemanticEquivalence.lean">{`
          /-- Representation equivalence together with baseline invariance. -/
          structure SemanticEquivalence (P : Problem) where
            equivalent : P.Ambient -> P.Ambient -> Prop
            equivalence : Equivalence equivalent
            baseline_iff : equivalent G H -> (P.Baseline G ↔ P.Baseline H)

          /-- Invariance of one external target under a chosen semantic equivalence. -/
          structure TargetInvariant {P : Problem}
              (E : SemanticEquivalence P) (Target : P.Ambient -> Prop) where
            target_iff : E.equivalent G H -> (Target G ↔ Target H)

          /-- Transport a target proof forward across semantic equivalence. -/
          theorem TargetInvariant.transport (invariant : TargetInvariant E Target) {G H : P.Ambient}
              (equivalent : E.equivalent G H) (target : Target G) : Target H

          /-- Transport target avoidance forward across semantic equivalence. -/
          theorem TargetInvariant.transport_not (invariant : TargetInvariant E Target) {G H : P.Ambient}
              (equivalent : E.equivalent G H) (avoids : Not (Target G)) : Not (Target H)

          /-- Equality supplies canonical semantics for every problem. -/
          def SemanticEquivalence.equality (P : Problem) : SemanticEquivalence P

          /-- Every target is invariant under equality semantics. -/
          def TargetInvariant.equality (P : Problem) (Target : P.Ambient -> Prop) :
              TargetInvariant (SemanticEquivalence.equality P) Target
        `}</LeanCode>
        <p>
          A domain whose objects are compared up to isomorphism registers that
          relation once with its baseline invariance, and separately proves
          each target invariant under it. A domain with no such notion uses{" "}
          <L>equality</L>.
        </p>
      </section>

      <section>
        <h2>Atom/context assembly</h2>
        <p>
          Domains register extraction, compatibility, assembly and
          reconstruction; Core owns replacement and semantic transport.
        </p>
        <LeanCode source="Hypostructure/Core/Assembly/AtomContext.lean">{`
          /-- Exact local/global decomposition indexed by a shared interface. -/
          structure AtomContextAssembly (P : Problem) (E : SemanticEquivalence P) where
            Interface : Type
            Site : P.Ambient -> Type
            interface : (object : P.Ambient) -> Site object -> Interface
            Atom : Interface -> Type
            Context : Interface -> Type
            compatible : {interface : Interface} ->
              Atom interface -> Context interface -> Prop
            atom : (object : P.Ambient) -> (site : Site object) ->
              Atom (interface object site)
            context : (object : P.Ambient) -> (site : Site object) ->
              Context (interface object site)
            assemble : {interface : Interface} ->
              Atom interface -> Context interface -> P.Ambient
            extractedCompatible : forall object site,
              compatible (atom object site) (context object site)
            reconstruct : forall object site,
              E.equivalent (assemble (atom object site) (context object site)) object
        `}</LeanCode>
        <p>
          A <em>site</em> of an object names a place where it decomposes into a
          local <em>atom</em> and the surrounding <em>context</em>, both typed
          by the shared <em>interface</em> at that site. Assembling the
          extracted atom back into the extracted context reconstructs the
          object up to the registered equivalence. On top of that record Core
          defines replacement:
        </p>
        <LeanCode source="Hypostructure/Core/Assembly/AtomContext.lean">{`
          /-- A replacement atom certified compatible with the literal extracted
          context at one site. -/
          structure AtomContextAssembly.Replacement (A : AtomContextAssembly P E)
              (object : P.Ambient) (site : A.Site object) where
            atom : A.Atom (A.interface object site)
            compatible : A.compatible atom (A.context object site)

          /-- Framework-owned local replacement in the exact extracted context. -/
          def AtomContextAssembly.replace (A : AtomContextAssembly P E)
              {object : P.Ambient} {site : A.Site object}
              (replacement : A.Replacement object site) : P.Ambient :=
            A.assemble replacement.atom (A.context object site)

          /-- Reconstruction preserves the baseline through registered semantics. -/
          theorem AtomContextAssembly.reconstructedBaseline (A : AtomContextAssembly P E)
              (object : P.Ambient) (site : A.Site object) (baseline : P.Baseline object) :
              P.Baseline (A.assemble (A.atom object site) (A.context object site))

          /-- Reconstruction preserves any target registered against the semantics. -/
          theorem AtomContextAssembly.reconstructedTargetIff (A : AtomContextAssembly P E)
              {Target : P.Ambient -> Prop} (invariant : TargetInvariant E Target)
              (object : P.Ambient) (site : A.Site object) :
              Target (A.assemble (A.atom object site) (A.context object site)) <-> Target object
        `}</LeanCode>
      </section>

      <section>
        <h2>The profile</h2>
        <p>
          A profile bundles the domain semantics the theorem consumes. It
          contains no executor, branch choice, ledger value or authored
          outcome.
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/InterfaceReplacement.lean">{`
          /-- Domain semantics consumed by the reusable strategy family.  This record
          contains no executor, branch choice, ledger value, or authored outcome. -/
          structure Profile {P : Core.Problem} {T : Core.Target P} (progress : Core.Progress P) where
            semantics : Core.SemanticEquivalence P
            targetInvariant : Core.TargetInvariant semantics T.Predicate
            assembly : Core.AtomContextAssembly P semantics
            Signature : assembly.Interface → Type
            signature : {interface : assembly.Interface} →
              assembly.Atom interface → Signature interface
        `}</LeanCode>
        <p>
          <L>Signature</L> is the interface data a replacement must preserve
          exactly; what counts as "the same signature" is the domain's choice.
        </p>
      </section>

      <section>
        <h2>Strict replacement is impossible at a minimal counterexample</h2>
        <p>
          A strict replacement at a site of a minimal counterexample is: a
          compatible replacement atom with the same signature, at most as
          obstructing as the source atom (a one-way inclusion,{" "}
          <L>ObstructionProfileLE</L>), whose result satisfies the baseline and
          is strictly smaller in the registered progress order.
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/InterfaceReplacement.lean">{`
          /-- A strict replacement in exactly the form required by the replacement
          lemma: equal interface signature, one-way obstruction inclusion, preserved
          baseline, and strict decrease. -/
          structure Profile.StrictReplacement
              (ctx : Core.MinimalCounterexampleContext P T.Predicate progress)
              (site : profile.assembly.Site ctx.G) where
            replacement : profile.assembly.Replacement ctx.G site
            signature_eq : profile.signature replacement.atom =
              profile.signature (profile.assembly.atom ctx.G site)
            obstruction_le : profile.ObstructionProfileLE
              (profile.assembly.atom ctx.G site) replacement.atom
            baseline : P.Baseline (profile.assembly.replace replacement)
            smaller : progress.Smaller
              (profile.assembly.replace replacement) ctx.G
        `}</LeanCode>
        <p>The theorem, with its proof — the proof is the explanation:</p>
        <LeanCode source="Hypostructure/Core/Strategy/InterfaceReplacement.lean">{`
          /-- A strict replacement at any site of a minimal counterexample is impossible.

          The proof is the manuscript's: the replaced object satisfies the baseline and
          is strictly smaller, so minimality gives it the target; the one-way obstruction
          inclusion carries that target back through the shared context to the source
          atom; and target-invariance of the reconstruction contradicts the selected
          object's avoidance.

          Everything it consumes is in \`ctx\` -- \`target_of_smaller\` and \`avoids\`, the two
          components of the selection.  There is no registration, payload, or closure
          record in the statement, so a consumer holding only the selection fact of the
          canonical ledger can apply it directly. -/
          theorem Profile.strictReplacementImpossible
              (ctx : Core.MinimalCounterexampleContext P T.Predicate progress)
              (site : profile.assembly.Site ctx.G) :
              ¬ Nonempty (profile.StrictReplacement ctx site) := by
            rintro ⟨replacement⟩
            have replacementTarget : T.Predicate
                (profile.assembly.replace replacement.replacement) :=
              ctx.target_of_smaller replacement.smaller replacement.baseline
            have sourceTarget : T.Predicate
                (profile.assembly.assemble
                  (profile.assembly.atom ctx.G site)
                  (profile.assembly.context ctx.G site)) :=
              replacement.obstruction_le
                (profile.assembly.context ctx.G site)
                (profile.assembly.extractedCompatible ctx.G site)
                replacement.replacement.compatible replacementTarget
            exact ctx.avoids
              ((profile.targetInvariant.target_iff
                (profile.assembly.reconstruct ctx.G site)).mp sourceTarget)
        `}</LeanCode>
        <p>
          Three steps: minimality (<L>target_of_smaller</L>) gives the replaced
          object the target; the one-way obstruction inclusion carries that
          target back, through the shared context, to the source atom assembled
          in place; target invariance of the reconstruction turns that into the
          target on the selected object, contradicting <L>avoids</L>. Everything
          it needs is in the context, which is why a step holding only the
          selection fact can apply it.
        </p>
      </section>

      <section>
        <h2>How a step uses it</h2>
        <p>
          The verified usage shape is: decode the selection into a{" "}
          <L>MinimalCounterexampleContext</L> (see{" "}
          <Link to="/lean/assembly">the assembly page</Link>), instantiate the
          domain's profile, convert the domain's own replacement hypothesis
          into a <L>StrictReplacement</L> at the relevant site — either
          directly or through a small bridge lemma — and apply the theorem. The
          resulting negation is the value of a fact.
        </p>
        <LeanCode>{`
          -- shape, not a compilable module
          (fun inputs =>
            let selection := (inputs.get (key .selection)).down
            let context := contextOfSelection inputs.current selection.1 selection.2
            let profile := domainProfile targetInvariant
            .cons (key := key .replacementExclusion)
              ⟨fun site domainReplacement =>
                let strict : profile.StrictReplacement context site :=
                  strictOfDomainReplacement domainReplacement
                profile.strictReplacementImpossible context site ⟨strict⟩⟩
              .nil)
        `}</LeanCode>
        <p>
          Only <L>Profile</L>, <L>Profile.StrictReplacement</L> and{" "}
          <L>Profile.strictReplacementImpossible</L> — with the supporting
          semantics and assembly records above — are consumed by verified steps;
          nothing else from that module is documented here.
        </p>
      </section>
    </>
  );
}
