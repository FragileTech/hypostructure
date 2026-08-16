import { L } from "../LeanCode";
import { ApiReference, ReferenceLegend, type ApiModule } from "./ApiReference";

const SEMANTICS: ApiModule = {
  title: "Hypostructure.Core — semantic equivalence",
  paths: ["hypostructure/Hypostructure/Core/SemanticEquivalence.lean"],
  intro:
    "Representation equivalence with baseline invariance, and the invariance of one target under it.",
  entries: [
    {
      name: "SemanticEquivalence",
      kind: "structure",
      audience: "application",
      signature: `
        structure SemanticEquivalence (P : Problem) where
          equivalent : P.Ambient -> P.Ambient -> Prop
          equivalence : Equivalence equivalent
          baseline_iff : equivalent G H -> (P.Baseline G ↔ P.Baseline H)`,
      note: "Representation equivalence together with baseline invariance.",
    },
    {
      name: "SemanticEquivalence.refl / symm / trans",
      kind: "theorem",
      audience: "application",
      signature: `
        @[refl] theorem SemanticEquivalence.refl (E : SemanticEquivalence P) (G : P.Ambient) : E.equivalent G G
        @[symm] theorem SemanticEquivalence.symm (E : SemanticEquivalence P) : E.equivalent G H -> E.equivalent H G
        @[trans] theorem SemanticEquivalence.trans (E : SemanticEquivalence P) :
            E.equivalent G H -> E.equivalent H K -> E.equivalent G K`,
      note: "The equivalence laws, exposed as tagged lemmas.",
    },
    {
      name: "SemanticEquivalence.transport_baseline",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem SemanticEquivalence.transport_baseline (E : SemanticEquivalence P)
            (equivalent : E.equivalent G H) (baseline : P.Baseline G) : P.Baseline H`,
      note: "Transport a baseline proof forward across semantic equivalence.",
    },
    {
      name: "SemanticEquivalence.equality",
      kind: "def",
      audience: "application",
      signature: `
        def SemanticEquivalence.equality (P : Problem) : SemanticEquivalence P

        @[simp] theorem SemanticEquivalence.equality_equivalent_iff :
            (equality P).equivalent G H ↔ G = H`,
      note: "Equality supplies canonical semantics for every problem.",
    },
    {
      name: "TargetInvariant",
      kind: "structure",
      audience: "application",
      signature: `
        structure TargetInvariant {P : Problem} (E : SemanticEquivalence P) (Target : P.Ambient -> Prop) where
          target_iff : E.equivalent G H -> (Target G ↔ Target H)`,
      note: "Invariance of one external target under a chosen semantic equivalence.",
    },
    {
      name: "TargetInvariant.transport / transport_not",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem TargetInvariant.transport (invariant : TargetInvariant E Target) {G H : P.Ambient}
            (equivalent : E.equivalent G H) (target : Target G) : Target H

        theorem TargetInvariant.transport_not (invariant : TargetInvariant E Target) {G H : P.Ambient}
            (equivalent : E.equivalent G H) (avoids : Not (Target G)) : Not (Target H)`,
      note: "Transport a target proof, or target avoidance, forward across semantic equivalence.",
    },
    {
      name: "TargetInvariant.equality",
      kind: "def",
      audience: "application",
      signature: `
        def TargetInvariant.equality (P : Problem) (Target : P.Ambient -> Prop) :
            TargetInvariant (SemanticEquivalence.equality P) Target`,
      note: "Every target is invariant under equality semantics.",
    },
  ],
};

const ASSEMBLY: ApiModule = {
  title: "Hypostructure.Core — atom/context assembly",
  paths: ["hypostructure/Hypostructure/Core/Assembly/AtomContext.lean"],
  intro:
    "Interface-indexed local/global decomposition. Domains register extraction, compatibility, assembly and reconstruction; Core owns replacement and semantic transport.",
  entries: [
    {
      name: "AtomContextAssembly",
      kind: "structure",
      audience: "application",
      signature: `
        structure AtomContextAssembly (P : Problem) (E : SemanticEquivalence P) where
          Interface : Type
          Site : P.Ambient -> Type
          interface : (object : P.Ambient) -> Site object -> Interface
          Atom : Interface -> Type
          Context : Interface -> Type
          compatible : {interface : Interface} -> Atom interface -> Context interface -> Prop
          atom : (object : P.Ambient) -> (site : Site object) -> Atom (interface object site)
          context : (object : P.Ambient) -> (site : Site object) -> Context (interface object site)
          assemble : {interface : Interface} -> Atom interface -> Context interface -> P.Ambient
          extractedCompatible : forall object site,
            compatible (atom object site) (context object site)
          reconstruct : forall object site,
            E.equivalent (assemble (atom object site) (context object site)) object`,
      note: "Exact local/global decomposition indexed by a shared interface.",
    },
    {
      name: "AtomContextAssembly.Replacement",
      kind: "structure",
      audience: "application",
      signature: `
        structure AtomContextAssembly.Replacement (A : AtomContextAssembly P E)
            (object : P.Ambient) (site : A.Site object) where
          atom : A.Atom (A.interface object site)
          compatible : A.compatible atom (A.context object site)`,
      note: "A replacement atom certified compatible with the literal extracted context at one site.",
    },
    {
      name: "AtomContextAssembly.replace",
      kind: "def",
      audience: "application",
      signature: `
        def AtomContextAssembly.replace (A : AtomContextAssembly P E)
            {object : P.Ambient} {site : A.Site object}
            (replacement : A.Replacement object site) : P.Ambient`,
      note: "Framework-owned local replacement in the exact extracted context.",
    },
    {
      name: "AtomContextAssembly.reconstructedBaseline",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem AtomContextAssembly.reconstructedBaseline (A : AtomContextAssembly P E)
            (object : P.Ambient) (site : A.Site object) (baseline : P.Baseline object) :
            P.Baseline (A.assemble (A.atom object site) (A.context object site))`,
      note: "Reconstruction preserves the baseline through registered semantics.",
    },
    {
      name: "AtomContextAssembly.reconstructedTargetIff",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem AtomContextAssembly.reconstructedTargetIff (A : AtomContextAssembly P E)
            {Target : P.Ambient -> Prop} (invariant : TargetInvariant E Target)
            (object : P.Ambient) (site : A.Site object) :
            Target (A.assemble (A.atom object site) (A.context object site)) <-> Target object`,
      note: "Reconstruction preserves any target registered against the semantics.",
    },
  ],
};

const REPLACEMENT: ApiModule = {
  title: "Hypostructure.Core.Strategy.InterfaceReplacement",
  paths: ["hypostructure/Hypostructure/Core/Strategy/InterfaceReplacement.lean"],
  intro:
    "The reusable replacement exclusion at a minimal counterexample. Only the declarations consumed by verified steps are listed; the file's further compression and registration declarations are not documented.",
  entries: [
    {
      name: "Profile",
      kind: "structure",
      audience: "application",
      signature: `
        structure Profile {P : Core.Problem} {T : Core.Target P} (progress : Core.Progress P) where
          semantics : Core.SemanticEquivalence P
          targetInvariant : Core.TargetInvariant semantics T.Predicate
          assembly : Core.AtomContextAssembly P semantics
          Signature : assembly.Interface → Type
          signature : {interface : assembly.Interface} →
            assembly.Atom interface → Signature interface`,
      note: "Domain semantics consumed by the reusable strategy family. No executor, branch choice, ledger value or authored outcome.",
    },
    {
      name: "Profile.StrictReplacement",
      kind: "structure",
      audience: "application",
      signature: `
        structure Profile.StrictReplacement (profile : Profile progress)
            (ctx : Core.MinimalCounterexampleContext P T.Predicate progress)
            (site : profile.assembly.Site ctx.G) where
          replacement : profile.assembly.Replacement ctx.G site
          signature_eq : profile.signature replacement.atom =
            profile.signature (profile.assembly.atom ctx.G site)
          obstruction_le : profile.ObstructionProfileLE
            (profile.assembly.atom ctx.G site) replacement.atom
          baseline : P.Baseline (profile.assembly.replace replacement)
          smaller : progress.Smaller (profile.assembly.replace replacement) ctx.G`,
      note: "Equal interface signature, one-way obstruction inclusion, preserved baseline, strict decrease.",
    },
    {
      name: "Profile.strictReplacementImpossible",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem Profile.strictReplacementImpossible (profile : Profile progress)
            (ctx : Core.MinimalCounterexampleContext P T.Predicate progress)
            (site : profile.assembly.Site ctx.G) :
            ¬ Nonempty (profile.StrictReplacement ctx site)`,
      note: "A strict replacement at any site of a minimal counterexample is impossible. Consumes only ctx.target_of_smaller and ctx.avoids.",
    },
  ],
};

const MODULES = [SEMANTICS, ASSEMBLY, REPLACEMENT];

export function SemanticsApiPage() {
  return (
    <>
      <header className="docs-header">
        <p className="hero-eyebrow">Reference</p>
        <h1>Semantics and replacement API</h1>
        <p className="docs-lead">
          Semantic equivalence, target invariance, the atom/context assembly
          record, and the interface-replacement exclusion. Universe annotations
          and the repeated <L>{"{P : Problem}"}</L> binder are left out;
          everything else is verbatim.
        </p>
        <ReferenceLegend />
      </header>
      <ApiReference modules={MODULES} />
    </>
  );
}
