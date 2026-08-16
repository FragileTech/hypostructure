import { Link } from "react-router-dom";

import { L, LeanCode } from "../LeanCode";

export function ProblemPage() {
  return (
    <>
      <header className="docs-header">
        <p className="hero-eyebrow">Defining a problem</p>
        <h1>The problem is the only input</h1>
        <p className="docs-lead">
          An application tells the framework what it is proving exactly once,
          as one <L>Core.Problem</L> and the data indexed by it: a{" "}
          <L>Target</L>, a <L>Progress</L> order for minimality, and a fact
          vocabulary. Everything else — the residual a branch argues about, its
          refinement relation, its <L>FactSystem</L>, the branch contexts and the
          minimal-counterexample scope — is derived from those by Core. No
          step of a proof ever mentions problem-specific carriers.
        </p>
      </header>

      <section>
        <h2>Problem</h2>
        <p>
          The universal problem data contains only an ambient type, its
          baseline predicate, and the branch state indexed by the current
          ambient object. Targets and optional capabilities are supplied
          separately.
        </p>
        <LeanCode source="Hypostructure/Core/Problem.lean">{`
          /-- Irreducible data shared by every tactic in one proof program. -/
          structure Problem where
            Ambient : Type
            Baseline : Ambient -> Prop
            BranchState : Ambient -> Type
            /-- Type of optional, typed presentation data shared by its strategies. -/
            Presentation : Type := PUnit
            /-- Problem-owned metadata and parameters.  \`none\` keeps existing problem
            declarations source-compatible; declarations that need typed presentation
            data install it with \`some\`. -/
            presentation : Option Presentation := none
        `}</LeanCode>
        <ul>
          <li>
            <strong><L>Ambient</L></strong> — the type of objects the theorem
            quantifies over.
          </li>
          <li>
            <strong><L>Baseline</L></strong> — the standing hypothesis every
            object of the theorem satisfies. Objects that fail it are simply
            not part of the problem.
          </li>
          <li>
            <strong><L>BranchState</L></strong> — dependent state a branch may
            carry alongside its object. A problem with no such state uses{" "}
            <L>fun _ =&gt; Unit</L>.
          </li>
          <li>
            <strong><L>Presentation</L> / <L>presentation</L></strong> —
            optional, defaulted; typed presentation data shared by the
            problem's strategies. Most problems leave both at their defaults.
          </li>
        </ul>
        <p>
          Three fields are mandatory. That is the whole of what a problem{" "}
          <em>is</em>; the theorem to be proved is deliberately not one of them.
        </p>
      </section>

      <section>
        <h2>Target</h2>
        <p>
          Targets are kept separate from <L>Problem</L> so the same problem
          registration can be reused by different theorem statements or
          terminal predicates.
        </p>
        <LeanCode source="Hypostructure/Core/Problem.lean">{`
          structure Target (P : Problem) where
            Predicate : P.Ambient -> Prop
            Statement : Prop
            statement_to_target :
              Statement -> forall object, P.Baseline object -> Predicate object
            target_to_statement :
              (forall object, P.Baseline object -> Predicate object) -> Statement
        `}</LeanCode>
        <p>
          <L>Predicate</L> is what a proof establishes about every baseline
          object; <L>Statement</L> is the public theorem as it will be stated.
          The two bridge fields are formulation laws relating the one to the
          other — they carry no mathematical content of the proof itself. A
          branch that <em>avoids</em> the target is one whose object fails{" "}
          <L>Predicate</L>; that is the sense in which a counterexample is a
          counterexample.
        </p>
        <p>
          When the theorem is exactly the closure of a predicate, both bridges
          are the identity:
        </p>
        <LeanCode source="Hypostructure/Core/Problem.lean">{`
          /-- The target whose public statement is exactly its own closure: every
          baseline object satisfies the registered predicate.  Both bridge fields are
          the identity, so a problem whose theorem *is* the closure of a predicate
          registers this and supplies no formulation law. -/
          def Target.ofPredicate (P : Problem) (Predicate : P.Ambient -> Prop) :
              Target P where
            Predicate := Predicate
            Statement := forall object, P.Baseline object -> Predicate object
            statement_to_target := fun statement => statement
            target_to_statement := fun closure => closure
        `}</LeanCode>
      </section>

      <section>
        <h2>Progress</h2>
        <p>
          A progress profile is an explicit capability: a well-founded measure
          on ambient objects, available to steps that require strict progress.
          A proof by minimal counterexample needs one; a problem that never
          argues by minimality does not.
        </p>
        <LeanCode source="Hypostructure/Core/Progress.lean">{`
          /-- A well-founded measure available to tactics that require strict progress. -/
          structure Progress (P : Problem) where
            Measure : Type
            lt : Measure -> Measure -> Prop
            wellFounded : WellFounded lt
            measure : P.Ambient -> Measure

          /-- The strict ambient-object relation induced by a progress profile. -/
          def Progress.Smaller (progress : Progress P) (G H : P.Ambient) : Prop :=
            progress.lt (progress.measure G) (progress.measure H)

          /-- Pulling back a well-founded measure relation remains well-founded. -/
          theorem Progress.wellFounded_smaller (progress : Progress P) :
              WellFounded progress.Smaller

          /-- No ambient object is strictly smaller than itself. -/
          theorem Progress.not_smaller_self (progress : Progress P) (G : P.Ambient) :
              Not (progress.Smaller G G)

          /-- Equal measures cannot certify a strict replacement. -/
          theorem Progress.not_smaller_of_measure_eq (progress : Progress P)
              {G H : P.Ambient} (measure_eq : progress.measure G = progress.measure H) :
              Not (progress.Smaller G H)
        `}</LeanCode>
        <p>
          <L>Smaller G H</L> is the strict order on objects the profile
          induces; <L>wellFounded_smaller</L> is what a minimality argument
          ultimately rests on. Because <L>Progress</L> depends on nothing about
          its problem except <L>Ambient</L> — not <L>Baseline</L>, not{" "}
          <L>BranchState</L>, not the presentation — a profile registered once
          transports for free to any other problem with the same ambient type:
        </p>
        <LeanCode source="Hypostructure/Core/Progress.lean">{`
          def Progress.ofAmbientEq {P Q : Problem}
              (h : Q.Ambient = P.Ambient) (progress : Progress P) : Progress Q
        `}</LeanCode>
      </section>

      <section>
        <h2>ProblemInput: the residual</h2>
        <p>
          The residual every assembly argues about is a{" "}
          <L>ProblemInput P</L>: one ambient object together with the baseline
          theorem and branch state registered by its problem. This is the
          residual type in <L>ExactLedger (ProblemInput P) current known</L>{" "}
          throughout a proof.
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/ProblemInput.lean">{`
          /-- One ambient object together with the baseline theorem and branch state
          registered by its \`Core.Problem\`. -/
          structure ProblemInput (P : Core.Problem) where
            object : P.Ambient
            baseline : P.Baseline object
            branchState : P.BranchState object
        `}</LeanCode>
        <p>
          Core supplies its <Link to="/lean/ledger">
            <L>RefinementSystem</L>
          </Link>{" "}
          instance. The refinement relation is <em>object equality</em>:
        </p>
        <LeanCode source="Hypostructure/Core/Strategy/ProblemResidual.lean">{`
          /-- Object equality is the refinement relation of the problem-input domain.
          A fact-only step is \`refl\`; a step that rewrites branch state keeps the object
          and therefore keeps every established fact applicable. -/
          instance problemInputRefinement (P : Core.Problem) :
              RefinementSystem (Strategy.ProblemInput P) where
            Subject := P.Ambient
            subject input := input.object
            Refines new old := new.object = old.object
            refl _ := rfl
            trans new_middle middle_old := new_middle.trans middle_old
            subject_eq refinement := refinement
        `}</LeanCode>
        <p>
          That is the honest relation for this domain. Once the opening scope
          has selected an object, no later step replaces the object it argues
          about: a step may only add facts (<L>RefinementSystem.refl</L>) or
          move branch state while the object stays fixed. Because{" "}
          <L>Subject</L> is the object itself, <L>subject_eq</L> is exactly the
          statement that a refinement never changes what the branch is proving
          a target about. Fact-only steps discharge their refinement obligation
          by reflexivity; a step that genuinely changes the residual must prove
          the new residual refines the old one.
        </p>
      </section>

      <section>
        <h2>Contexts and minimality</h2>
        <p>
          From a problem, a target predicate and a progress profile, Core
          derives the notions a minimal-counterexample argument needs. None of
          these are written per problem.
        </p>
        <LeanCode source="Hypostructure/Core/Context.lean">{`
          /-- The inherited state of one branch. -/
          structure BranchContext (P : Problem) where
            G : P.Ambient
            baseline : P.Baseline G
            state : P.BranchState G

          /-- A branch context on which the external target has not been realized. -/
          structure AvoidingContext (P : Problem) (Target : P.Ambient -> Prop)
              extends BranchContext P where
            avoids : Not (Target G)

          /-- Every strictly smaller baseline object satisfies the target. -/
          def MinimalityKernel (P : Problem) (Target : P.Ambient -> Prop)
              (progress : Progress P) (ctx : BranchContext P) : Prop :=
            forall H : P.Ambient,
              progress.Smaller H ctx.G -> P.Baseline H -> Target H

          /-- A target-avoiding branch equipped with a minimal-counterexample principle
          for one explicit progress profile. -/
          structure MinimalCounterexampleContext (P : Problem) (Target : P.Ambient -> Prop)
              (progress : Progress P) extends AvoidingContext P Target where
            minimal : MinimalityKernel P Target progress toBranchContext
        `}</LeanCode>
        <p>
          A <L>BranchContext</L> is the same data as a <L>ProblemInput</L> seen
          from the context side. An <L>AvoidingContext</L> adds the branch
          condition — the object does not satisfy the target — and a{" "}
          <L>MinimalCounterexampleContext</L> adds the minimality kernel: every
          strictly smaller baseline object <em>does</em> satisfy the target.
        </p>
        <p>The selection principle is one theorem, owned by Core:</p>
        <LeanCode source="Hypostructure/Core/Context.lean">{`
          /-- Select a minimal target-avoiding baseline object using only the registered
          well-founded progress relation and a branch-state initializer. -/
          theorem AvoidingContext.exists_minimalCounterexample
              {P : Problem} {Target : P.Ambient -> Prop}
              (ctx : AvoidingContext P Target)
              (progress : Progress P)
              (stateOf : (G : P.Ambient) -> P.BranchState G) :
              Nonempty (MinimalCounterexampleContext P Target progress)
        `}</LeanCode>
        <p>
          Its counterexample predicate is <L>P.Baseline G ∧ ¬ Target G</L> and
          its minimality is <L>progress.wellFounded_smaller.has_min</L>. Two
          consequences are exposed for use inside a branch:
        </p>
        <LeanCode source="Hypostructure/Core/Context.lean">{`
          /-- The target consequence for any strictly smaller baseline object. -/
          theorem MinimalCounterexampleContext.target_of_smaller
              (ctx : MinimalCounterexampleContext P Target progress) {H : P.Ambient}
              (smaller : progress.Smaller H ctx.G) (baseline : P.Baseline H) :
              Target H

          /-- A strictly smaller avoiding branch contradicts minimality. -/
          theorem MinimalCounterexampleContext.contradiction_of_smaller
              (ctx : MinimalCounterexampleContext P Target progress)
              (candidate : AvoidingContext P Target)
              (smaller : progress.Smaller candidate.G ctx.G) : False
        `}</LeanCode>
      </section>

      <section>
        <h2>What you write, what you get</h2>
        <dl className="docs-properties">
          <div>
            <dt>You supply</dt>
            <dd>
              One <L>Problem</L> (ambient type, baseline, branch state); one{" "}
              <L>Target</L> (predicate, statement, two bridges); one{" "}
              <L>Progress</L> if the argument is by minimality; one{" "}
              <L>FactVocabulary</L> naming the facts the argument proves; a
              branch-state initializer <L>stateOf</L>; and the encoding of the
              selection fact. Nothing else is problem-specific.
            </dd>
          </div>
          <div>
            <dt>Core derives</dt>
            <dd>
              The residual domain <L>ProblemInput P</L> with its{" "}
              <L>RefinementSystem</L> (object equality); the domain's sole{" "}
              <L>FactSystem</L> with the reserved closure key; the branch
              contexts and the minimal-counterexample selection; and the
              opening of the branch scope that commits the selection as the
              first ledger fact.
            </dd>
          </div>
        </dl>
        <p>
          The next page covers the two derived pieces an application touches
          directly: the fact vocabulary, and opening the scope.
        </p>
      </section>
    </>
  );
}
