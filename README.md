A Blueprint
===========

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"

At JetBrains, we develop the most effective, convenient,
and enjoyable tools for engineers and researchers so that their natural drive to develop can flourish and bear fruit.
We dare to pursue ambitious, visionary ideas.
We wanted to use a programming language that we ourselves would enjoy, so we created one,
and now Kotlin is the language of choice for millions of software developers worldwide.

Likewise, we have endeavoured to develop a convenient and enjoyable language for formal reasoning:
a general-purpose language for expressing results, definitions,
conjectures, constructions, and proofs in all major areas of mathematics and computer science —
including, of course, theorems about Kotlin applications and Kotlin itself.
After 25 years of active research,
supported by a series of breakthroughs resulting from the Univalent Foundations programme,
we finally have a blueprint for such a language.
These developments have also led to a [variety of ideas for Kotlin](kotlin-series)
that dramatically improve its capabilities for correct-by-construction software design
and make it amenable to automated verification.

§ The Foundation
----------------

Higher Categorical Construction Calculus (HCCC)
is a tentative name for a univalent computational type theory we are developing.
As a proof calculus, it will be capable of classical reasoning with choice, structural induction over its own language,
and higher categorical reasoning.
It will enjoy decidable proof checking
and will be shown
to be a conservative extension of the classical set theory extended with appropriate higher infinity axioms.

It is a _construction calculus_,
because, besides proofs, it can express constructions such as numerical algorithms,
straightedge and compass constructions, and abstract constructions such as profinite completions.
In line with the tradition of the original [Calculus of Constructions](https://en.wikipedia.org/wiki/Calculus_of_constructions),
it features a universal type of propositions to express structures defined by non-first-order axiomatic theories.  
It is _higher categorical_,
because instances of structures, i.a. Models of axiomatic theories,
come conveniently prepackaged in displayed ω-categories that keep track of structure-respecting correspondences,
homomorphisms, and equivalences on every level,
so that all proofs and constructions can be generalized, specialized, and transferred along.

- Starting point of HCCC is the third-generation univalent type theory
  [HOTT currently being developed by M. Shulman et al.](https://ncatlab.org/nlab/show/higher+observational+type+theory)
  with propositional resizing and inductive types powerful enough to speak of the real numbers ℝ and the Turing-complete
  partiality monad `Computation<T>`. 
- [□Parametric Polymorphism for Agnostic Type Theories](polymorphism):
  We add the parametric quantification `∀<X : T> Y` and
  the S4 necessity modality mapping each proper type `T` to the set `□T` of its closed-form inhabitants.
  This way, the theory acquires truly polymorphic type (`List<T>`), typeclass (`Monoid<T>`), 
  and instance (`id : ∀<T> T → T`) definitions and LEM-compatible (□-internal) parametric reasoning,
  so `{ x ↦ x }` can be shown to be the unique closed-form inhabitant of `∀<T> T → T`.
- [◇Classical Reasoning in Constructive Type Theories](modalities):
  We add the S4 possibility modality mapping each proper type `T` to the spectrum `◇T` of its formal inhabitants
  to enable univalence-compatible (◇-internal) classical reasoning with choice
  without compromising favorable computational properties and decidability of proof and type checking. 
  The computational content of the ◇-modality turns out to be given by the
  [Verse calculus](https://simon.peytonjones.org/verse-calculus/), a recently developed deterministic approach to 
  functional logic programming.
  Incidentally, we also vastly expand of the computational power by allowing all classically provable algorithms.
- [Higher Categorical Type Theory](reedy-types):
  We add types representing Reedy categories, presheaves on them and functors between them,
  resulting in a [homoiconic](https://homotopytypetheory.org/2014/03/03/hott-should-eat-itself/)
  computational type theory with native ω-categories
  which is still interpretable in every elementary ∞-topos with enough inductive types.
- [Bounded Inductive Construction Calculus](BICC):
  We are developing a finitistic core theory to use for proving desired meta-theoretical properties,
  namely typechecking decidability, canonicity, normalization, and conservativity of HCCC over
  [M. Shulman’s ZMC/𝕊 set theory](https://arxiv.org/abs/0810.1279) and thus their equiconsistency.

§ Towards an enjoyable reasoning language
-----------------------------------------

A sound theoretical foundation still needs to be put into shape.
In a series of [short](kotlin_literate.pdf) [proposals](kotlin_academic.pdf) we develop a versatile syntax
designed for excellent readability,
conciseness, and typographic perfection.
Based on Kotlin, Python, Agda, Lean, Scala, and Fortress,
it is a culmination of over two decades of meticulous collection and evaluation of ideas,
carefully assembled into a coherent system.

Human readers instantly recognize implicit conversions, forgive minor omissions, and think along with the author,
bridging nontrivial gaps and transforming arguments "mutatis mutandis".
Proof formalization is plagued by the pain to elaborate all of this explicitly.
An enjoyable proof language must at least address the issues of that kind with known solution approaches:
- Most frustrating are the type mismatch issues caused by obvious equalities that do not hold computationally. Partial solutions:
   - The universe `SProp` of definitionally propositional types ([“Definitional proof-irrelevance without K”](https://dl.acm.org/doi/10.1145/3290316))
   - The universe `SData` of definitionally set-like types ([“Observational Equality meets CiC”](https://hal.science/hal-04535982v1))
   - Limited predicate subtyping ([“Predicate Subtyping with Proof Irrelevance”](https://arxiv.org/abs/2110.13704))
   - Equations on neutral terms ([“New Equations for Neutral Terms”](https://dl.acm.org/doi/10.1145/2502409.2502411)) and parallel reductions ([“The Taming of the Rew”](https://dl.acm.org/doi/10.1145/3434341))
   - Typechecking-driven automated equality proof synthesis
- The richness and flexibility of the type system lures into reinventing the wheel. Every library tends to use its own slightly different inventory of standard types and typeclasses, which massively hinders their interoperability. Partial solutions:
  - [Algebraic ornaments](https://arxiv.org/abs/1212.3806) and [Dependent Interoperability](https://dl.acm.org/doi/abs/10.1145/2103776.2103779)
  - Typeclass-based mechanism of contextual implicit coercions as in [Lean](https://lean-lang.org/functional_programming_in_lean/type-classes/coercion.html) and [Scala3](https://dotty.epfl.ch/docs/reference/contextual/conversions.html).
  - Fortress-style configurable inheritance for sound typeclass hierarchies.
  - Contextually configurable instance resolution and derivation.

§ HCCC as a programming language
--------------------------------

Computational type theories are functional programming languages capable of exhaustive internal reasoning about the programs’
behaviour.
The ability to make use of classical termination proofs makes HCCC an exceptionally powerful total programming language.
It is also capable of expressing general Turing-complete (and thus potentially diverging)
computations and computations on exact real numbers
since both the `Computation<T>`-monad and the datatype ℝ of Cauchy reals are available as quotient inductive-inductive types.
In addition,
the computational interpretation of ◇-modality is given by the recently introduced [Verse Calculus](https://simon.peytonjones.org/verse-calculus/),
which adds the unparalleled expressiveness of deterministic functional logic programming.

HCCC seems to have everything one could ever want from a language for _non-interactive programming_.
Yet, as great as it sounds in theory,
programming in bare-bones intensional type theories demands for frustrating amounts of explicit termination,
productivity, and convertibility proofs.
For a decent practical programming language,
we additionally need indexed modalities for size-guarded recursion and clock-guarded corecursion,
and liquid types for automated reasoning where applicable.

Embracing interactive programming is a vast subject in its own right. 
While non-interactive programs deal only with data,
interactive programs interact with the environment and deal with references in addition to values.
We think
that interactivity can be dealt with
by introducing substructural object and reference variables and the substructural cousins of □/◇-modalities:
the pure modality ⊡ and the live modality ⟐.
Pure objects `x : ⊡X` are self-contained;
they do not interact through any references, even those available in the context,
see [Controlling purity in Kotlin](kotlin_purity.pdf).
Live objects `x : ⟐X` may have captured references, i.e.
they can interact through references not present in the context.
Live objects include those that may interact or have interacted with the outside world,
so they have a spectrum of possible states rather than one fixed state,
just like the formal variables in Verse calculus.
Analogously to Verse,
an object can interact with ⟐-objects becoming ⟐ itself (from the internal point of view, x will have a fixed state),
but as opposed to Verse we do not have `one` and `all` operators,
we can only extract value into the non-live context
if we have a proof that the live object eventually converges to a unique determined state.

The extrinsic state of objects `x : X` can be described as an element of its trace monoid.
When concurrency and interaction come into play,
we have to deal with incomplete information about the operational state of objects.
Instead of a fixed state, we have a set of possible states.
Thus, the “state” of a live object `x : ⟐X` is a boolean combination of fixed states,
given by an element of the respective trace algebra.

For instance, if we start two coroutines in parallel,
and these coroutines perform actions on the same object,
its algebraic state is given by a sum of possible outcomes for all possible on orders of the actions
performed on the object by these two coroutines.
Objects such as heaps,
where fresh mutable objects and arrays can be created,
have very particular trace monoids
generated by a partial commutative monoid of creation and substitution operators
giving rise to the associated concurrent separation logic within the type theory.

We have not yet worked out the formal definition for the interactive extension of HCCC.
However, we have developed [type system extension for Kotlin](kotlin_objects.pdf) that embraces effects,
mutability, concurrency, and synchronization,
while being intended to be translatable into the purported interactive HCCC.

Similar to the [case of guarded (co)recursion modalities](https://bentnib.org/productive.pdf),
the whole system will be reducible to plain HCCC by encoding objects as parametrized relative
(co)monads and interpreting expressions involving reference types via do-notation.
See
[Paella: algebraic effects with parameters and their handlers](https://icfp24.sigplan.org/details/hope-2024-papers/7).


§ The Missing Part
------------------

There are two major areas that are not yet covered:
- The [affine logic for biconstructive mathematics](https://arxiv.org/abs/1805.07518) on the reasoning side;
- Quantum algorithms and interacting quantum automata on the programming side;

The live modality ⟐ introduces the notion of objects with mixed states and interactions that makes such objects entangled
(allowing only particular combinations of their respective states),
which reminds of quantum mechanics.
Trace algebras for heaps,
which extrinsically describe states of objects inside the heap,
can be defined in terms of their duals, the algebras of observables,
which are commutative since observations are independent of each other.
A non-commutative generalization,
in which observations are no longer necessarily independent,
would allow the description of quantum objects
where the coexistence of multiple pure states is inherent rather than due to lack of knowledge.
The non-commutative generalization of state creation and substitution algebras would allow
describing quantum arenas where separate objects can be entangled.
There, the separately created objects generally do not remain separable objects,
and the picture of arenas as collections of distinct objects becomes fuzzy.
We cannot reason in terms of "distinct particles" any more,
and have to reason in terms of "field quanta", with quantum arenas playing the role of quantum fields.
We assume this analogy can be made precise 
and will allow describing quantum computations and perhaps also non-discrete quantum processes in general
and might shed new some light onto formalization of quantum field theory.

The affine logic for biconstructive mathematics seems an entirely distinct subject at first.
However, biconstructive propositions are semantically described as particularly simple Chu spaces,
while the general form of which is known to also describe the Hilbert spaces of quantum states.
It resonates with the situation in the homotopy type theory,
where the propositions are particularly simple (truncated) types.
