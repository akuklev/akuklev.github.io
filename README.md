A Blueprint
===========

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com), [JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)

At JetBrains, we create the most effective, convenient, and pleasurable tools for engineers and researchers, allowing their the natural drive to develop to thrive and bear fruit. We dare to pursue ambitious visionary ideas. We wanted to use a programming language we'd enjoy using, so we created one, and now Kotlin is the language of choice for millions of software developers worldwide.

If we want to make Kotlin amenable for certified programming, we want a proof language and toolset we'd enjoy using. We believe that the best proof language for certified programming should be a general-purpose language results, definitions, conjectures, constructions, and proofs in all mainstream areas of mathematics and computer science. After 25 years of active research, aided by a number of breakthroughs sprouting from the Univalent Foundations Program, we finally have a blueprint for such a language.

§ Overview
----------

Higher Categorical Construction Calculus (HCCC) is a tentative name for a univalent computational type theory we're developing. As a proof calculus, it will be capable of classical reasoning with choice, structural induction over its own language, and higher categorical reasoning. It will enjoy decidable proof checking and will be shown to be a conservative extension of the classical set theory extended with appropriate higher infinity axioms.

It's a _construction calculus_, because, besides proofs, it can express constructions such as numerical algorithms, straightedge and compass constructions, and abstract constructions such as profinite completions. In line with the tradition of the original Calculus of Constructions, it features a universal type of propositions to express structures defined by non-first-order axiomatic theories.  
It is _higher categorical_, because instances of structures, i.a. models of axiomatic theories, come conveniently prepackaged in displayed ω-categories that keep track of structure-respecting correpsondences, homomorphisms, and equivalences on every level, so that all proofs and constructions can be generalized, specialized, and transferred along.

We develop HCCC in steps:
- Our starting point is is the third-generation univalent type theory [HOTT currently being developed by Shulman et al.](https://ncatlab.org/nlab/show/higher+observational+type+theory) with propositional resizing and quotient inductive-inductive definitions, including analytic real numbers ℝ and the Turing-complete computation monad `Computation<T>`. 
- [“□Parametric Polymorphism for Agnostic Type Theories”](polymorphism): We add the parametric quantification `∀<X : T> Y` and the S4 neccesity modality mapping each proper type `T` to the set `□T` of its closed-form inhabitants. This way, the theory acquires truly polymorphic type (`List<T>`), typeclass (`Monoid<T>`), and instance (`id : ∀<T> T → T`) definitions and LEM-compatible (□-internal) parametric reasoning, so `{ x ↦ x }` can be shown to be the unique closed-form inhabitant of `∀<T> T → T`.
- [“◇Classical Reasoning in Constructive Type Theories”](modalities): We add the S4 possibility modality mapping each proper type `T` to the spectrum `◇T` of its formal inhabitants to enable univalence-compatible (◇-internal) classical reasoning with choice without compromising favorable computational properties and decidability of proof/type checking. Additionally, we obtain a vast expansion of the computational power by allowing all classically provable algorithms and a dependently typed form of functional logic programming (see Verse calculus).
- [Higher Categorical Type Theory](reedy-types): We add types representing Reedy categories, presheaves on them and functors between them, resulting in a [homoiconic](https://homotopytypetheory.org/2014/03/03/hott-should-eat-itself/) computational type theory with native ω-categories which is still interpretable in an arbitrary ∞-topos. 
- [Bounded Inductive Construction Calculus](BICC): we are developing a finitistic core theory to use for proving desired metatheoretic properties, namely typechecking decidability, canonicity, normalization, and conservativity of HCCC over M. Shulman's ZMC/𝕊 and thus its relative consistency.

A sound theoretical foundation still needs to be put into shape. In a series of [short](kotlin_literate.pdf), [proposals](kotlin_academic.pdf) we develop a versatile syntax designed for excellent readability, conciseness, and typographic perfection. Based on Kotlin, Python, Agda, Lean, Scala, and Fortress, it's a culmination of over two decades of meticulous collection and evaluation of ideas, carefully assembled into a coherent system.

§ A proof language we'd enjoy using
-----------------------------------

Human readers understand implicit conversions immediately, forgive minor omissions, and think along with the author, so they are able to bridge nontrivial gaps and transform arguments "mutatis mutandis" once they grasp the idea. Proof formalization is plagued by the pain to elaborate all of this explicitly. An enjoyable proof language must at least address the issues of that kind with known solution approaches:
- Most frustrating are the type mismatch issues caused by obvious equalities that do not not hold computationally. Partial solutions:
   - The universe `SProp` of definitionally propositional types ([“Definitional proof-irrelevance without K”](https://dl.acm.org/doi/10.1145/3290316))
   - The universe `SData` of definitionally set-like types ([“Observational Equality meets CiC”](https://hal.science/hal-04535982v1))
   - Limited predicate subtyping ([“Predicate Subtyping with Proof Irrelevance”](https://arxiv.org/abs/2110.13704))
   - Equations on neutral terms ([“New Equations for Neutral Terms”](https://dl.acm.org/doi/10.1145/2502409.2502411)) and parallel reductions ([“The Taming of the Rew”](https://dl.acm.org/doi/10.1145/3434341))
   - Typechecking-driven automated equality proof synthesis
- The richness and flexibility of the type system lures into reinventing the wheel. Every library tends to use its own slightly different inventory of standard types and typeclasses, which massively hinders their interoperability. Partial solutions:
  - [Algebraic ornaments](https://arxiv.org/abs/1212.3806) and [Dependent Interoperability](https://dl.acm.org/doi/abs/10.1145/2103776.2103779)
  - Typeclass-based mechanism of contextual implicit coercions as in [Lean](https://lean-lang.org/functional_programming_in_lean/type-classes/coercion.html) and [Scala3](https://dotty.epfl.ch/docs/reference/contextual/conversions.html).
  - Fortress-style configurable inheritance for sound typeclass hierarchies.
  - Contextually configurable instance resulution and derivation.

§ HCCC as a programming language
--------------------------------

Computational type theories are functional programming languages capable of exhaustive internal reasoning about the programs' behavior. The ability to make use of classical termination proofs makes HCCC an exceptionally powerful total programming language. It's also capable of expressing general Turing-complete (and thus potentially diverging) computations and computations on exact real numbers since both the `Computation<T>`-monad and the datatype ℝ of Cauchy reals are available as quotient inductive-inductive types. In addition, the computational interpretation of ◇-modality is given by the recently introduced [Verse Calculus](https://simon.peytonjones.org/verse-calculus/), which adds the unparalleled expressiveness of deterministic functional logic programming.

HCCC seems to have everything you could ever want from a language for _non-interactive programming_, but as great as it sounds in theory, programming in bare-bones intensional type theories demands for frustrating amounts of explicit proofs of termination, productivity, and convertibility. For decent practical programming language, we additionally need indexed modalities for size-guarded recursion and clock-guarded corecursion, and a liquid type system.

Embracing interactive programming is a whole separate matter. While non-interactive programs deal only with data, interactive programs interact with the environment and deal with references in addition to values. We think that interactivity can be dealt with by introducing substructural object and reference variables and the substructural cousins of □/◇-modalities: the pure modality ⊡ and the live modality ⟐. Pure objects `x : ⊡X` are self-contained, they do not interact through any references, even those available in the context, see [Controlling purity in Kotlin](kotlin_purity.pdf). Live objects `x : ⟐X` may have captured references, i.e. they can interact through references not present in the context. Live object include those that may interact or have interacted with the outside world, so they have a spectrum of possible states rather then one fixed state, just like the formal variables in Verse calculus. Analogously to Verse, an object can interact with ⟐-objects becoming ⟐ itself (from the internal point of view, x will have a fixed state), but as opposed to Verse we don't have `one` and `all` operators, we can only extract value into the non-live context if we have a proof that the live object eventually converges to a unique determined state.

The extrinsic state of objects `x : X` can be described as an element of its trace monoid. When concurrency and interaction comes into play, we have to deal with incomplete information about the operational state of objects. instead of a fixed state, we have a set of possible states. Thus, the “state” of a live object `x : ⟐X` is a boolean combination of fixed states, given by an element of the respective trace algebra. For instance, if we start two coroutines in parallel, and these coroutines perform actions on the same object, its algebraic state is given by a sum of possible outcomes for all possible on orders of the actions performed on the object by these two coroutines. Objects such as heaps, where fresh mutable objects and arrays can be created, have very particular trace monoids generated by a partial commutative monoid of creation and substitution operators giving rise to the associated concurrent separation logic within the type theory.

We have not yet worked out the formal definition for the interactive extension of HCCC, but have developed [type system extension for Kotlin](kotlin_objects.pdf) that embraces effects, mutability, concurrency, and synchronization, while being intended to be translatable into the purported interactive HCCC.

Similar to the case of guarded (co)recursion modalities, the whole system will be reducible to plain HCCC by encoding objects as parametrized relative (co)monads and interpreting expressions involving reference types via do-notation (see [Paella: algebraic effects with parameters and their handlers](https://icfp24.sigplan.org/details/hope-2024-papers/7)).


§ What's missing?
-----------------

There are two major areas that are not yet covered:
- The [affine logic for biconstructive mathematics](https://arxiv.org/abs/1805.07518) on the reasoning side;
- Quantum algorithms and interacting quantum automata on the programming side;

The live modality ⟐ introduces the notion of objects with mixed states and interactions that makes such objects entangled (allowing only particular combinations of their respective states), which reminds of quantum mechanics. Trace algebras for heaps, which extrinsically describe states of objects inside the heap, can be defined in terms of their duals, the algebras of observables, which are commutative since observations are independent of each other. A non-commutative generalization, in which observations are no longer necessarily independent, would allow the description of quantum objects where the coexistence of multiple pure states is inherent rather than due to lack of knowledge. The non-commutative generalization of state creation and substitution algebras would allow to describe quantum arenas where separate objects can be entangled. There, the separately created objects generally do not remain separable objects, and the picture of arenas as collections of distinct objects becomes fuzzy. We can't reason in terms of "distinct particles" anymore, and have to reason in terms of "field quanta", with quantum arenas playing the role of quantum fields. We assume this analogy can be made precise, and will allow describing quantum computations and perhaps also non-discrete quantum processes in general and might shed new some light onto formalization of quantum field theory.

The affine logic for biconstructive mathematics seems an entirely distinct subject at first, but biconstructive propositions are semantically described as particularily simple Chu spaces, while the general form of which is known to also describe the Hilbert spaces of quantum states. It resonates with the situation in the homotopy type theory, where the propositions are particularily simple (truncated) types.
