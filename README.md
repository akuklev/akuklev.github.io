Esquisse d'un Programme
=======================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com), [JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)

At JetBrains, we create the most effective, convenient, and pleasurable tools for engineers and researchers, allowing their the natural drive to develop to thrive and bear fruit. We dare to pursue ambitious visionary ideas. We wanted to use a programming language we'd enjoy using, so we created one, and now Kotlin is the language of choice for millions of software developers worldwide.

We want to make Kotlin fully amenable for certified programming, and we want a proof language and toolset we'd enjoy using. We believe that the best proof language for certified programming should be a general-purpose language suitable for stating results, definitions, conjectures, constructions, and proofs in all mainstream areas of mathematics and computer science. After 25 years of active research, aided by a number of breakthroughs sprouting from the Univalent Foundations Program, we finally have a blueprint for such a language, which we'll present below.

§ Overview
----------

The Higher Categorical Construction Calculus (HCCC) is a powerful univalent computational type theory. As a proof calculus, it is capable of classical reasoning with choice, abstractness-aware (“parametric”) reasoning, structural induction over its own language, and higher categorical reasoning. It enjoys decidable proof checking and can be shown consistent relative to a strong form of classical set theory.

We call it a _construction calculus_, because, besides proofs, it can express canonical objects, structures, and algorithmic constructions involving them. Expressable canonical objects include the basic numerical datatypes such as (unbounded) integers, (Cauchy) reals, (pure) functions between and subsets of other expressable datatypes, and also datatypes of expressions for arbitrary formalized languages, allowing to provide interpretations using structural recursion and perform proofs by structural induction. Expressable structures include those defined by arbitrary^[axiomatic theories are not limited to first-order logic, so HOCC assumes an impredicative universe of all propositions which is the distinctive feature the original Calculus of Constructions and its successors.] axiomatic theories in any formalized language, including category-like theories that exhibit higher-order homomorphisms, e.g. natural transformation between functors.

We call it _higher categorical_, because instances of these structures, i.a. models of axiomatic theories, come conveniently prepackaged in displayed ω-categories, together with structure-respecting correpsondences, expressing equivalence (one-to-one correspondences), relatedness (many-to-many correspondences), and homomorphisms (many-to-one correspondences) on every level, so that all proofs and constructions can be specialized, generalized, and transferred along these correspondences. Proofs and constructions also transfer outwards, i.e., all constructions and proofs about ω-categories and any other theories also apply to their displayed versions, which is crucial since models of an axiomatic theory, including ω-categories themselves, form a displayed higher category, and displayed ω-categories form a displayed displayed ω-category, and so on.

- The starting point of HCCC is the third-generation univalent type theory [HOTT currently being developed by Shulman et al.](https://ncatlab.org/nlab/show/higher+observational+type+theory) 
- In [Higher Categorical Type Theory](reedy-types) we propose to add types representing Reedy categories, presheaves on them and functors between them, resulting in a [homoiconic](https://homotopytypetheory.org/2014/03/03/hott-should-eat-itself/) computational type theory with native ω-categories which is still interpretable in an arbitrary ∞-topos. 
- In [“◇Classical and □Parametric Modalities for Martin-Löf Type Theories”](modalities) we propose to add S4 modal operators □ of neccesity and ◇ possibility on types, mapping each proper type `T` to the modal type `□T` of its finite closed expressions and the modal type `◇T` of its formally existent inhabitants. With these modalities we can enjoy the following without compromising favorable computational properties and decidability of proof/type checking:
  - Classical reasoning with choice under the ◇ modality;
  - Parametric quantifiers `∀<X : T> Y` that only allow using the parameter `X` in type annotations;
  - Abstractness-aware “parametric“ reasoning under the □ modality, for instance a proof that `∀(f : □∀<T> T → T) f(x) = x`;
  - A vast expansion of the computational power by allowing all classically provable algorithms;
  - Reflective universes, resulting in a type-theoretic counterpart of M. Shulman's “Set theory for category theory” ZMC/𝕊, and making the underlying type theory eminently suitable for performing constructions widely used in modern algebraic geometry.

A sound theoretical foundation still needs to be put into shape. In a series of short proposals ([Literate Kotlin](kotlin_literate.pdf), [Declarative Kotlin](kotlin_declarative.pdf), [Academic Kotlin](kotlin_academic.pdf), a few pages each) we develop a versatile syntax designed for excellent readability, conciseness, and typographic perfection. It is based on Kotlin, Python, Agda, and Lean, with elements of Scala and Fortress. 
It's the culmination of over two decades of meticulous collection and evaluation of ideas, carefully assembled into a coherent system.

§ A proof language we'd enjoy using? A long way to go...
--------------------------------------------------------

Human readers understand implicit conversions immediately, forgive minor omissions, and think along with the author, so they are able to bridge nontrivial gaps and transform arguments "mutatis mutandis" once they grasp the idea. Any attempt at formalization is plagued by the pain to elaborate all of this explicitly.

To start with, known issues with known solution approaches have to be addressed:
- Most frustrating are the faulty type mismatch errors caused by obvious equalities and subsumptions not holding computationally. Every available solution approach should be taken into account: parallel reductions ([“The Taming of the Rew”](https://dl.acm.org/doi/10.1145/3434341)) and equations on neutral terms ([“New Equations for Neutral Terms”](https://dl.acm.org/doi/10.1145/2502409.2502411)), coercions along observational equality ([“Observational Equality meets CiC”](https://hal.science/hal-04535982v1)), the universe of explicitly propositional types ([“Definitional proof-irrelevance without K”](https://dl.acm.org/doi/10.1145/3290316)), limited predicate subtyping ([“Predicate Subtyping with Proof Irrelevance”](https://arxiv.org/abs/2110.13704)), and maybe also automated proof synthesis.
- The richness and flexibility of the type system lures into reinventing the wheel. Every library tends to use its own slightly different inventory of standard types and typeclasses, which massively hinders their interoperability. Luckily, this issue be addressed systematically by [algebraic ornaments](https://arxiv.org/abs/1212.3806) and [Dependent Interoperability](https://dl.acm.org/doi/abs/10.1145/2103776.2103779) in connection with a typeclass-based mechanism of contextual implicit coercions as in [Lean](https://lean-lang.org/functional_programming_in_lean/type-classes/coercion.html) and [Scala3](https://dotty.epfl.ch/docs/reference/contextual/conversions.html). Besides that, we need Fortress-style configurable inheritance for sound typeclass hierarchies, and a contextually configurable mechanism of instance resulution and derivation.
- Many other cases of excessive verbosity can be addressed with [liquid types](https://dl.acm.org/doi/10.1145/3632912), as well custom solvers and tactics, including the ones handling identification along canonical isomorphisms, elaboration of ”without loss of generality” and "mutatis mutandis" arguments, separation of “general position” arguments and corner case handling.

§ HCCC as a programming language
--------------------------------

Computational type theories are functional programming languages capable of exhaustive internal reasoning about the programs' behavior. The ability to make use of classical termination proofs makes HCCC an exceptionally powerful total programming language. It's also capable of expressing general Turing-complete (and thus potentially diverging) computations and computations on exact real numbers since both the `Computation<T>`-monad and the datatype ℝ of Cauchy reals are available as quotient inductive-inductive types. In addition, the computational interpretation of ◇-modality is given by the recently introduced [Verse Calculus](https://simon.peytonjones.org/verse-calculus/), which adds the unparalleled expressiveness of deterministic functional logic programming. HCCC seems to have everything you could ever want from a language for _non-interactive programming_, but as great as it sounds in theory, programming in bare-bones intensional type theories demands for frustrating amounts of explicit proofs of termination, productivity, and convertibility. 

To make a decent practical programming language, HCCC would need indexed modalities for size-guarded recursion and clock-guarded corecursion, and SMT solver-based system of liquid types.

§ Embracing interactive programming
-----------------------------------

Non-interactive programs deal only with data. Interactive programs interact with the environment and deal with references in addition to values. References point to some kind of location or object in the environment, and all interactions involve one or more references. To deal with references, the notion of expression contexts must be generalized: in addition to available variables and their types, they must track available references and their types. The types of references can depend on other values as well as on other references from the context, for example we can have such a context:
```
T : Type, size : Nat, h : Heap, r : h.MutableArray<T>(size)
```
Here both `h` and `r` are references, and the type of `r` depends on the type `T`, the value `size` and the reference `h`. The dependency of a reference type on another reference `h` signalizes that the referenced object exists inside the object referenced by `h` (the mutable array `r` is an entity inside the heap `h` in our case) and guarantees that these references can never escape the scope in which their parent objects are available. 

References can be annotated as singular and/or unique, see [Linearity and Uniqueness: An Entente Cordiale](https://granule-project.github.io/papers/esop22-paper.pdf). The "singular" annotation prohibits the creation of secondary references, while the "unique" annotation guarantees that no secondary references have been previously created outside. References can also be annotated as mandatory and/or disposing. The “mandatory” ones have to be explicitly consumed, while “disposing” references are guaranteed to be eventually consumed outside. These are crucial for suspended coroutines (which must eventually be resumed) and blocking resource handles (which must be eventually disposed).

The bifurcation of contexts into the value and reference parts, introduces reference-level cousins of ◇/□-modalities. The usual □-modality describes finite closed expressions which can also be understood as compile-time constants (written “const” in Kotlin). It's cousin is the `pure` modality: pure expressions are those that do not use references, even if they are available in the context. Its dual is the `live` modality, which contains expressions that might have captured references, i.e. they can make use of references not present in the context. References captured as typal parameters are known as capabilities, and essentially reproduce the [Capture Checking mechanism recently proposed for Scala3](https://docs.scala-lang.org/scala3/reference/experimental/cc.html). The `live` modality is closely related to coroutines in Kotlin. In fact, if we only allow reactive (coroutine-based) IO and interactions with external shared mutable objects, Kotlin's `suspend (Xs)-> Y` would translate exactly to (Xs)→ (live Y).

Dependent reference types and the `live` modality that allows references to be captured = structured resource management, a robust joint generalization of Rust's structured ownership and Kotlin's structured concurrency.

On the other hand, interactivity can be incapsulated: for example, a pure function can create an instance `h` of a persistent data structure that emulates a mutable heap, and execute a non-pure imperative program that requires a heap against `h`, while still being pure from the outside. The same surely applies to exceptions and algebraic effects in general: as long as we handle all exceptions/effects, we're pure from the outside. Similar to the case of guarded (co)recursion modalities, the whole system is reducible to plain HCCC by encoding objects as parametrized relative (co)monads and interpreting expressions involving reference types via do-notation (see [Paella: algebraic effects with parameters and their handlers](https://icfp24.sigplan.org/details/hope-2024-papers/7)).

§ Emergent separation logic
---------------------------

So far, we have only described a sound type system for interactive programs themselves, but have not addressed how to achieve exhaustive internal reasoning about the behavior of interactive programs.

The extrinsic state of objects can be described in terms of trace monoids. When concurrency comes into play, we have to deal with incomplete information about the operational state of objects: instead of a fixed state, we have a set of possible states. Thus, for the purpose of reasoning, the state of an object is described by an element of a trace algebra, a unital associative algebra, the Boolean rig, which takes on the role of the trace monoid in the concurrent setting. If we start two coroutines in parallel, and these coroutines perform actions on the same object, its algebraic state is given by a sum of possible outcomes for all possible on orders of the actions performed on the object by these two coroutines.

Object arenas such as heaps, where fresh mutable objects and arrays can be created, and coroutine contexts where jobs can be launched, and clusters where interacting actors can be spawned, have very particular trace monoids generated by a partial commutative monoid of creation and substitution operators for objective and ghost states giving rise to the associated concurrent separation logic within the type theory.

The resulting system would embrace mutability, concurrency and interactive programming in their in their entirety, and thus can be used
as a foundation for the aspired Certified Kotlin.

§ What's missing?
-----------------

There are two major areas that are not yet covered:
- The [affine logic for constructive mathematics](https://arxiv.org/abs/1805.07518) on the reasoning side;
- Quantum algorithms and interacting quantum automata on the programming side;

Trace algebras, which extrinsically describe states of objects, can be defined in terms of their duals, the algebras of observables, which are commutative since observations are independent of each other. A non-commutative generalization, in which observations are no longer necessarily independent, would allow the description of quantum objects where the coexistence of multiple pure states is inherent rather than due to lack of knowledge. The non-commutative generalization of state creation and substitution algebras would allow to describe quantum arenas where separate objects can be entangled. There, the separately created objects generally do not remain separable objects, and the picture of arenas as collections of distinct objects becomes fuzzy. We can't reason in terms of "distinct particles" anymore, and have to reason in terms of "field quanta", with quantum arenas being the quantum fields.

Remarkably, the affine logic for constructive mathematics mentioned above sees propositions as truncated Chu spaces, the general form of which is known to also describe the Hilbert spaces of quantum states. It resonates with the situation in the homotopy type theory, where the propositions are truncated types, while the types in general are the homotopy types (= weak ∞-groupoids = anima).
