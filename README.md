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
These developments have also led to a [variety of ideas for Kotlin](kotlin)
that greatly improve its expressiveness and conciseness, and most importantly 
enabling enforcing correctness-by-construction and verifiable contract programming — 
the only mainstreamable formal methods.

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
  with propositional resizing and sufficiently general notion of quotient inductive types to express universal
  Cauchy completions such as the real numbers ℝ and the Turing-complete partiality monad `Computation<T>`. 
- [□Parametric Polymorphism for Agnostic Type Theories](polymorphism):
  We add the parametric quantification `∀<X : T> Y` and
  the S4 necessity modality mapping each proper type `T` to the set `□T` of its closed-form inhabitants.
  This way, the theory acquires truly polymorphic type (`List<T>`), typeclass (`Monoid<T>`), 
  and instance (`id : ∀<T> T → T`) definitions and LEM-compatible (□-internal) parametric reasoning,
  so `{ x ↦ x }` can be shown to be the unique closed-form inhabitant of `∀<T> T → T`.
- [◇Classical Reasoning in Constructive Type Theories](verse):
  We add the S4 possibility modality mapping each proper type `T` to the spectrum `◇T` of its formal inhabitants
  to enable univalence-compatible (◇-internal) classical reasoning with choice
  without compromising favorable computational properties and decidability of proof and type checking. 
  The computational content of the ◇-modality turns out to be given by the
  [Verse calculus](https://simon.peytonjones.org/verse-calculus/), a recently developed deterministic approach to 
  functional logic programming.
  Incidentally, we also vastly expand of the computational power by allowing all classically provable algorithms.
- [Higher Categorical Type Theory](prototypes):
  We add types representing Reedy categories, presheaves on them, and functors between them,
  resulting in a [homoiconic](https://homotopytypetheory.org/2014/03/03/hott-should-eat-itself/)
  computational type theory with native ω-categories
  which is still interpretable in every elementary ∞-topos with enough inductive types.
- [Bounded Inductive Construction Calculus](BICC):
  We are developing a finitistic core theory to use for proving desired meta-theoretical properties,
  namely typechecking decidability, canonicity, normalization, and conservativity of HCCC over
  [M. Shulman’s ZMC/𝕊 set theory](https://arxiv.org/abs/0810.1279) and thus their equiconsistency.

§ Extensions for convenient reasoning
-------------------------------------

Human readers instantly recognize implicit conversions, forgive minor omissions, and think along with the author,
bridging nontrivial gaps and transforming arguments "mutatis mutandis".
Proof formalization is plagued by the pain to elaborate all of this explicitly.
An enjoyable proof language must at least address the issues of that kind with known solution approaches:
- Most frustrating are the type mismatch issues caused by obvious equalities that do not hold computationally.
 Partial solutions:
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

In a series of [short](kotlin/kotlin_literate.pdf) [proposals](kotlin/kotlin_academic.pdf) we develop a versatile syntax
for the resulting language
designed for excellent readability,
conciseness, and typographic perfection.
Based on Kotlin, Python, Lean, Agda, Scala, and Fortress,
it is a culmination of over two decades of meticulous collection and evaluation of ideas,
carefully assembled into a coherent system.


§ Extensions for convenient programming
---------------------------------------

Observational type theories can be seen as functional programming languages
that also contain an embedded language to reason about the programs’ behaviour.
Unambiguous specifications of language primitives are part of the language and
can be composed into formal proofs regarding any behaviorally relevant properties
of the programs.

The ability to make use of classical termination proofs makes HCCC an exceptionally powerful total programming language,
which is also capable of expressing not necessarily terminating Turing-complete computations and
exact computations over the reals ℝ. The ◇-modality adds the unparalleled expressiveness of deterministic functional
logic programming based on the recently introduced [Verse Calculus](https://simon.peytonjones.org/verse-calculus/).

HCCC seems to have everything one could ever want from a language for _non-interactive programming_.
Yet, as great as it sounds in theory,
programming in bare-bones intensional type theories demands for frustrating amounts of explicit termination,
productivity, and convertibility proofs.
A decent practical programming experience can only be achieved by automating them away via liquid types
and providing convenient infrastructure to deal with cases that cannot be automated:
indexed modalities for size-guarded recursion and [clock-guarded corecursion](https://arxiv.org/abs/1804.09098).

§ Embracing interactivity and concurrency
-----------------------------------------

Non-interactive programs deal only with data and are inherently deterministic, atemporal, and inconsequential:
it does not matter if one repeats a some part of the computation or performs it only once, it does not matter
if one performs an unnecessary part of the computation speculatively, it does not matter if the computation
is performed sequentially or concurrently.

Interactive programs interact with the environment, these interactions are partially ordered in time and are in general
non-deterministic both due to order unpredictability
```kotlin
for (i in 1..3) {
    launch { user.say(i) }
}
```
and due to the environment unpredictability
```kotlin
val n = user.ask<Int>("Enter any integer number: ")
```

We think that interactivity can be dealt with by introducing 
- substructural reference-valued variables,
- opaque existential quantification over them to construct types with limited lifetimes, and
- the reference-level cousins of □/◇-modalities: the pure modality ⊡ and the live modality ⟐.

Interaction only happens through references, and in general changes their typestates,
which makes interactions partially ordered and limited according to the typestate
transition and subsumption diagram of the respective reference, which plays the role of
the type for references.
We obtain references can be usable at most once (affine), at least once (relevant), and
exactly once (linear) as the elementary special cases.

By specifying an implementation for a typestate diagram, we construct an object and get
a fresh reference to it.
In general, objects may construct and use other objects inside
and/or capture external references.

Pure objects `x : ⊡X` are self-contained;
they do not make use of any external references, even those available in the context,
see [Controlling purity in Kotlin](kotlin/kotlin_purity.pdf).

Sometimes the straightforward, correct-by-construction implementation of a non-interactive
function is best described as an imperative algorithm `f : ⊡(X => Y)`.
Internally, it can create mutable objects and act on them, even in a concurrently non-deterministic way, and
make use of effects (such as throwing exceptions) as long as they are encapsulated
(caught inside, in case of exceptions).
Liquid types facilitate entirely automated verification that the algorithm always terminates with a definite value
in most cases of interest, so the self-contained imperative implementation can be used as a genuine function
`f : X -> Y`.
This way, interactive extension of HCCC helps even for non-interactive programming.

Live objects `x : ⟐X` may have captured references, i.e.
they can interact through references not present in the context.
Being objects that may interact or have interacted
with the outside world, they have a spectrum of possible states rather than one fixed state,
just like the formal variables in Verse calculus.
Interaction with live objects can be formalized in analogously to functional logic programming,
albeit without `one : ◇◇T -> ◇T` and `all : ◇T -> Stream<T>` operators.

Adjunction between ⊡ and ⟐ modalities is given by the box and unbox operations of [Capture Calculus
CC<sub><:□</sub> by M. Odersky et al](https://arxiv.org/abs/2207.03402).
This calculus also allows introducing temporarily borrowed and temporarily locked references, which
can be captured inside objects of limited lifetime we introduce using reference-level existential quantification.
This mechanism enables structured sharing and structured concurrency.

We have not yet worked out the formal definition for the interactive extension of HCCC, but we have developed
[type system extension for Kotlin](kotlin/kotlin_objects.pdf) that embraces effects, mutability, concurrency,
and synchronization on the practical level.
It should also make Kotlin amenable to automated verification.

Similar to the [case of guarded (co)recursion modalities](https://bentnib.org/productive.pdf),
the whole system will be reducible to plain HCCC by encoding objects as parametrized relative
(co)monads and interpreting expressions involving reference types via do-notation.
See
[Paella: algebraic effects with parameters and their handlers](https://icfp24.sigplan.org/details/hope-2024-papers/7).

§ Logic of interaction
----------------------

Assume that every time one interacts with a self-contained object `x : ⊡X` by calling `x.doSomething(params)`,
the action name, parameters, and outcome are saved into a log.
Such logs form a monoid under concatenation, the free monoid of `X`-histories generated by atomic entries
`action(params) ↦ outcome`.
Now let us consider histories equivalent if they lead to observationally indistinguishable states of `x`.
The quotient monoid generated by this equivalence is known as the trace monoid of `X`. 
From extensional point of view, state of an object `x : X` is given by an element of its trace monoid.

(In general, some actions may add or remove actions available afterwards, making trace monoid into a
category with objects given by typestates of the object.)

When concurrency and interaction come into play,
we have to deal with incomplete information about the object states.
Instead of a fixed state, we have a set of possible states.
Thus, the state of a live object `x : ⟐X` is a boolean combination of fixed states,
given by an element of the respective trace algebra.

```kotlin
user.say("Hi!")
for (i in 1..2) {
    launch { user.say(i) }
}
user.say("Bye!")

// user = say("Hi"!) ; (user.say(1) | user.say(2)) ; user.say("Bye!")
//      = say("Hi"!) ; user.say(1) ; user.say("Bye!") | say("Hi"!) ; user.say(2) ; user.say("Bye!")
```

```kotlin
val n = user.ask<Int>("Enter any integer number: ")

// user = (ask<Int>("Enter any integer number: ") ↣  0)
//      | (ask<Int>("Enter any integer number: ") ↣  1)
//      | (ask<Int>("Enter any integer number: ") ↣ -1)
//      | (ask<Int>("Enter any integer number: ") ↣  2)
//      | (ask<Int>("Enter any integer number: ") ↣ -2)
//      | (ask<Int>("Enter any integer number: ") ↣  3)
//      | ···
```

Objects such as heaps, where fresh objects can be created,
have very particular trace monoids generated by creation operators:
```kotlin
val r1 = heap.new<Int>(1)
val r2 = heap.new<Int>(2)
r1.set(3)

// heap = (new(1) ↣ r1) ; (new(2) ↣ r2) ; r1.set(3)
//      = (new(2) ↣ r1) ; (new(2) ↣ r2)
```

If we consider value substitution operators such as `r1.set(3)`,
we have to consider a trace category instead of a trace monoid
since this substitution operator is only available after `r1` is created.
But setting the `r1` to `3` has the same effect as if it were originally initialized by `3`,
so it is effectively sufficient to consider a trace monoid.

It is customary to write creation operators `(new(1) ↣ r1)` as `r1 ↦ 1` and write
(*) instead of (;) when the actions commute, so the final state of the heap can be written
as `(r1 ↦ 3) * (r2 ↦ 2)`.

Above posed that object types are described by typestate transition and subsumption diagrams,
which in particular contain actions with their signatures as transitions.
Typestate transition and subsumption diagrams generate the respective free trace algebroids.

In the case of heap-like objects (also including coroutine scopes), we have indexed families of typestates.
In particular, for heaps, the typestate is indexed by the number and types of allocated
variables.
Object may (and should) additionally contain equational laws for their trace
algebroids, such as the commutativity of creation operators and absorption of substitutions:
```
contracts {
  { val x = new(a) ; x.set(b) } ≡ { val x = new(b) }
  { val x = new(a) ; val y = new(b) } ≡ { val y = new(b) ; val x = new(n) }
}
```

This way, types of heap-like objects give rise to the associated concurrent separation logic
within the type theory.

We suspect that reference-level counterparts of indexed guarded computation modalities would give
rise to causal temporal logic allowing internal conceptualization of such notions as consensus 
fairness and eventual consistency.

§ The Missing Part
------------------

There are two major areas that are not yet covered:
- The [affine logic for biconstructive mathematics](https://arxiv.org/abs/1805.07518) on the reasoning side;
- Quantum algorithms and interacting quantum automata on the programming side;

The live modality ⟐ introduces the notion of objects with mixed states.
Interactions make such objects entangled,
restricting their joint state spectra to particular combinations of their respective states,
which reminds of quantum mechanics.
Trace algebras for heaps remind of algebras of [observables in physics](https://en.wikipedia.org/wiki/Observable).
In the case of heaps, they are commutative since observations are non-destructive and independent of each other.
Its non-commutative generalization describes the case where observations are no longer necessarily independent
and cannot be in general made non-destructive.
It allows description of quantum objects
where the coexistence of multiple pure states is inherent rather than due to lack of knowledge.
Non-commutative state creation operators algebras allow
describing quantum heaps where separate objects can be entangled.
There, separately created objects do not remain separable,
and the picture of heaps as collections of distinct objects becomes fuzzy:
instead of "distinct particles", we deal with "field quanta", with quantum heaps playing the role of quantum fields.
We assume this analogy can be [made precise](https://ncatlab.org/nlab/show/quantum+circuits+via+dependent+linear+types) 
and will allow describing quantum computations and perhaps also non-discrete quantum processes in general
and might shed new some light onto formalization of quantum field theory.

The affine logic for biconstructive mathematics seems an entirely distinct subject at first.
However, biconstructive propositions are semantically described as particularly simple Chu spaces,
while the general form of which is known to also describe the Hilbert spaces of quantum states.
It resonates with the situation in the homotopy type theory,
where the propositions are particularly simple (truncated) types.
