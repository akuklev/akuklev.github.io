Towards Higher Categorical Construction Calculus
================================================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com), [JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)


Almost a decade ago, the co-founder and former CEO of JetBrains Sergey Dmitriev told me about his
long-standing ambition to establish a database of mathematical results, definitions, conjectures,
constructions, and proofs. This database should allow content-based search and connect related
results into a web. Ideally, it should also connect results on mathematical objects of similar
structure even if their relatedness is not apparent and unknown to the respective authors.
Independently, related ideas got traction inside the mathematical community over the last years,
as exemplified by the [Formal Abstracts Project](https://formalabstracts.github.io/) by Thomas C. Hales.

The prerequisite for such a database is a common formalized language for mathematics, which has to be
syntactically appealing, comfourtable to work with and most importantly expressive enough to satisfy
the needs of mathematicians. We made a substantial progress towards this goals by meticulously piecing
together existing ideas, and also by developing original ones.

§ The HCCC Project
------------------

Over almost a decade at JetBrains Research, I've been intensely working on expressivity the
foundational systems underlying modern proof assistants, and came to a vision of what we call
Higher Categorical Construction Calculus.

On the reasoning side, HCCC is a natural deduction calculus capable of classical reasoning with
choice, abstractness-aware reasoning, structural induction over its own language, and (higher)
categorical reasoning.

On the other side, HCCC is a construction calculus capable of expressing canonical objects,
structures, and algorithmic constructions involving them. Expressable canonical objects include
datatypes of integers, reals, formalized languages of any complexity, and datatypes of their
respective expressions, while expressable structures include the ones defined by arbitrary
axiomatic theories in any signature, i.e. a formalized language of underlying expressions. 

Those structures (models of axiomatic theories) come conviniently prepackaged into parametrized
higher categories together with structure-respecting correpsondences between them, expressing
equivalence (one-to-one correspondences), relatedness (many-to-many correspondences), and
homomorphism  many-to-one correspondences), and also correspondences between correspondences
themselves, so that proofs and constructions can be specialized, generalized, and transferred
along those correspondences. In fact, the theories themselves also come packed into categories,
considering theories that generate equivalent classes of models as equivalent (Morita-equivalence),
and taking relative interpretability of theories as homomorphisms. Moreover, the higher categories
also form a parametrized higher category, and parametrized higher categories form a parametrized
parametrized categories and so on, while all constructions and proofs about higher categories
(and any other theories) are also automatically applicable to their parametrized versions.

In the first paper we outline extending Martin-Löf Type Theories by types representing 
inductively-defined synthetic categories, and functors on those. When applied to the Higher
Observational Type Theory by Shulman et al., we would pressumably obtain a Higher Categorical
Type Theory, featuring native ω-categories and capability to express its own syntax as an
inductive datatype, but still interpretable in an arbitrary ∞-topos.

In [“◇Classical and □Parametric Modalities for Martin-Löf Type Theories”](modalities.md) we
outline extending MLTTs by a dual pair of modalities enabling both abstractness-aware and
classical reasoning with choice, and also hugely expanding available algorithmic constructions
by enabling all classically provable algorithms, without compromising its favorable computational 
properties and decidability of typechecking. The modalities also allow convinient introduction
of impredicative universe of propositions and reflective Mahlo universes of types yielding a
type-theoretic counterpart of M. Shulman's “Set theory for category theory” ZMC/𝕊, and making the
underlying type theory excellently suitable for performing large constructions widely used in
(higher) algebraic geometry. We obtain HCCC by applying these extensions to HCTT.

## Practical aspects

While the aforementioned features make the purposed system an optimal for a proof assistaint,
it does not automatically make such a proof assistaint a viable alternative to hand-written proofs.
We need a pleasent and concise syntax, and a lot of additional mechanisms that minimize the formalization
pain: reduction of neutral terms and applications non-determinstic confluent reduction rules, support for
algebraic ornaments together with versatile subtyping, highly configurable implicit conversions, resolution
and derivation of implicit arguments, type inference, and proof inference (including but not limited to SMT
solvers and specialized solvers). In [Literate Kotlin series](litkot.md) we propose a versatile syntax based
on Kotlin, Python, Scala3, Lean, and Agda simultaneously, and propose some machinery related to subtyping
and inference. The rest is a work in progress that probably only can really start after an initial
implementation of HCCC is available.

## As a non-interactive programming language

While not very relevant for mathematal applications, MLTTs are at the same time total functional
programming languages. For for practical usability as a functional programming language, HCCC has
to be extended with indexed modalities for size-guarded recursion and clock-guarded corecursion,
which are known to be eliminable towards of ordinary recursion and corecursion at cost of substantial
complexity blowup. Speaking of expressivity, the ◇ and □ modalities greatly enhance expressivity of
the underlying theory taken as a programming language. While MLTTs can be understood as total functional
programming language, adding modalities makes it into a functional logic programming language.

# Future Work

## Embracing Interactive programming

To embrace interactive programming, we'll need to introduce substructural types for
non-discardable/non-sharable objects, and the substructural cousins of the ◇- and □-modalities:
`interactive` and `pure`, the `interactive` being closely related to `suspend`-modality of Kotlin
coroutines. We'll have to develop notions of (captured or standalone) objects, references and capabilities,
the linear, cartesian, and opaque variables related to the same entity. We'll understand Kotlinesque
structured concurrency and Rustacean structured (lifetime-based) ownership-management as instances
of structured ressource management, where managed shared objects are understood as addressable parts
of the state of their respective arena, which can be either an addressable part of an enclosing arena
a captured/standalone object in its own right. We'll show how objects and arenas can be defined as
in terms of algebraic effects/algebraic effects with parameters, and how the description of states of
those objects in terms of trace rigs (concurrent generalization of trace monoids) gives rise to separation
logic embedded into the substructural part of the type theory.

The theory should be desugarable into the plain HCCC by encoding objects etc. as paramatrized relative
(co)monads and interpreting expressions involving substructural types via do-notation.

This way we'll also obtain the ultimate type system for concurrent interactive programming possibly
making Kotlin the first general purpose programming language thoroughly susceptable to internal reasoning.

## Embracing biconstructive proofs
We'll discuss that in presence of affine types, we also have room for biconstructive propositions and proofs,
as presented in [“Affine logic for constructive mathematics” (M. Shulman)](https://arxiv.org/abs/1805.07518).

## Quantum computation, quantum systems, and quantum logic
We'll make conjecture how simultaneous interactions and entanglement (in the sense of Verse Calculus/◇-modality)
allows to include a quantum programming (programming only executable on a quantum computer) into our formalism.

The types `ᴿ◇T` of possible inhabitants of substructural types `T` can be probably understood as spectra over the
generalized rings R (algebras over the sphere spectrum, with 𝔽₁ being the initial generalized ring), connections
to absolute geometry (Connes) and to the type theory of parametrized spectra should be studied.

We'll discuss how arenas allow describing interactive/interacting quantum systems and quantum fields, how the
respective trace rigs turn into C*-algebras of those systems/fields, and how the combination of the separation
logic generated by those C*-algebras and the notion of biconstructive proofs could shed some light on the
nature of quantum reality.

## Dialectica type theory: A size-graded type theory with internal ∂

It should be possible to develop a resource-aware (hopefully non-Gödelian) variant of non-interactive HCCC,
where only size-non-increasing functions on sized types can be shown to exist unconditionally. All the other
functions can be only shown to exist conditionally on the availability of enough “computational budget”, with
their derivatives (computed by an internal Dialectica translation ∂) describing how much computational budged they
need for arguments of given size.

It might turn out to be possible to provide a translation of this type theory into the self-verifying
Pakhomov set theory. It might be possible to provide an understanding of this type theory as a type theory
of Diophantine equations.
