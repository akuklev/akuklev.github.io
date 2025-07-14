◇Classical Reasoning in Constructive Type Theories
==================================================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com), [JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)

# Overview

In 2016 C. McBride [introduced](https://link.springer.com/chapter/10.1007/978-3-319-30936-1_12) graded type theories with exact control over the number of computationally relevant argument usages. Original version used three modes, but can be extended to the following five:
```
x : X -- as often as desired
x :⁻X -- use at most once
x :¹X -- use exactly most once
x :⁺X -- use at least once
x :⁰X -- virtual argument, use only in type annotations
```

In intutionistic type theories, negation `¬T` is encoded as the function type `T → ⊥`. A proof that requires an assumption `nT : ¬T` can employ
this assumption to cut excluded cases when performing case analysis. For instance, a value `v : P + T` can be matched by `{ inl(p) ↦ ... ; inr(t) ↦ nT(t) }`.
Due to ex-falso-quodlibet (the recursion operator of the empty type ⊥), the excluded branch `nT(t)` can typecheck against any type.

Proofs by contradiction assume a negative premise `nT : ¬T` to derive a contradiction `⊥`. One way to arrive at a contradiction is to construct a counter-example `t : T` and feed it into `nT(t)` thus yielding a contradiction. In general, a proof can require multiple negative premises, and use only one of them, so it is not guaranteed that every negative premise is used. On the other hand, such a premise can be used inside an internal recursive subproof to cut branches, so it can be used unbounded number of times. However, if we require such a premise to be used exactly once, we can extract a counterexample from a proof by contradiction:
```
 prf : ¬(nT :¹¬T)
——————————————————
   εᵀ(prf) : T
```

Otherwise, the extraction will be non-determinstic. However, we can introduce modalities of spectra ◇⁺, ◇⁻ and ◇, meaning “one or more possible outcome”, ”one or less outcomes” and “any number of possible outcomes”. With this modalities we have:
```
 prf : ¬(nT :⁺¬T)      prf : ¬(nT :⁻¬T)        prf : ¬¬T
——————————————————    ——————————————————    ——————————————
  εᵀ(prf) : ◇⁺T         εᵀ(prf) : ◇⁻T        εᵀ(prf) : ◇T
```

For the rest of this paper will not consider the substructural modes (⁻, ¹, ⁺) and modal operators (◇⁺, ◇⁻), and only consider the truly remarkable third rule above. It's the classical choice operator, which means we can presummably use classical reasoning (with excluded middle and choice) under the ◇-modality!  `◇T` is the type of hypothetically possible inhabitants of `T`, yet will argue that it has a sound computational^[Versal functions only compute on introspectable (closed-form) arguments, they cannot be applied to an “external function” (which can be applied to any value, but not introspected) nor an arbitrary (Cauchy) real number. This is in strong opposition to the total functions outside ◇-modality which are guaranteed to compute also on external entities. Verse calculus seems to provide a Krivine-type realizability interpretation for classical logic with choice, while general MLTT provide stronger Kreisel-type realizability for intuitionistic logic.] interpretation in terms of the Verse Calculus recently introduced by S. Peyton Jones et al. We will also introduce the dual types `□T` of “manifestly neccesary” inhabitants of `T`, i.e. finite closed terms, yielding the well-known computational interpretation in terms of staged computability. Dually to classical reasoning under ◇-modality, we obtain parametric reasoning under □-modality, so that we can show that `{ x ↦ x }` in the only canonical endomorphism of an arbitrary type up to equivalence: `∀(id : □∀(T : *) T → T) id ≃ { x ↦ x }`, see the [companion paper](/polymorphism)

By establishing a set-theoretic interpretation of types under ◇-modality, we will show admissibility of the computational Markov principle allowing to evaluate (potentially diverging by virtue of halting problem) computations given a finite closed classical proof of their non-divergence: 
```
 c : Computation<T>   nonDivergence : □◇(c ≠ ⊥)
—————————————————————————————————————————————————
          eval(c, nonDivergence) : T
```

We will show that even in presence computational of Markov principle, all closed-form functions `f : □(X → Y)` are continuous with respect to the topology given by positively semi-decidable predicates which is also the usual open-ball topology for all types constructed as Cauchy completions, and the sets of closed-form inhabitants of types with positively semi-decidable equality are formally subcountable: Check if we can show that types with verifiable equality are formally subcountable: `∀<T : *> verifiable(T) → ◇(ℕ ⇀ □T)`   
**TODO**: Check if we can also show that types with falsifiable equality are formally completely separable.

# The spectral modality ◇ and perceived entanglement

# Spectral quantifiers and canonical quantifiers

# The Markov principle

# Unary parametricity

# Interpreting classical logic

# Interpreting verse calculus

Verse calculus is a functional logic programming language, which implies that a finite closed “program” can be evaluated:
```
         prgm : □◇P
————————————————————————————————
 all(prgm) : PolyComputation P
```

Where PolyComputation is a monad similar to the Computation monad, but allowing to yield multiple, potentially infinutely many values, a computational stream modulo order and multiplicity of values.

This is the “all” operator of Verse Calculus, while εᵀ gives “one” operator.

# Embedding of the type-theoretic model of ZF-sets into ◇ by Zakharyaschev subframe canonical formulae

# Set-theoretic model a la Pujet-Tabareau and conservativity via back-and-fourth argument

# Normalization for the modal-free fragment and admissibility of Markov principle

# Future work: Canonicity for the □-fragment, productivity for the ◇-fragment

The former means that the “stream” `all(prgm : □◇P)` is productive and dense in the spectrum `◇P` with respect to the topology given by positively semi-decidable predicates.
