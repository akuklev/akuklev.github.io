# Overview

In 2016 C. McBride [introduced](https://link.springer.com/chapter/10.1007/978-3-319-30936-1_12)
graded type theories with exact control over the multiplicity of computational argument usages.
In particular, it is possible to have the following multiplicity modes:
```
x : X -- as often as desired
x :⁻X -- use at most once
x :¹X -- use exactly most once
x :⁺X -- use at least once
x :°X -- opaque argument, use only in type annotations
```

As we have shown in “[□Parametric Polymorphism for Agnostic Type Theories](polymorphism)”, the opaque mode (`:°`) 
allows introducing the □-modality mapping types `T` to their sets of closed-form inhabitants `t : □T`.
It is also possible to define its dual ◇-modality that maps types to `T` to spectra `◇T` (see below)
of their formally possible inhabitants.

When “constructing” a formal inhabitant, we may use the principle `ε : (¬¬T) → T` that allows that states
that everything which is not forbidden is possible:
```
  Γ, ε : ∀<T> (¬¬T) → |T| ⊢ prf : P
————————————————————————————————————
          Γ ⊢ prf : ◇P
```

With ε is both double negation elimination for propositional types `T` and axiom of choice for the
non-propositional ones^[To remain consistent with univalence under the ◇-modality,
`ε` should only be applicable to types satisfying uniqueness of identity proofs propositionally,
i.e. set-like types.]. 
It allows harnessing the full power of classical (non-constructive) reasoning within ◇-fragment
without compromising computational properties of the underlying type theory such as canonicity,
normalization and decidability of type checking, as well as its compatibility with univalence.

In fact, we can even use non-constructive proofs to enhance the computational strength of the
underlying theory by postulating computational Markov Principle (CMP) that allows evaluating
Turing-complete computations given a closed-form classical proof of their non-divergence:
```
 c : Computation<T>   nonDivergence : □◇(c ≠ ⊥)
————————————————————————————————————————————————————
          eval(c, nonDivergence) : T
```


# Extracting counter-examples

In intuitionistic type theories, negation `¬T` is encoded as the function type `T → Void`.
A proof that requires an assumption `nT : ¬T` can employ this
assumption to cut excluded cases when performing case analysis.
For instance, a value `v : P + T` can be matched by `{ inl(p) ↦ ... ; inr(t) ↦ nT(t) }`.
Using the ex-falso-quodlibet rule (the recursion operator of the empty type `Void`),
the excluded branch `nT(t)` can typecheck against any type.

Proofs by contradiction `prf : ¬T → Void`assume a negative premise `nT : ¬T` to derive a contradiction,
i.e. an expression of the empty type `Void`.
To arrive at a contradiction, one can construct a counter-example `t : T` and feed it into `nT(t) : Void`.
If we specify that a proof uses the negative premise `nT` exactly once, it is admissible to state that we
can extract the counter-example fed into it from the closed proof term:
```
 prf : □( (nT :¹¬T) → Void ) 
—————————————————————————————
      extract(prf) : T
```

If the proof uses the negative premise at most once, extraction is not guaranteed to terminate.
```
  prf : □( (nT :⁻¬T) → Void ) 
———————————————————————————————
 extract(prf) : Computation<T>
```

If we do not pose any restrictions on the usage multiplicity, the extraction process might yield any number of results.
```
   prf : □(¬¬T) 
———————————————————
 extract(prf) : §T
```
To account for this, we must introduce the surveyable subsets monad `§T`.
As we’ll see below, it provides an interpretation for the recently developed Verse calculus, a novel approach
to deterministic functional logic programming.
We will argue
that Verse calculus terms provide classical realizability interpretation^[[Krivine21](https://arxiv.org/abs/2006.05433)]
for the non-constructive reasoning under ◇-modality.

# Surveyable subsets

Let us work in a univalent type theory with enough inductive types to express
Cauchy completions including the monad `Computation<T>` of Turing-complete
computations returning `T` if they terminate. For every type `T` we'll can
define the type of Turing-complete lazy sequences `LazySeq<T>`:

```kotlin
structure LazySeq<T>:
  next : Computation<T × LazySeq<T>>
```

Let us say that a lazy sequence `s : §T` intersects a computationally verified
predicate `p : T → Computation<Unit>` iff it has an element satisfying the predicate,
and call sequences intersecting same predicates image-equivalent:
```kotlin
def <T> LazySeq<T>.intersects(p : T → Computation<Unit>)
  ∃(head, tail) (s.next = return (head, tail)) and
  ( p(head) = (return ()) ) or tail.intersects(p) )

def <T> imageEq(s q : LazySeq<T>)
  ∀(p : T → Computation<Unit>) x.intersects(p) = x.intersects(q) 
```

Since the above definitions respect image equivalence, we can define the type `§T`
of lazy sequences modulo image equivalence. It is the type of surveyable subsets of `T`.

Let us also say that `s : §T` covers an `x : T`
iff it intersects every computationally verifiable predicate `p : T → Computation<Unit>`
that holds for `x`:
```
def <T> (§T).covers(x : T) =
  ∀(p : T → Computation<Unit>, p(x) = (return ()))
   s.intersects(p)
```

Types `T` equipped by an `s : §T` covering the whole type will be called surveyable:
```
structure Surveyable<this T>
  enumerate : §T
  fullness : ∀(x : T) enumerate.covers(x)
```

All finitary datatypes (such as `Fin(n)`, `ℕ`, `ℤ` and `ℚ`) and their
Cauchy completions (such as `ℝ`) are surveyable. In case of finitary
datatypes, `enumerate` just enumerates all closed terms, while in case of
Cauchy completions it numerates elements of the enumerable dense
subset the type was generated by.

For convenience let us introduce the universe `FinData` of finitary
data types, the types which are by construction isomorphic to `ℕ` or
to `Fin(n)` for some fixed `n : ℕ`. `FinData` includes all quotient
inductive types with closed definitions that do not mention functions
with non-finite domain or other coinductive types. `FinData` includes
`ℕ`, `ℤ`, `ℚ` and all decidable predicates and relations such `n < m`
and `n = m` for `n m : ℕ`, `ℤ` or `ℚ`, but does not include `ℝ`, nor
the predicates `x = y` and `x < y` for `x y : ℝ`.

A predicate is surveyable iff it is verifiable, so `x < y` for real
`x y : ℝ` is surveyable, while `x = y` is not.

Notably, we can generate a list of solutions for a verifiable
predicate on a surveyable type: 
```kotlin
def <T : Surveyable> findAll(p : T → Computation<Unit>) : §T
```

# Spectral variables

For any type `T`, the type `§T` is pointed as it can be instantiated by
a divergent computation `⊥ : §T`.

The type constructor `§T` carries a natural structure of a strong monad, as we
have
```kotlin
def unit(x) = return(x, ⊥)
def <T> §(§T).flatten() : §T
def <T, R> §T.map(f : T → R) : §R
def infix <X, Y> zip(x : §X, y: §Y) : §(X × Y)
```

Note that `§(X × Y)` is not equal to the cartesian product of type `§X × §Y`, but to
the smash product `§X ∧ §Y` of pointed types `(X, ⊥)` and `(X, ⊥)`.
For all `x : X` and `y : Y`, `zip(unit(x), ⊥)` and `zip(unit(x), ⊥)` map to `zip(⊥, ⊥)`.

For any type `T` we have the function `forget(x : T) : Unit`, so we can also define
```kotlin
def infix <X, Y> then(x : §X, y: §Y) : §Y
  x.map(::forget) zip y
```

Now let us introduce a deeply embedded do notation for this monad, which would almost perfectly correspond
to the recently developed Verse calculus.

First let us introduce special types
`♮T` which correspond to `§T` under the hood but do not belong to the usual type theoretic universes and
do not have usual `Id`-types on them. For the reasons explained below, we will call these spectral types.
They will be used to introduce special substructural variables we will call spectral variables `x : ♮X`.

Let us define the spectral pairing and spectral application:
```
 Γ ⊢ x : ♮X    Γ ⊢ y : ♮Y       Γ ⊢ x : ♮X    Γ ⊢ y : ♮Y       Γ ⊢ x : ♮X    Γ ⊢ f : ♮(X → Y)
——————————————————————————     ——————————————————————————     ————————————————————————————————
     Γ ⊢ (x; y) : ♮Y              Γ ⊢ (x, y) : ♮X ∧ ♮Y              Γ ⊢ f(x) : ♮Y
```

Under the hood this, operations work via `then`, `zip` and `map`. Availability of `unit` and strong
monad laws guarantee that a normal variable always can be used where a spectral variable is expected.

With `findAll` we can implement the ∃-binder of the Verse calculus:
```
 Γ ⊢ X : Surveyable    Γ, x : X ⊢ y : ♮Y
—————————————————————————————————————————
        Γ ⊢ (ε(x : Y) y) : ♮X
```

We also can introduce
```
 Γ ⊢ T : *          Γ ⊢ s : ♮(§T)           Γ ⊢ x : ♮T  
————————————     ———————————————————     ————————————————— 
 Γ ⊢ ⊥ : ♮T       Γ ⊢ anyOf(s) : ♮T       Γ ⊢ all(x) : §T 
```

Using diverging computation, `flattening` and the acknowledging that spectral variables work via §-types under the hood.

The only missing thing from the Verse calculus is the `one` operator we prefer calling `any`:
```
 Γ, any : ∀<T> ♮T → T ⊢ expr : X
————————————————————————————————
       Γ ⊢ expr : ♮X
```

Note similarity between `any` operator here and `ε` operator for the `◇`-modality.

Now it remains to be shown (by induction on Verse calculus terms), that our system can interpret Verse
calculus with essentially the same reduction rules. Since Verse calculus satisfies a condition called
logical completeness, it is also admissible for our system:
```
    Γ ⊢ X : Surveyable      Γ, x : X ⊢ y : ♮Y
————————————————————————————————————————————————————
 ∀(x : X) (y(x) ≠ ⊥) = all(ε(x': Y) y(x)).covers(x)
```

Logical completeness can be further generalized to state that functional logic programming together with
extraction operator `extract : □(¬¬T) → ♮T` provide a sound classical realizability interpretation to non-constructive 
reasoning within `◇`.