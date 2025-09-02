◇Classical Reasoning in Constructive Type Theories
==================================================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com), [JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)

# The non-constructive modality

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

NB: To remain consistent with univalence under the ◇-modality, `ε` should only be applicable
to data types, i.e. types satisfying uniqueness of identity proofs propositionally.

With ε is both double negation elimination (“law of excluded middle”)
for propositional types `T` and axiom of choice for the non-propositional data types.

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
————————————————————————————————
 extract(prf) : Computation⁎<T>
```
To account for this, we must introduce the monad `Computation⁎<T>` of surveyable subsets.
As we will see below, it provides an interpretation for the recently developed Verse calculus, a novel approach
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

Let us say that a lazy sequence `s : LazySeq<T>` intersects a computationally verified
predicate `p : T → Computation<Unit>` iff it has an element satisfying the predicate,
and call sequences intersecting same predicates image-equivalent:
```kotlin
def <T> LazySeq<T>.intersects(p : T → Computation<Unit>)
  ∃(head, tail) (s.next = return (head, tail)) and
  ( p(head) = (return ()) ) or tail.intersects(p) )

def <T> imageEq(s q : LazySeq<T>)
  ∀(p : T → Computation<Unit>) x.intersects(p) = x.intersects(q) 
```

Since the above definitions respect image equivalence, we can define the type `Computation⁎<T>`
of lazy sequences modulo image equivalence. It is the type of surveyable subsets of `T`.

Let us also say that `s : Computation⁎<T>` covers an `x : T`
iff it intersects every computationally verifiable predicate `p : T → Computation<Unit>`
that holds for `x`:
```kotlin
def <T> Computation⁎<T>.covers(x : T) =
  ∀(p : T → Computation<Unit>, p(x) = (return ()))
   s.intersects(p)
```

Types `T` equipped by an `s : §T` covering the whole type will be called surveyable:
```kotlin
structure Surveyable<this T>
  enumerate : Computation⁎<T>
  fullness : ∀(x : T) enumerate.covers(x)
```

All descrete finitary types (such as `Fin(n)`, `ℕ`, `ℤ` and `ℚ`) and their
Cauchy completions (such as `ℝ`) are surveyable. In case of finitary
types, `enumerate` just enumerates all closed terms, while in case of
Cauchy completions it numerates elements of the enumerable dense
subset the type was generated by.

For convenience let us introduce the universe `FData` of discrete finitary
types which are isomorphic to `ℕ` or to `Fin(n)` for some fixed `n : ℕ`.
`FData` includes all quotient inductive types with closed definitions
that do not mention functions with non-finite domain or other coinductive
types. `FData` includes `ℕ`, `ℤ`, `ℚ` and all decidable predicates and
relations such `n < m` and `n = m` for `n m : ℕ`, `ℤ` or `ℚ`, but does
not include `ℝ`, nor the predicates `x = y` and `x < y` for `x y : ℝ`.

A predicate is surveyable iff it is verifiable, so `x < y` for real
`x y : ℝ` is surveyable, while `x = y` is not.

Notably, we can generate a list of solutions for a verifiable
predicate on a surveyable type: 
```kotlin
def <T : Surveyable> findAll(p : T → Computation<Unit>) : Computation⁎<T>
```

# Spectral variables and Verse calculus

The types `Computation⁎<T>` are pointed as they can be instantiated by
a divergent computation `⊥ : Computation⁎<T>` and carry a natural structure
of a strong monad, as we
have
```kotlin
def unit(x) = return(x, ⊥)
def <T> Computation⁎<Computation⁎<T>>.flatten() : Computation⁎<T>
def <T, R> Computation⁎<T>.map(f : T → R) : Computation⁎<R>
def infix <X, Y> zip(x : Computation⁎<X>,
                     y : Computation⁎<Y>) : Computation⁎<X × Y>
```

Note that `Computation⁎<X × Y>` is not equal to the cartesian product of type `Computation⁎<X> × Computation⁎<Y>`, 
but to the smash product `Computation⁎<X> ⊗ Computation⁎<Y>` of pointed types `(X, ⊥)` and `(X, ⊥)`.
For all `x : X` and `y : Y`, `zip(unit(x), ⊥)` and `zip(unit(x), ⊥)` map to `zip(⊥, ⊥)`.

For any type `T` we have the function `forget(x : T) : Unit`, so we can also define
```kotlin
def infix <X, Y> then(x : Computation⁎<X>, y : Computation⁎<Y>) : Computation⁎<Y>
  x.map(::forget) zip y
```

Now let us introduce a deeply embedded do notation for this monad, which would almost perfectly correspond
to the recently developed Verse calculus.

First let us introduce special types `§T` that to `Computation⁎<T>` under the hood but do not belong to the usual
type theoretic universes `*`, and do not have the usual `Id`-types that make ordinary types `T : *` into
∞-groupoids. Instead, these types belong to special universes `𝒮` and have stabilized `Id`-types making
them into Ω-spectra. For this reason we will call these spectral types.

For any two spectral types `X Y : 𝒮` realized by `Computation⁎<X>` and `Computation⁎<Y>` “under the hood”,
we have the smash product `X ⊗ Y` realized by `Computation⁎<X × Y>` and wedge sum `X ⊕ B`
realized by `Computation⁎<X + Y>`.
We also have their indexed versions, the wedge and smash quantifiers:
```
  Γ, x : X ⊢ Y : 𝒮         Γ, x : X ⊢ Y : 𝒮
————————————————————     ————————————————————
 Γ ⊢ ⊕(x : X) Y : 𝒮       Γ ⊢ ⊗(x : X) Y : 𝒮
```

We introduce spectral types to introduce special substructural variables we will call spectral variables `x : §X`.

Let us define the spectral pairing and spectral application:
```
 Γ ⊢ x : §X    Γ ⊢ y : §Y       Γ ⊢ x : §X    Γ ⊢ y : §Y       Γ ⊢ x : §X    Γ ⊢ f : §(X → Y)
——————————————————————————     ——————————————————————————     ————————————————————————————————
     Γ ⊢ (x; y) : §Y              Γ ⊢ (x, y) : §X ⊗ §Y              Γ ⊢ f(x) : §Y
```

Under the hood this, operations work via `then`, `zip` and `map`. Availability of `unit` and strong
monad laws guarantee that a normal variable always can be used where a spectral variable is expected.

With `findAll` we can implement the ∃-binder of the Verse calculus:
```
 Γ ⊢ X : Surveyable    Γ, x : X ⊢ y : §Y
—————————————————————————————————————————
        Γ ⊢ (ε(x : Y) y) : §X
```

We also can introduce
```
 Γ ⊢ T : *         Γ ⊢ s : §Computation⁎<T>          Γ ⊢ x : §T  
————————————     ————————————————————————————     ————————————————— 
 Γ ⊢ ⊥ : §T           Γ ⊢ anyOf(s) : §T           Γ ⊢ all(x) : §T 
```

Using diverging computation, `flattening` and the acknowledging that spectral variables work via §-types under the hood.

The only missing thing from the Verse calculus is the `one` operator we prefer calling `any`:
```
 Γ, any : ∀<T> §T → T ⊢ expr : X
————————————————————————————————
       Γ ⊢ expr : §X
```

Note similarity between `any` operator here and `ε` operator for the `◇`-modality.

Now it remains to be shown (by induction on Verse calculus terms), that our system can interpret Verse
calculus with essentially the same reduction rules. Since Verse calculus satisfies a condition called
logical completeness, it is also admissible for our system:
```
    Γ ⊢ X : Surveyable      Γ, x : X ⊢ y : §Y
————————————————————————————————————————————————————
 ∀(x : X) (y(x) ≠ ⊥) = all(ε(x': Y) y(x)).covers(x)
```

Logical completeness can be further generalized to state that functional logic programming together with
extraction operator `extract : □(¬¬T) → §T` provide a sound classical realizability interpretation to non-constructive 
reasoning within `◇`.

# Equality structure of spectral types

For finitely presented higher inductive types `J` we always have an algorithm `findEq(x, y)`
that finds equivalences `x ≃ y` between its two elements `x y : J` if they exists,
but is not guaranteed to halt.
The result type of `findEq` is `(c : Computation*<x ≃ y>, (c = ⊥) = ¬T)`.

What happens if we apply `findEq` to two spectral variables `x y : §T`?
We obtain a new spectral type `x ≗ y` with which corresponds to the computation type
`(c : Computation*<x ≃ y>, (c = ⊥) = (¬T ∨ (x = ⊥) ∨ (y = ⊥))` that heavily reminds
of reduced suspensions. We conjecture, that higher equality structure of the spectral
type generate by an ordinary type (a ∞-groupoid in HOTT) is its reduced suspension
spectrum, while equality structures of spectral types in general are given by
sequential spectra.

# Perceived entanglement and spectral quantifiers

The peculiar property of Verse calculus deep embedding is our ability to extend contexts with spectral variables by
non-spectral ones:
```
  Γ, x : X ⊢ Y : *
—————————————————————
 Γ, x :§X, y : Y ctx
```

This way, we can entangle spectral variables:
```
 Γ, p q : §ℤ, w : (p + q = 5) ⊢ expr
```
In the body of `expr` the spectral variables `p` and `q` can assume arbitrary values individually,
their sum will always be 5.

In some context `Γ, x : §X` we can have a spectrum of types `Y : §*` and an entangled spectrum of
values `y` so that `Y` and `y` can only appear in such pairs that `y : Y` or `y : §Y`, which allows
us to define two spectral quantifiers
```
 Γ, x : §X ⊢ Y : §*      Γ, x : §X ⊢ y : Y
———————————————————————————————————————————
       Γ ⊢ (x : §X ↦ y) : &(x : §X) Y
          
 Γ, x : §X ⊢ Y : §*     Γ, x : §X ⊢ y : §Y
———————————————————————————————————————————
       Γ ⊢ (x : §X ↦ y) : ⅋(x : §X) Y
```

# Admissibility of modal Church’s thesis

Let us call a data type `Equatable` if its identity types are surveyable,
`Discernible` the negation of its identity types are surveyable, or
`Discrete` if both (i.e. its identity types are decidable).
Let us denote partial functions by `X ⇀ Y`.
We conjecture that the following three rules are admissible:

**Closed-form inhabitants of equatable types are formally subcountable:**
```kotlin
∀<T : Equatable> ◇(d : ℕ ⇀ □T) isSurjective(d)

def <X> isSurjective(d : ℕ ⇀ X) 
  ∀(x : X) ∃(n : ℕ) x = d(n)
```

**Discernible types are formally completely separable:**
```kotlin
∀<T : Discernible> ◇(d : ℕ ⇀ □T) isDense(d)

def <X> isDense(d : ℕ ⇀ X) 
  ∀(x : X) ∃(s : ℕ → ℕ) x = lim(d ∘ s)
```

**Closed-form functions are formally continuous:**
```kotlin
∀<X, Y> ∀(f : □(X → Y)) ◇isContinuous(f)
```

Formal continuity is equivalent to with formal (synthetic) computability,
so the latter principle is the modal version of Church’s thesis.
