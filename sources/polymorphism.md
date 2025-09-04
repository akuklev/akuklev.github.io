□Parametric Polymorphism for Agnostic Type Theories
===================================================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com),
[JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)
& [Radboud Univ. Nijmegen](https://sws.cs.ru.nl/Person/Guests)

Our starting point will be a type theory with a countable hierarchy of universes
introduced by the following infinite family of rules:
$$
\frc{}{Γ ⊢ Type : Type⁺}\quad
\frc{}{Γ ⊢ Type⁺ : Type⁺⁺}\quad
\frc{}{Γ ⊢ Type⁺⁺ : Type⁺⁺⁺}\quad\cdots
$$

Considered together, these rules introduce a countably infinite family of well-typed terms `Type`, `Type⁺`, `Type⁺⁺`, etc., but they have to be considered together as the type used in each rule is first introduced by the next rule.

Let us postulate the first universe `Type` to be ΠΣ-closed and add some basic types to taste:
$$
\frc{}{Void : Type}\quad
\frc{}{Unit : Type}\quad
\frc{}{Bool : Type}
$$
$$
\frc{Γ ⊢ X : Type \quad Γ, x : X ⊢ Y(x) : Type
}{Γ ⊢ (x : Y) × Y(x) : Type}\qquad
\frc{Γ ⊢ X : Type \quad Γ, x : X ⊢ Y(x) : Type
}{Γ ⊢ ∀(x : Y) Y(x) : Type}
$$
(We will write `X → Y` for non-dependent Π-types `∀(_ : X) Y`.)

We want a type theory where all closed-form type former definitions
`F(K : Type⁺) : Type`, can be lifted to the higher universes. The “closed-form” restriction is essential to avoid inconsistencies. So let's introduce the S4 necessity □-modality mapping types `T` to
sets of their closed-form inhabitants `t : □T`. Naïvely, we can try the following rules:
$$
\frc{□Г ⊢ x : X
}{□Г, Δ ⊢ x : □X}\texttt{(□Intro)}\qquad
\frc{Г ⊢ x : □X
}{Г ⊢ x : X}\texttt{(□Elim)}
$$

Here we say that an inhabitant definable in a context only containing closed-form expressions is a closed-form inhabitant,
and that a closed-form inhabitant of `X` is an inhabitant of `X`.

Unfortunately, this definition is unsatisfactory in presence of dependent types.
To proceed, we need to make our type theory `{0, ω}`-graded,
that is we will allow marking some variables in contexts as
opaque using zero subscripts above the colon.
It will allow introducing parametric quantifiers `∀<x : X> T(x)` (note angle brackets instead of parens):
$$
\frc{Γ ⊢ X : Type \quad    Γ, x : X ⊢ Y(x) : Type}{Γ ⊢ ∀\<x : Y\> Y(x) : Type}\qquad
\frc{Γ ⊢ X : Type \quad  Г, x :° X ⊢ y : Y(X)}{Г ⊢ \\{ x :° X ↦ Y(X) \\} : ∀\<x : Y\> Y(x) }

But more importantly, it allows adjusting the rules for the □-modality to work well with dependent types.
In the introduction rule we allow opaque variables,
while in the elimination rule we state
that a closed-form element can only depend on non-closed-form elements opaquely:
$$
\frc{□Г, Δ° ⊢ x : X
}{□Г, Δ°, Σ ⊢ x : □X}\texttt{(□Intro)}\qquad
\frc{Г ⊢ x : □X(t)
}{Г° ⊢ x : X(t)}\texttt{(□Elim)}
$$

Now let us define the universe-shifting operator ( ⁺) for all types.
Its action on the types will be defined on a case-by-case basis for all type formers, i.e. coinductively. Types living inside the first universe `Type` are constructed without mentioning `Type`, so the universe-shifting operator does not affect them. Otherwise, universe shifting is applied componentwise:
$$
\texttt{((x : Y) × Y(x))⁺ ↦ (x : Y⁺) × (Y(x))⁺}
$$
$$
\texttt{\quad\  (∀(x : Y) Y(x))⁺  ↦ ∀(x : Y⁺) × (Y(x))⁺ }
$$

Now we can finally introduce an infinite family of rules ensuring that closed-form type formers work in all universes above their original universe:
$$
\frc{Γ ⊢ K : Type⁺ \quad Γ ⊢ F : □(K → Type)
}{Γ ⊢ F : K⁺ → Type⁺}\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad
$$
\vspace{-0.4ex}
$$
\frc{Γ ⊢ K : Type⁺⁺ \quad Γ ⊢ F : □(K → Type⁺)
}{Γ ⊢ F : K⁺ → Type⁺⁺}\qquad\qquad\qquad\quad
$$
\vspace{1ex}
$$
\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\frc{Γ ⊢ K : Type⁺⁺⁺ \quad Γ ⊢ F : □(K → Type⁺⁺)
}{Γ ⊢ F : K⁺ → Type⁺⁺⁺}\qquad\qquad\qquad
$$
$$
\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\ddots
$$
Closed-form type formers such as `List<T : Type> : Type` and `Endo<T : Type> := T → T` are now applicable to types in any universes. It also works for typeclasses^[Typeclasses are introduced as records with a marked (by `this`), possibly higher-kinded, typal parameter, but turn into a subtype of their marked parameter’s type, e.g. `Boolᴿ <: Type`, so every `T : Boolᴿ` is both a type and an instance of `Boolᴿ<T>`, which does not introduce ambiguities since types and families cannot have fields, while typeclass instances are records and consist from their fields. See \href{https://akuklev.github.io/kotlin/kotlin_typeclasses.pdf}{\texttt{kotlin\\_typeclasses.pdf}} for details.] such as
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Monoid<this M : Type>(unit : M,
                           compose : M² → M,
                           ...axioms)
```
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Monad<this F : Type → Type>(    // Higher kinded typeclasses work too!
  unit<T>(x : T) : F<T>
  compose<X, Y>(x : F<X>, y : X → F<Y>) : F<Y>
  ...axioms)
```

(To deal with typeclasses more conveniently, let us introduce the following shorthand notation:
given a typeclass `F : K → U`, let `∀<X : F> Y(X)` mean
`∀<X : K> ∀(X : F<X>) Y(X)`
where `X` can mean both the carrier `X : K` and the instance `X : F<T>`, disambiguated by the context.)

Let us now use parametric quantifiers for the cumulativity rules for terms of polymorphic types:
$$
\frc{Γ ⊢ K : Type⁺ \quad Γ ⊢ F : □(K → Type)\quad Γ ⊢ c : □∀\<T : K\> F(T)
}{Γ ⊢ c : ∀\<T : K⁺\> F(T)} \quad \cdots
$$

Consider the following polymorphic function:
```kotlin
|\textbf{\textcolor{dgreen}{def}}| id : ∀<T : Type> T → T
  x ↦ x
```
With the rule above, it additionally inhabits `Endo<T : Type⁺>`, `Endo<T : Type⁺⁺>`, etc.

Consider the canonical instance of the monoid typeclass and the Cayley Embedding construction:
```kotlin
object Endo<T> : Monoid<Endo<T>>
  unit = id<T>
  compose(f g : Endo<T>) = { x : T ↦ f(g(x)) }
```
```kotlin
|\textbf{\textcolor{dgreen}{def}}| cayleyEmbedding : ∀<M : Monoid> MonoidMorphism<M, Endo(M)>
  ...
```

We only give the definitions for small monoids, but with cumulativity, they work for all monoids regardless of size, provided that definitions are closed and only depend on typal parameters parametrically.

# Unary parametricity

We have achieved that `id := { x ↦ x }` inhabits `Endo<T>` in all universes,
but we can also extend our type theory
so we can show that `id` is the only closed-form inhabitant of `∀<T> Endo<T>` up to equivalence.
The □-modality together with ( ᵈ) operator from Displayed Type Theory allows □-internal parametric reasoning.
As opposed to type theories with non-modal internal parametricity,
this approach does not contradict LEM (law of excluded middle) maintaining the underlying type theory constructively agnostic.

In 1941, Alonzo Church noticed that natural numbers can be represented as
polymorphic functions of the type `∀<T> (T → T) → T → T`.
All other inductive types also have Church encodings, and
the type of `id : ∀<T> (T → T)` is the Church encoding for the `Unit` type.
To establish that `id` is its unique closed-form inhabitant,
it is enough to postulate
that closed-form inhabitants of Church encoded inductive datatypes are exhausted by Church encodings.

Every inductive type `I : U` comes with a dual typeclass `Iᴿ<T : U>`. For natural numbers:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| ℕᴿ<this T : U>(base : T
                    next : T → T)
```

Instances of `Iᴿ` define structural recursion for the type `I`. Church encodings `xᶜ : ∀<T : Iᴿ> → T` evaluate instances of `Iᴿ` for `x`:
```kotlin
|\textbf{\textcolor{dgreen}{def}}| 0ᶜ = { T :° U, T : ℕᴿ<T> ↦ T.base }
|\textbf{\textcolor{dgreen}{def}}| 1ᶜ = { T :° U, T : ℕᴿ<T> ↦ T.next T.base }
|\textbf{\textcolor{dgreen}{def}}| 2ᶜ = { T :° U, T : ℕᴿ<T> ↦ T.next (T.next T.base) }
...
```

Both the original and the Church-encoded inductive type form an instance of the typeclass Iᴿ:
```kotlin
object ℕ : ℕᴿ
  |\textbf{\textcolor{dgreen}{def}}| base = 0
  |\textbf{\textcolor{dgreen}{def}}| next = ( ⁺)
```
```kotlin
object ℕᶜ : ℕᴿ
  |\textbf{\textcolor{dgreen}{def}}| base = 0ᶜ
  |\textbf{\textcolor{dgreen}{def}}| next = ( ⁺)ᶜ
```

To postulate that the instance `ℕ` is the initial model,
we need to introduce the induction rule (that is, the dependent elimination rule)
for `ℕ`. Ensuring that closed-form inhabitants of `ℕᶜ` are exhausted by Church encodings of `ℕ` elements
is essentially the same rule,
but for the type `□ℕᶜ` instead of `ℕ`. To formulate both rules uniformly for all inductive types,
let us apply the ( ᵈ) operator introduced in Displayed Type Theory to the typeclass `Iᴿ`:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| ℕᴿᵈ<T : U>(M : ℕᴿ<T>)<this Ts : T → U>(base : T
                                            next : T → T)
```

Now we can formulate induction and unary parametricity:
```kotlin
I-ind(n : I) : ∀<M : Iᴿᵈ I> → (M n)
```
```
I-par(n : □Iᶜ) : ∀(R : Iᴿᵈ Iᶜ) → (R n)
```

We can use `Unit-par` to derive that `id` is the unique closed-form inhabitant of `∀<T> (T → T)`:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Unitᴿ<this T>(point : T)  // Dual of the `Unit` type are pointed types
```
```kotlin
object Helper : Unitᴿᵈ<Unitᶜ> { id : Unitᶜ ↦ (id ≃ { x ↦ x }) }
  |\textbf{\textcolor{dgreen}{def}}| point = refl
```
```kotlin
|\textbf{\textcolor{dgreen}{theorem}}| ∀(id : □∀<T : U> T → T) id ≃ { x ↦ x }
  id ↦ Unit-par id Helper
```

Ideas we present in [“Reedy Types and Dependent Type Families”](https://akuklev.github.io/reedy.pdf) indicate a direction beyond unary parametricity towards `S`-shaped parametricity for any effectively presentable Reedy category `S`. In addition to well-known applications of binary (Wadler's “Theorems for Free”) and $n$-ary parametricity, it enables extending polymorphism and cumulativity beyond `upwards-only` allowing to generalize from `U` to presheaf universes `J → U` and `(J → U⁺) → U`.

# Classical reasoning and functional logic programming

In the [companion paper](https://akuklev.github.io/verse) we argue
that it is also possible to introduce a modality dual to □,
namely the S4-possibility modality mapping each type `T` to the spectrum `◇T` of its formal inhabitants,
i.e., inhabitants that can “non-constructively shown to exist”
using choice operator (as in Lean4) and double negation elimination as its special case.
This modality allows classical (non-constructive)
reasoning within `◇`-fragment
without compromising computational properties of the underlying type theory such as canonicity,
normalization and decidability of type checking, as well as its compatibility with univalence.
These desirable properties remain intact even if impermeability of the `◇`-fragment is violated by
computational Markov Principle (CMP) that allows evaluating Turing-complete computations given
a closed-form classical proof of their non-divergence:
$$
\frc{c : Computation\<T\> \quad  nonDivergence : □◇(c ≠ ⊥)}{eval(c, nonDivergence) : T}
$$

We can easily show that the type `M = W(T : U) ◇T` of iterative classical sets satisfies all axioms
of the classical set theory ZFC, and the reasoning under `◇`-modality satisfies Hilbert axioms
of classical logic, thus our proposed type theory contains a model of ZFC.

# Relation to Shulman’s strong Feferman set theory `ZMC/S`

Let us additionally assume an impredicative universe Prop of propositions and that the universes `Type : Type⁺ : Type⁺⁺ : Type⁺⁺⁺ : ···` are closed under the formation of types by PN-inductive-recursive type definitions^[cf. Variations on Inductive-Recursive Definitions by N Ghani, C McBride, F Nordvall Forsberg, and S Spahn],
it is possible to manually construct closed Tarski universes `V : U`. In particular, for any finite collection of type formers `Fₙ : (Kₙ → U) → U` where `Kₙ : U⁺`, we can construct a universe `V : U` containing codes for all types `T : U` that can be generated using type formers `Fₙ`.

In this way, the resulting type theory is analogous to the strong Feferman set theory `ZMC/S`
[introduced by M. Shulman](https://arxiv.org/pdf/0810.1279). Moreover, it is, presumably, a conservative extension thereof.

Let us interpret the language of `ZMC/S` into the universe `Prop` as follows: translate `S`-bounded quantification into Π-types over sets `M := W(T : Type) ◇T`, and translate unbounded quantification over sets into parametrically quantified propositions
via Zakharyaschev subframe canonical formulae. We have manually checked that such translation turns out to satisfy all axioms of `ZMC/S`. At the same time, it seems possible to exhibit a construction that yields `ZMC/S`-valued models for finite fragments of this type theory built in such a way that the type-theoretic translation of
the set-theoretic formula φ is only inhabited if the formula φ holds in the model.

Conservativity implies equiconsistency, so it should be possible to adapt the consistency-dependent canonicity proof
for TTobs by [L. Pujet and N. Tabareau](https://dl.acm.org/doi/10.1145/3498693) to show desirable computational
properties claimed above.


# Relation to Stratified Type Theory and Mahlo universes

In 2024, [J. Chan and S. Weirich devised a stratified type theory StraTT](https://arxiv.org/pdf/2309.12164), a
logically consistent type theory that allows speaking of the all-encompassing universe `Type : Type` by stratifying
typing judgments.
This approach parallels New Foundations, a non-well-founded set theory developed by W. V. Quine in 1937,
the only successful foundational theory able to speak of all-encompassing self-containing universal objects,
which was recently definitely shown to be consistent.
Stratified type theory can probably be extended to admit the `ω`-category of all `ω`-categories, and used to explore
the boundaries of what can be said about such an object.

It remains to be figured out how stratified type theory relates to the approach presented here.