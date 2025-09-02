□Parametric Polymorphism for Agnostic Type Theories
===================================================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com),
[JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)
& [Radboud Univ. Nijmegen](https://sws.cs.ru.nl/Person/Guests)

Our starting point will be a type theory with a countable hierarchy of universes
introduced by the following infinite family of rules:
```
––––––––––––––––––     ––––––––––––––––––––     ––––––––––––––––––––––     ···
 Γ ⊢ Type : Type⁺       Γ ⊢ Type⁺ : Type⁺⁺       Γ ⊢ Type⁺⁺ : Type⁺⁺⁺
```

These rules introduce a countably infinite family of well-typed terms `Type`, `Type⁺`, `Type⁺⁺`, etc.,
and have to be considered together as the type used in each rule is first introduced in the next one.

Let us postulate the first universe U to be Σ- and Π-closed and add some basic types to taste:
```
 Γ ⊢ X : Type     Γ, x : X ⊢ Y(x) : Type       Γ ⊢ X : Type     Γ, x : X ⊢ Y(x) : Type
–––––––––––––––––––––––––––––––––––    –––––––––––––––––––––––––––––––––––– 
      Γ ⊢ (x : Y) × Y(x) : Type                  Γ ⊢ ∀(x : Y) Y(x) : Type

––––––––––––––     –––––––––––––      –––––––––––––      –––––––––––––
 Γ ⊢ 𝟘 : Type       Γ ⊢ 𝟙 : Type       Γ ⊢ 𝔹 : Type       Γ ⊢ ℕ : Type
```

(We will write `X → Y` for `∀(_ : X) Y`, i.e., the non-dependent case of Π-types.)

Our goal is to state variadic cumulative.
That is, we want to state that every type belonging to some universe `Type` also belongs to `Type⁺`,
and every type former `F(K : Type⁺) : Type` can be also lifted one universe above.
The second rule leads to inconsistency unless we only state it for closed-form type formers, i.e.
the ones definable in empty context.
Naïvely,
we can try
to introduce the S4 necessity □-modality mapping types `T` to
their sets of closed-form inhabitants `t : □T` by the following two rules:
```
 • ⊢ x : X                Г ⊢ x : □X      
––––––––––––(□Intro)     ––––––––––––(□Elim)
 Г ⊢ x : □X               Г ⊢ x : X
```

Here we say that an inhabitant definable in an empty context is a closed-form inhabitant (□Intro),
and that a closed-form inhabitant of `X` is an inhabitant of `X` (□Elim).

In the first rule we can allow a context containing only closed-form inhabitants:
```
 □Г ⊢ x : X
––––––––––––––––(□Intro)
 □Г, Δ ⊢ x : □X
```     

Now we can clearly see that it is indeed the S4 necessity modality.
But in this form it does not work well with dependent types.
To proceed, we need to make our type theory {0, ω}-graded,
that is we will allow marking some variables in contexts as
opaque using zero subscripts above the colon.
It will allow introducing parametric quantifiers `∀<x : X> T(x)` (note angle brackets instead of parens):
```
 Γ ⊢ X : Type     Γ, x : X ⊢ Y(x) : Type
–––––––––––––––––––––––––––––––––––––––––
   Γ ⊢ ∀<x : Y> Y(x) : Type

   Γ ⊢ X : Type   Г, x :° X ⊢ y : Y(X)
–––––––––––––––––––––––––––––––––––––––
 Г ⊢ { x :° X ↦ Y(X) }: ∀<x : Y> Y(x) 
```

But more importantly, it allows adjusting the rules for the □-modality to work well with dependent types.
In the introduction rule we allow opaque variables,
while in the elimination rule we state
that a closed-form element can only depend on non-closed elements of the context opaquely:
```
   □Г, Δ° ⊢ x : X                  Г ⊢ x : □X(t)
––––––––––––––––––––(□Intro)      –––––––––––––––(□Elim)
 □Г, Δ°, Σ ⊢ x : □X                Г° ⊢ x : X(t)

(We use the notation □Γ and Γ° to apply □/° to each element of Γ.)
```

Now let us define the universe-shifting operator ( ⁺) for all types.
Its action on the types will be defined on a case-by-case basis for all type formers (i.e. coinductively).
It shifts the universe levels in types built using universes, e.g. `(Type → Type)⁺` should be `(Type⁺ → Type⁺)`,
while doing nothing for types inside the base universe as they cannot involve universes in their definitions:
```
 Γ ⊢ T : Type
––––––––––––––
  T⁺ ↦ T

 ((x : Y) × Y(x))⁺ ↦ (x : Y⁺) × (Y(x))⁺
 (∀(x : Y) Y(x))⁺  ↦ ∀(x : Y⁺) × (Y(x))⁺    
```

Now we can finally write down the cumulativity rules that do not only ensure that closed-form types
(e.g. `𝟙 : Type`, `(ℕ → 𝔹) : Type`) also live in all universes above the one they were defined for,
but also that all closed-form type formers defined for some universe are also applicable to all universes above:
```
 Γ, K : Type⁺ ⊢ F : □(K → Type)      Γ, K : Type⁺⁺ ⊢ F : □(K → Type⁺)     Γ, K : Type⁺⁺⁺ ⊢ F : □(K → Type⁺⁺)      
———————————————————————————————    ——————————————————————————————————    ———————————————————————————————————   ···
     Γ ⊢ F : K⁺ → Type⁺                   Γ ⊢ F : K⁺ → Type⁺⁺                   Γ ⊢ F : K⁺ → Type⁺⁺⁺
```

This rule makes closed-form type formers polymorphic,
i.e., once we define a type-former such as `List<T : Type> : Type`, `Endo<T : Type> := T → T`
for some universe in an empty context, it automatically becomes applicable to all higher universes.
Now we need the cumulativity rule for the inhabitants of polymorphic types:
```
 Γ, K : Type⁺ ⊢ F : □(K → Type)     Γ ⊢ c : □∀<T : K> F(T)
———————————————————————————————————————————————————————————
                Γ ⊢ c : ∀<T : K⁺> F(T)
```

This way,
```
def id : ∀<T : Type> T → T
  x ↦ x
```
is not only inhabitant of `Endo<T : Type>`,
but also an inhabitant of `Endo<T : Type⁺>`, `Endo<T : Type⁺⁺>`, etc.

Polymorphism allows defining mathematical structures ([“typeclasses”](kotlin/kotlin_typeclasses.pdf))
without size restrictions.
One of the simplest structures is the monoid:
```
data Monoid<this M : Type>(unit : M,
                           compose : M² → M,
                           ...axioms)
```
A typical example is the monoid of endomorphisms on any type:
```
object Endo<T> : Monoid<Endo<T>>
  unit = id<T>
  compose(f g : Endo<T>) = { x : T ↦ f(g(x)) }
```

We can also have type classes of type formers (type-valued functions):
```
data Monad<this F : Type → Type>(
  unit<T>(x : T) : F<T>
  compose<X, Y>(x : F<X>, y : X → F<Y>) : F<Y>
  ...axioms
)
```

The monad of lists is a typical example.
We can reuse the name `List` for this monad making it a companion object
to the `List<_>` type-former.
```
object List : Monad<List>
  ...
```

Structures can have dependently typed carriers:
```
data Category<Ob : Type, Mor : Ob² → Type>(
  unit(O) : Mor(O, O),
  compose<X, Y, Z>(f : Mor(X, Y), g : Mor(Y, Z)) : Mor(X, Z)
  ...axioms
)
```
For every structure on types we can generate the corresponding “displayed” structure on typeclasses
using an operator ( ᵈ) defined in “Displayed type theory” by A. Kolomatskaia and M. Shulman.

To form an example, let's take the typeclass of monoids and introduce the typeclass of monoid homomorphisms
```
data MonoidHomomorphism<X Y : Monoid>(this apply : X → Y, ...axioms)
```

Together, they form a displayed category:
```
object Monoid : Categoryᵈ<Monoid, MonoidHomomorphism>
  ...
```
Once again, we reused the name of the typeclass for the category.

To deal with typeclasses more conveniently, let us introduce the following shorthand notation:
given a typeclass `F : K → U`, let `∀<X : F> Y(X)` mean
```
∀<X : K> ∀(X : F<X>) Y(X)
```
where `X` can mean both the carrier `X : K` and the instance `X : F<T>`, disambiguated by the context.

In our system,
polymorphic proofs and constructions are automatically applicable to all typeclass instances regardless of their size.
For example, assume we have proven the Cayley’s embedding theorem for U-small monoids:
```
cayleyEmbedding : ∀<M : Monoid> MonoidHomomorphism<M, Endo(M)>
```

With the inhabitant cumulativity rule,
it automatically applies also to monoids in any universe U. We have just achieved
that closed-form type former definitions and closed-form proofs
that depend on types parametrically automatically become fully polymorphic
without mentioning universe levels explicitly in any way.

Note that the coinductively defined operator ( ⁺) reminds of another coinductively defined operator on types,
namely the ( ᵈ) operator in [Displayed Type Theory](https://arxiv.org/abs/2311.18781),
which allows
deriving the displayed category of monoids `Categoryᵈ<Monoid, MonoidHomomorphism>(...)` using the type classes above.
Given a proof of, say, Yoneda’s lemma,
for U-small categories, we actually want it to be applicable not only for categories of arbitrary size
but also for arbitrary displayed categories.
This can now be achieved using a simple generalization of the cumulativity rule above.
Ultimately we want to achieve a type theory
(cf. https://akuklev.github.io/reedy-types) where the Yoneda’s lemma can be stated
(and proven) also for ω-categories and will automatically also apply to the displayed ω-category of all ω-categories,
the displayed² ω-category of all displayed ω-categories, and so on.

# Unary parametricity

We have achieved that `id := { x ↦ x }` inhabits `Endo<T>` in all universes,
but we can also extend our type theory
so we can show that `id` is the only closed-form inhabitant of `∀<T> Endo<T>` up to equivalence.
The □-modality together with ( ᵈ) operator from Displayed Type Theory allows □-internal parametric reasoning.
As opposed to type theories with non-modal internal parametricity,
this approach does not contradict LEM maintaining the underlying type theory constructively agnostic.

In 1941, Alonzo Church noticed that natural numbers can be represented as
polymorphic functions of the type `∀<T> (T → T) → T → T`.
All other inductive types also have Church encodings, and 
the type `∀<T> (T → T)` is the Church encoding of the unit type 𝟙.
To establish that `id` is its unique closed-form inhabitant,
it is enough to postulate
that closed-form inhabitants of Church encoded inductive datatypes are exhausted by Church numerals.
Let us see how to formulate that as rules.

Every inductive type `I` comes with a typeclass `Iᴿ<T : U>` of I-structures. For example, for natural numbers we have
```
data ℕᴿ<this T : U>(base : T
                    next : T → T)
```

An I-structure instance is precisely what we need to recursively fold an inhabitant of I.
Thus, typeclasses of I-structures allow formulating the non-dependent elimination rule for inductive types uniformly:
```
( )ᶜ : I → ∀<T : U> Iᴿ → T 
```

Its partial applications are known as Church encodings, e.g.
```
def 0ᶜ = { T :° U, m : ℕᴿ<T> ↦ m.base }
def 1ᶜ = { T :° U, m : ℕᴿ<T> ↦ m.step m.base }
def 2ᶜ = { T :° U, m : ℕᴿ<T> ↦ m.step (m.step m.base) }
...
```

Their type `Iᶜ := ∀<T : U> Iᴿ → T` is known as impredicative (Church-)encoding of the inductive type `I`.

Trivially, both the original and the Church-encoded inductive type form an instance of the typeclass Iᴿ:
```
object ℕ : ℕᴿ<ℕ>
  base: 0
  next: ( ⁺)

object ℕᶜ : ℕᴿ<ℕᶜ>
  base: 0ᶜ
  next: ( ⁺)ᶜ
```

To postulate that the instance ℕ is the initial model,
we need to introduce the induction rule (that is, dependent elimination rule)
for ℕ. Ensuring that closed-form inhabitants of ℕᶜ are exhausted by Church encodings of ℕ elements
is essentially the same rule,
but for the type □ℕᶜ instead of ℕ. To formulate both rules uniformly for all inductive types,
let us apply the ( ᵈ) operator to the typeclass of I-models:
```
data ℕᴿᵈ<T : U>(M : ℕᴿ<T>)<this Ts : T → U>(base : T
                                            next : T → T)
```

Now, the dependent elimination rule `I-elim` reads
```
I-elim(n : I) : ∀<M : Iᴿᵈ I> → M(n)
```
and unary parametricity is given by
```
I-par(n : □Iᶜ) : ∀(R : Iᴿᵈ Iᶜ) → (R n)
```

Now let us see how it works for the unit type 𝟙. Its models are pointed types:
```
data 𝟙ᴿ<this T>(point : T) 
```

We can use 𝟙-par to derive the classical “theorem for free” for the unit type by introducing the following instance:
```
def m : 𝟙ᴿᵈ<𝟙ᶜ> { id : 𝟙ᶜ ↦ (id ≃ { x ↦ x } }
  point: refl

theorem ∀(id : □∀<T : U> T → T) id ≃ { x ↦ x }
  id ↦ 𝟙-par id m
```

We have just shown that the only closed-form inhabitant of the type `∀<T : U> T → T` is `{ x ↦ x }`.

# Classical reasoning and functional logic programming

In the [companion paper](https://akuklev.github.io/modalities) we argue
that it is also possible to introduce a modality dual to □,
namely the S4-possibility modality mapping each type `T` to the spectrum `◇T` of its formal inhabitants,
i.e., inhabitants that can “non-constructively shown to exist”
using choice operator (as in Lean4) and double negation elimination as its special case.
This modality allows classical (non-constructive)
reasoning within ◇-fragment
without compromising computational properties of the underlying type theory such as canonicity,
normalization and decidability of type checking, as well as its compatibility with univalence.
These desirable properties remain intact even if impermeability of the ◇-fragment is violated by
computational Markov Principle (CMP) that allows evaluating Turing-complete computations given
a closed-form classical proof of their non-divergence:
```
 c : Computation<T>   nonDivergence : □◇(c ≠ ⊥)
————————————————————————————————————————————————————
          eval(c, nonDivergence) : T
```

We can easily show that the type `M = W(T : U) ◇T` of iterative classical sets satisfies all axioms
of the classical set theory ZFC, and the reasoning under `◇`-modality satisfies Hilbert axioms
of classical logic, thus our proposed type theory contains a model of ZFC.

# Relation to Shulman’s strong Feferman set theory ZMC/𝕊 

If the universes `U : U⁺ : U⁺⁺ : U⁺⁺⁺ : ···` are also closed under formation of inductive-recursive type families,
it is possible to manually construct closed universes.

The universe `U` is said to satisfy effective reflection property if for any finite set of types and type formers in `U`
it is possible to construct a closed universe `U' : U`
containing all those types and closed under all those type formers, a property that should hold if we allow a
sufficiently general form of inductive-recursive types.

This type theory variant morally corresponds to the strong Feferman set theory ZMC/𝕊
[introduced by M. Shulman](https://arxiv.org/pdf/0810.1279):
If we interpret 𝕊-bounded quantifiers as `M`-bounded quantifiers under the ◇-modality (where `M = W(T : U) ◇T` for
the first universe `U`) and translate unbounded quantification over sets into parametrically quantified propositions
via Zakharyaschev subframe canonical formulae, the translation will turn out to satisfy all axioms of ZMC/𝕊.

Thus, this type theory variant is an extension of ZMC/𝕊.
Presumably, a conservative one: It is possible to exhibit a construction that yields ZMC/𝕊-valued models for
finite fragments of this type theory in ZMC/𝕊 built in such a way that the type-theoretic translation of
the set-theoretic formula φ is only inhabited if the formula φ holds in the model.

Conservativity implies equiconsistency, so it should be possible to adapt the consistency-dependent canonicity proof
for TTobs by [L. Pujet and N. Tabareau](https://dl.acm.org/doi/10.1145/3498693) to show desirable computational
properties claimed above.


# Future work

In 2024, [J. Chan and S. Weirich devised a stratified type theory StraTT](https://arxiv.org/pdf/2309.12164), a
logically consistent type theory that allows speaking of the all-encompassing universe `Type : Type` by stratifying
typing judgments.
This approach parallels [New Foundations](nf), a non-well-founded set theory developed by W. V. Quine in 1937,
the only successful foundational theory able to speak of all-encompassing self-containing universal objects,
which was recently definitely shown to be consistent.
Stratified type theory can probably be extended to allow for the ω-category of all ω-categories, and be used to explore
the boundaries of what can be said about such an object.

One should undoubtedly study how stratified type theory relates to the approach presented above,
and how they both relate to the extended predicative Mahlo universes [recently constructed in MLTT by
P. Dybjer and A. Setzer](https://csetzer.github.io/articles/dybjerSetzerExtendedPredicativeMahloMLTT/dybjerSetzerExtendedPredicativeMahloMLTT.pdf).