Higher Categorical Type Theory
==============================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com), [JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)

Building on the unpublished ideas of C. McBride, we propose a novel extension for univalent Martin-Löf Type Theories (MLTTs) we'll call inductive prototypes, a type-theoretic internalization of Reedy categories. Inductive type families indexed over prototypes provide effective machinery for dealing with syntaxes that include binding, and become indispensable when internalizing the syntax and semantics of type theories themselves. Bidirectional presentations of dependent type theories turn out to be inductive-inductive-recursive definitions. There, the inductive type families of expressions and normal forms are defined simultaneously with inductive prototypes representing their contexts and reduction rules framed as recursive functions on expressions.

Semantically, fibered quotient inductive-inductive type definitions (FQIITs) are effective presentations of weak model categories whose structure-preserving functors correspond to elimination motives. In strong analogy to the functorial semantics of Lavwere algebraic theories, these functors themselves form a category of models, with their natural transformations serving as model homomorphisms.

In a subsequent paper, we hope to establish the existence of initial models in an arbitrary (∞,1)-topos, thus providing a semantics for FQIITs. We assume it to be conditional on the existence of an inaccessible/Mahlo cardinal for small/large FQIITs, respectively, and unconditional for finitary FQIITs. It would also uniformly solve the initiality conjecture for structures admitting an effective bidirectionally algebraic presentation, including [weak ω-categories](https://arxiv.org/abs/1706.02866), [virtual equipments](https://arxiv.org/abs/2210.08663), and (∞,1)-toposes once the [Higher Observation Type Theory (HOTT)](https://ncatlab.org/nlab/show/higher+observational+type+theory) is complete.

# Overview

Natural deduction, an inference rule-based proof calculus can be seen as a precursor of Martin-Löf type theories.
The inference rules of natural deduction serve as a typed generative grammar for proof terms, where the propositions being
proven serve as types of the respective proofs:
```
  a : P     b : Q
————————————————————
 (a, b) : (P and Q)
```
— ‘given a proof term `a` which proves the proposition `P` and a proof term `b` which proves the proposition `Q`, we can construct a proof term denoted `(a, b)` which proves the proposition `P and Q`’. This notation for inference rules still universally used today was first introduced for natural deduction.

Another forerunner of Martin-Löf type theories is Gödel's System T: it's a Simply Typed λ-Calculus `STLC(ℕ)` over the inductive data type of natural numbers. In fact, it's a fragment of all Martin-Löf type theories. There, the types of expressions are data types.

The other constituent of Martin-Löf type theories comes from the first type theory ever introduced, the Russell's theory of types introduced at the very beginning of XX century as a way to deal with Russell's paradox: the type universes. It was long assumed that the universes of data types in Martin-Löf type theories can be seen as data types themselves, but due to a discovery made by Martin Hofmann and Thomas Streicher in 1996 it began to become apparent that it's not the case: the universe of datatypes neccesarily carries additional higher structure, and ignoring this structure makes the theory either undecidable or unsound. Datatypes can be equivalent in inequivalent ways: for instance, the functions `id := { x ↦ x }` and `negate = { tt ↦ ff ; ff ↦ tt}` are nonequivalent automorphisms of the datatype `𝔹 = {tt, ff}`. Starting with the universe `U₀` of datatypes we can construct other “non-data” types, e.g. the universe of pointed data types `Σ(T : U₀) T` or the universe of `U₀`-polymorphic datatypes `U₀ → U₀`. The next type universe `U₀⁺` is obviously also a “non-data” type. Ultimately, Voevodski understood that the types of Martin-Löf type theories represent anima (also known as ∞-groupoids), with data types and propositions being special cases of 0th and -1th truncation levels respectively. Advanced forms of MLTT correctly accomodating higher structure of type universes are now known as univalent (Martin-Löf) type theories. Currently there are several implementations, each with its own minor issues, while the mature one (the Higher Observational Type Theory) is being developed. There, universes come with a recursively defined operation `(≃) : ∀{T : U} ∀(x y : T) U` that computes the type of equivalences of elements inside the types `T` inside the universe.

In fact, type universes are not just ∞-groupoids: taking function types `X → Y` between their elements makes them into ∞-categories. They also come with a recursively defined operation `( ᵈ) : U → U` that computes displayed types representing binary relations `Xᵈ` from the type `X` into other types. These binary relations make type universes into ∞-procategories. As I will show below, for every inductive type `I` we also obtain a ∞-procategory `I-Mod` of its models.^[Technically, the polymorphic type `I-Mod<T : *>` of I-model structures on a type `T` can be itself equipped with a natural structure of a displayed ∞-procategory, yielding a hierarchy of ∞-procategories of its U-small localizations `I-Modᵁ := Σ(T : U) I-Mod<U>`.]

Long before this realization of Voevodski's, enthusiasts of the category-theoretic approach to the foundations of mathematics wondered whether it was possible to generalize MLTTs to accomodate categories as types. Subsequently, approaches were indeed found (cf. [Type Theory for Synthetic ∞-categories](https://rzk-lang.github.io)), but as often happens in the absence of applied motivation, this developments remain rather obscure and hard to grasp. The situation changed in 2021 when C. McBride ([“Cats and Types: Best Friends?“](https://youtu.be/05IJ3YL8p0s)) presented the idea that representing syntaxes with binding begs for inductive data type families indexed over types with directed higher structure. Complementarily, representing dependently-sorted syntaxes requires very-dependent types_ introduced by Hickey and Kopylov [“Formal objects in type theory using very dependent types.”](https://www.cs.cornell.edu/jyh/papers/fool3/paper.pdf) which can be seen as families indexed over types with inverse higher structure.

To make the MLTTs capable of performing structural induction over their own language (i.e. representing their own syntax in terms of inductive types, also known as “eating themselves”), we need to introduce yet another kind of types not fitting into the landscape set by Voevodski, namely types with both directed and inverse higher structure, type-theoretic internalization of Reedy categories we call inductive prototypes.

The raison d'être for inductive prototypes are the inductive families indexed over them. We'll show that these are given by ( ᵈ)-coinductive types recently introduced by Kolomatskaia and Shulman. These are a type-theoretic internalizations of Reedy presheaves, and will turn out to include (semi-)simplicial types and other (weak) test categories commonly used to provide models for higher-categorical structures. We'll show how definition of type families indexed over prototypes can be generalized to functors from prototypes to arbitrary ∞-procategories, including other prototypes which can be seen as simplest synthetic procategories. We expect the universes of Reedy prototypes, as well as functors and families over them to carry structure of iterated ∞-procategories, that is, yet-to-be-defined, ω-procategories.

We conjecture that it would be possible to reproduce and advance developments related to the type theory for synthetic ∞-categories, and ultimately embrace synthetic ω-(pro)categories^[We expect that the approach developed in “Types are Internal ∞-Groupoids” by Allioux, Finster, and Sozeau to extend to show that all HCTT types would turn out to be internal ω-procategories.], a long sought-after category-theoretic foundational framework what turns to be emergent if one seeks for a natural proof calculus capable of structural induction over its own language.

# Remark on notation and terminology

Inductive and coinductive types are introduced with `inductive` and `structure` keywords respectively. Definitions we can simultaneously provide a pronounsible ASCII name and a consise notation.
```
structure Pair(X Y : *) `X × Y`
  fst : X
  snd : Y

inductive Nat `ℕ`
  zero `0`
  next(n : ℕ) `n⁺`
```
where the star `*` denotes the virtual universe of all types, which is used in polymorphic definitions. A word boundary around infix operators, befor prefix operators and after postfix operators are mandatory, since operators may contain alphanumerics in their names as in Agda, only exception being separating punctuation, open punctuation and close punctuation characters, which may only be followed/preceded only by characters of the same unicode category. This allows us to use bracket operators without whitespaces inside, for instance we can define
```
def List<T>.elementAt(idx : ℕ) `this[idx]`
   ...
```
and use it as `foo[idx]`.

We write support both infix and prefix notation for dependent pairs and functions:
```
(x : X) × Y(x) ≡ Σ(x : X) Y(x)
(x : X) → Y(x) ≡ ∀(x : X) Y(x)
```

We'll write lambda expressions as { x : X ↦ y } and anonymous structure instances as {name: value, name: value}.

In many cases, the same identifier means both a type/type family and their companion object. To disambiguage we'll use special notation `foo<Bar>` for typal parameters. An overloaded identifier should resolve to companion object unless used as a type annotation `: T` or as a typal parameter `List<T>`.

We will allow using type classes (structures parametrized by a type `T : *` or a type family `Ts : I → *`) on the right side of the colon as a shorthand. Consider the following type class
```
structure Magma<T>
  (•) : T → T → T
```

Now if we write `def f<M : Magma>(x y z : M)` it desugars into `def f<M : *>(implicit M : Magma<M>, x y z : M)`. The name `M` is overloaded and means either a type or its companion object depending on the usage context.


# Inductive types and ∞-procategories of their models

Let us begin with the definition of infinite sequences:
```
structure Sequence<T : *> `ℕ → T`
  head : T
  tail : Sequence<T>
```

Given sequences of types, we can also define dependently-typed sequences:
```
structure Sequence<Ts : ℕ → *> `ℕ → Ts`
  head : Ts.head
  tail : Sequence<Ts.tail>
```

Coinductive type definitions without dependencies generate (or presume) inductive definitions for the type of their observables. The types above share natural numbers as their observables:
```
inductive ℕ
  0 : ℕ
  ( ⁺) : ℕ → ℕ
```

Every inductive type comes with a ∞-procategory of its models. An inductive definition does not only generate the type (ℕ) itself, but also coinductive dual, the structure of a ℕ-model on an arbitrary type `T`.
```
structure ℕ-Mod<T : *>
  base : T
  next : T → T
```
and its canonical instance
```
instance ℕ-obj : ℕ-Mod<ℕ>
  base: 0
  next: ( ⁺)
```

Models of single-sorted algebraic theories arise as models for quotient inductive types, for example monoids arise as models for the following type:
```
inductive MonTh
  e : MonTh
  (∘) : MonTh → MonTh → MonTh

  unitorL : x = e ∘ x
  unitorR : x = x ∘ e
  associator : (x ∘ y) ∘ z = x ∘ (y ∘ z)
```

To each type we can apply the ( ᵈ)-operator to obtain its displayed version. Displayed models for inductive types have the form
```
structure ℕ-Modᵈ <M : ℕ-Mod> <Ts : M → *>
  base : Ts(M.base)
  next : ∀{n : M} Ts(n) → Ts(M.next n)
```
allowing do define the type of induction motives and the induction operator:
```
instance ℕᴹ : ℕ → *
  ℕ-Modᵈ ℕ-obj

ℕind<P : ℕ → *> : ℕᴹ → ∀(n : ℕ) P(n)
```
 
For each model `M : ℕ-Mod`, the inhabitants `Pm : ℕ-Modᵈ<M>` are promorphisms (many-to-many corresponcences, sometimes also called weak homomorphisms) on `M` with the target given by
```
instance target : ℕ-Mod<M × Pm>
  base: (M.base, Pm.base M.base)
  step: { n : M, x : (Pm n) ↦ (M.step n, Pm.next (M.next n) x) }
```

We can single out homomorphisms as the functional (= many-to-one) promorphisms `Σ(src : ℕMod<T>, pm : ℕModᵈ src) (f : ∀(n) (m : (pm n)) × ∀(n' : pm n) n ≃ m`, making the type of ℕ-models into a ∞-precategory (Segal type), which turns out to be a ∞-category (Complete Segal type) as it is well-known that the equivalences `(≃)<ℕ-Mod>` of ℕ-models correspond to their isomorphisms.

The presented construction generalizes to all inductive types, quotient inductive types and (quotient) inductive(-inductive-recursive) type families. We expect them to work mutatis mutandis for familes over inductive prototypes and positive fibered induction-recursion into arbitrary procategories.

# Basics of inductive prototypes

## The motivating example

A homogeneous pair `p : T × T` can be equivalently described as a function `p : 𝔹 → T` on the type with two values.
Heterogeneous pairs `p : X × Y` correspond to dependent functions `f : 𝔹 → { ff ↦ X; tt ↦ Y }`. What about dependent pairs?

With inductive prototypes we can do that! We'll need the following one:
```
prototype 𝔻
  fst : 𝔻
  snd : 𝔻
  snd [dep⟩ fst
```

The type of “functions” on 𝔻 requires the target to be a procategory `U : *̃`, a mere type `T : *` is not enough:
```
structure 𝔻-Func<U : *̃> `𝔻 → U` 
  fst : U
  snd : (dep : this.fst) →ᵁ U
```

(The operator (→ᵁ) referes to hom-types of the procategory U.)

And here is the dependent version:
```
structure 𝔻-Func<Ts : 𝔻 → *> `𝔻 → Ts`
  fst : Ts.fst
  snd : (dep : this.fst) →ᵀˢ Ts.snd
```

Now we dependent pairs `p : (x : X) × Y(x)` can be expressed as very dependent functions:
```
f : 𝔻 → { fst ↦ X, snd ↦ Y(f(fst)) }
```

Using this approach, we can define a carrier prototype for very dependent sequences:
```
prototype Δ⁻
  0    : Δ⁻
  ( ⁺) : Δ⁻ → Δ⁻

  (n⁺) [dep⟩ n

structure Δ⁻-Func<U : *̃> `Δ⁻ → U`
  head : U
  tail : (dep : this.head) →ᵁ Δ⁻-Func<U>

structure Δ⁻-Func<Ts : Δ⁻ ↦ *> `Δ⁻ → Ts`
  head : Ts.head
  tail : (dep : this.head) →ᵁ Δ⁻-Func<Ts.tail>
```

We have just defined the very-dependent function types initially introduced by Kopylov et al. 

Inductive prototypes restore the symmetry between induction and coinduction. For every coinductive type `S` we can generate an inductive prototype `I` of observables, so that elements `f : T` are functions on `I`, and for every prototype `I` we'll have a displayed coinductive type `I → *` of type families over `I` so that functions `f` on `I` can be typed as `f : I → Ts` for some `Ts : I → *`.

## Handling the contexts and telescopes

Definition of a prototype `I` automatically generates its truncations, the prototypes `↓n` for `n : I`.
In the particular case of `n : Δ⁻`, truncations can be used to describe dependent tuples `t : (↓n)→ Ts`
of length `n`, where `Ts : (↓n)→ *` are the type telescopes of length `n`.

When describing dependent syntaxes with bindings, we introduce types `Expr<ctx : Ctx>` of expressions
in a given context. Contexts are almost the same as telescopes `Ts : (↓n)→ *`, with a minor but very
important difference: an expression `e : Expr<ctx : Ctx>` should be liftable to a larger context
`ctx' : Ctx`, along thinnings `thn : ctx ⊂ ctx'`.

We will define a prototype Δ that extends Δ⁻ by inverse arows representing thinnings `m ⟨thn] n`, generating
embeddings `thn : ↓n ⊂ ↓m` and hence `thn : (ctx : (↓n)→ *) ⊂ (ctx' : (↓m)→ *)`, and also
`thn : Expr<ctx> ⊂ Expr<ctx'>`, i.e. for every `e : Expr<ctx>` we'll have `ap ⟨thn] e : Expr<ctx'>`.
```
prototype Δ
  0    : Δ
  ( ⁺) : Δ → Δ
 
  (n⁺) [dep⟩ n

  (n⁺) ⟨t(f : ↓n)] (f.target)⁺
  (n⁺) ⟨f(f : ↓n)] f.target
```
As arrows are constructors as well, they must act not only on plain constuctors but on other arrows of the same direcion,
which defines precomposition for dependency arrows and postcomposition for embedding arrows, making composition of arrows
definitionally/computationally associative. Differently from McBride, we only provide constructors for non-identity arrows.

```
structure Δ-Func<U : *̃>
  ..TODO

structure Δ-Func<Ts : Δ→ *̃>
  ..TODO
```

**TODO** Say how to understand prototypes as procategories themselves, and how the types ↓n also form
procategories, show examples of functors and show how they form procategories, define products of prototypes
and show how bifunctors are compatible with currying.

## Lax monoids

Let us introduce the type of lists of natural numbers indexed by their sum:
```
inductive SumsTo : ℕ → *
  nil : SumsTo 0
  cons : ∀{n : ℕ} (head : ℕ, tail : SumsTo n ) → SumsTo (head + n)
```

Now we can write a function `unflatten` that takes a `list : List<T>` and
an additive decomposition `s : SumsTo(list ▸length)` into a `listOfLists : List<List<T>>` with
`listOfLists ▸flatten = list` and `listOfLists ▸map {.length} = s`.

Now we can define the following
```
prototype LaxTh
  compose : List<LaxTh> → LaxTh

  compose(l) ⟨parenthesize(s : SumsTo(l ▸length))] compose(l ▸unflatten(s))
```

The models `LaxTh-Mod` for this prototype are the unbiased lax monoids.


## Categories as models for an inductive type

There can be more then one dependency between two inhabitants of an inductive prototype:
```
prototype Δ¹⁺
  ob : Δ¹⁺
  mor : Δ¹⁺
  mor [source⟩ ob
  mor [target⟩ ob
```

A family of types `T : Δ¹⁺ → *` has the following structure
```
structure `Δ¹⁺ → *`
  Ob : *
  Mor : (source : Ob, target : Ob) → *
```

Now let us define the following indexed quotient-inductive type family:
```
inductive CatTh : (i : Δ¹⁺) → *
  id : ∀{o : CatTh ob} (CatTh mor){source: o, target: o}
  (▸) : ∀{x y z : CatTh ob} (CatTh mor){source: x, target: y}
                          → (CatTh mor){source: y, target: z}
                          → (CatTh mor){source: x, target: z}

  unitorL : ∀{x y} f = id ▸ f
  unitorR : ∀{x y} f = f ▸ id
  associator : ∀{f g h} (f ▸ g) ▸ h = f ▸ (g ▸ h)
```

Now consider the type of models for this type:
```
structure CatTh-Mod<Ts : Δ¹ → *>
  id : ∀{o : Ts.ob} → Ts.mor{source: o, target: o}
  (▸) : ∀{x y z : Ts.ob} (Ts.mor){source: x, target: y}
                       → (Ts.mor){source: y, target: z}
                       → (Ts.mor){source: x, target: z}
  ... subject to unitality and associativity
```

That's precisely the definition of a category!
Well, actually, a precategory because we do not yet require univalence. But we can require univalence an embedding arrows we forgot in the definition
of our prototype:
```
prototype Δ¹
  ob : Δ¹
  mor : Δ¹
  mor [source⟩ ob
  mor [target⟩ ob

  ob ⟨よR] mor       
  ob ⟨よL] mor
  [source⟩⟨よR] ↦ [source⟩
  [target⟩⟨よL] ↦ [target⟩
```

Now given `Ts : Δ¹ → *`, for every `o : Ts.Ob` we'll have Yoneda embeddings
```
o⟨よR] : ∀(target : Ts.Ob) Ts.Mor(source: o, target)
o⟨よL] : ∀(source : Ts.Ob) Ts.Mor(source, target: o)
```
that allow to derive 
```
univalence : ∀{X Y : Ts.ob} (a ≃ b) ≃ Σ(f : Ts.hom{source: X, target: Y})
                                      Σ(g : Ts.hom{source: Y, target: X})
                                      (f ▸ g = id) and (f ▸ g = id)            
```

Structures defined as models for an inductive type compose extremely well. Consider `Δ¹Fam`-valued models `LaxTh-Mod<Δ¹Fam>` of the lax monoid prototype, and then consider the `LaxTh-Mod<Δ¹ → *>`-valued models of `CatTh`. This way we obtain lax monoidal categories `CatTh-Mod<LaxTh-Mod<Δ¹ → *>>`!

The other nice thing is that since we have defined categories as models for an inductive type, we automatically have the structure of a displayed category on categories:
```
Cat : Catᵈ
```
Furthermore we can iterate, and thus `Catᵈ : Catᵈᵈ` etc. And since constructions and proofs also can be lifted, any statement we have proven for all small categories `prf<C : Cat>` also can be applied to displayed categories, say like the category `Grp : Catᵈ` of all groups and the category of all categories `Cat : Catᵈ` itself. Seems like dream of size-agnostic category theory came true. Well, except we want to have the same for ω-categories `ωCat : ωCatᵈ : ωCatᵈᵈ : ···`.

# Higher structures

Defining categories required a prototype with only two inhabitants `ob hom : Δ¹`. For ω-categories we will a countably infinite hierarchy of those. Let us start with a strict ω-categories, which use the iterated version G (Globes) of Δ¹:
```
prototype G⁺
  0 : G⁺
  ( ⁺) : G⁺
  (n⁺) [source⟩ n
  (n⁺) [target⟩ n

  [source⟩[target⟩ ↦ [source⟩
  [target⟩[source⟩ ↦ [target⟩

structure `G⁺ → *`
  Ob : *
  Mor : (source : Ob, target : Ob) → G⁺Fam
```

A tower of cell types `Ts : G⁺ → *`
```
objects      Ts(0)
morphisms    T(1)(source₁ target₁ : Ts(0))
2-morphisms  T(2)(source₁ target₁ : Ts(0))(source₂ target₂ : Ts(1)(source₁, target₁))
3-morphisms  T(3)(source₁ target₁ : Ts(0))
                 (source₂ target₂ : Ts(1)(source₁, target₁))
                 (source₃ target₃ : Ts(2)(source₁, target₁)(source₂ target₂))
...
```

With this prototype we can define the indexed inductive type family `ωStrCatTh : G⁺ → *` so that strict pre-ω-categories arise
as the models for these inductive type families, `ωStrCatTh-Mod<Ts : G⁺ → *>`. By using the prototype G which extends G⁺ by
including Yoneda-embeddings, we obtain the strict ω-categories `sωCat<Ts : G → *> := ωStrCatTh-Mod<Ts>`.

# Beyond globes: The infamous semi-simplicial types

The ideas presented above were partially developed in 2015-2017 and finished up to globes by 2021. However, I was not able
to develop a systematic rule to derive structures of `I`-families for prototypes `I` with dependence structure beyond globes. Unfortunatelly, 
globes are not sufficient to develop general (weak) versions of higher algebraic structures such as ∞-categories or even unbiased lax monoidal
categories, let alone weak ω-categories. For “nice” definitions we need to form families over arbitrary inductive prototypes, but the bare minimum
to achieve workable versions are the type families over the opposite `Δ°` of the prototype Δ we have already introduced earlier to work with contexts.
Type families over the prototype Δ° are known as presheaves over the simplex category Δ or simplicial types. To deal with non-univalent versions of
higher structures, the semi-simplicial types `Ts : Δ⁺° → *` would be sufficient.

Recently, A. Kolomatskaia and M. Shulman have achieved a striking breakthrough by defining the semi-simplicial types using coinduction in conjunction with `( ᵈ)`-operation forming displayed types:
```
structure `Δ⁺° → *`
  head : *
  tail : this.head → (Δ⁺° → *)ᵈ<this>
```

With enough combinatorics, it is possible to generalize the approach for any prototypes. In particular, for any ℕ-like prototype I (the one with constructors like `0` and `( ⁺)`) we'll be able to derive the coinductive duals in the form
```
structure I-Func<U : *̃>
  head : U
  tail : F<this.head> →ᵁ (I-Funcᵈ< H<this> > U)
```
- where `F` and `H` are some static type formers. For example, in the case of globes `G`, we'd have `H<T> := 𝔹`, `H<T> := Unit`. To establish this fact we'll first construct the prototypes of observables for coinductive types as above, and then discuss how to reverse-engineer `G` and `H` to obtain any desired prototype.

## Prototype definitions as inductive-recursive definitions with compile-time checked conditions 

A prototype `T` is an inductive type `|T| : *` defined mutually with two following inductive-recursive types:
```
Deps[T] : *, .target : T, .compose : (x : Deps[.target]) -> Deps[T] with .target ≡ x.target
Embs[T] : *, .source : T, .compose : (x : Embs[.source]) -> Embs[T] with .source ≡ x.source
```
The definitional equalities must be checked in compile-time. It is only possible if `t.target` and `t.source`
are structurally smaller then `t`. It ensures that the arguments `x` of the functions precompose and postcompose
come from a type that has already been defined, its constructors are known and values of .to and .from on resulting values can be
explicitly computed. Since compositions of dependencies and embeddings are represented by composition of functions,
it is definitionally associative. The involution T° on prototypes simply exchanges dependencies and embeddings.
The prefix operator (↓ ) generates a derived downward prototype for each element `t : |T|` consisting only of
those elements of `|T|` that t can be reduced to, and their respective dependencies. The universe of derived
downward prototypes comes for a fixed prototype `T` comes with a prototype structure induced by embeddings
and embeddings in `T` acting elementwise.

## Definitions of inductive type families indexed over prototypes
**TODO**

## Induction over prototypes and procategories of prototype models
**TODO**

# Inductive prototypes and algebraic theories

## Lavwere algebraic theories

School algebra is about transforming expressions. We learn basic operations such as addition and multiplication and basic identities they satisfy such as associativity, commutativity and distributivity. We compose basic operations to form expressions (= derived operations), and learn how to transform them by composing identities. 

High school algebra only deals with operations on some kind of numbers, in propositional logic we deal with operations (conjunction, disjunction, negation) on propositions. Actually, one can study operations abstractly, i.e. without specifying what they are intended to act on. That's precisely what universal algebra does: it studies finitely-generated sets of operations satisfying finitely-generated sets of identities.

Classical universal algebra usually deals with the case when operations are generated by constants, unary, and binary operations, operands being of the same sort as values. It is possible to generalize to the case with multiple sorts, e.g. vectors and scalars.

To generalize from propositional logic to predicate logic, we need an infinite number of sorts, namely the sort 0 of propositions, the sort 1 of propositions with one variable (unary predicates) and so forth for propositions with any finite number of variables (`n`-ary predicates). Quantifiers `∀` and `∃` bind one variable and thus decrement the sort of their operand. To state it precisely, quantifiers are not just two operations but an infinite families of operations: for any natural numbers `n < m` there is a specific variant of that accept m-ary predicates binding their `n`th hole. Binary operations like the conjunction and disjunction also turn into an infinite family. For unary predicates `R(x)` and `Q(x)` each binary operation * has two variants: it can either join the variables of predicates `R(x) * Q(x)` or leave them distinct `R(x) and Q(y)`. In the general case of an n-ary and and m-ary predicate, there will be many ways to join variables, but it is not hard to derive them all algorithmically. Thus, the set of operations is not finitely-generated anymore, but effectively generated (can be generated by an algorithm). The same applies to the set of identities, since we finite number of identities cannot govern an infinite number of primitive operations.

**TODO:** Show how to handle this example using the inductive prototype Δ⁺!

The gadget to deal with predicate logic algebraically is known as effectively generated Lawvere algebraic theory: it has a subcountable set of sorts, and effectively generated sets of operations and identities. As opposed to the case of finitely-generated theories, presenations of effectively generated ones include algorithms producing operations and identities, which have to be checked for termination and producing expressions of matching sorts, which requires some heavy computational machinery and is almost impossible to do by hand for nontrivial theories.

## Dependent sorts

We already discussed operations acting on numbers, propositions, and predicates. Let us now consider operations acting on even more complex entities: proofs and programs.

A proof calculus is a two-level system somewhat like vector spaces having the sort of vectors and the sort of scalars. The first layer is the layer of propositions and predicates we have already described as a Lawvere theory. In addition there will be the layer of proofs. Similar to propositions, we'll have sorts of proofs with `n` variables for each `n`. But it is more complicated than that. The sort of proof has to include the proposition or predicate being proven! Otherwise we cannot state the most basic operator on proofs `p ▸ q` that composes a proof of `A` and a proof of `A implies B` into a proof of  `B`. Sorts of proofs with `n` variables have to be of the form `Prf(p)`, where `p`is an `n`-ary predicate. We need to have dependent sorts: a feat Lawvere theories cannot accomodate.

In Lawvere algebraic theories, sorts are mere labels governing which expressions can be plugged together. An expression can be plugged into a hole of another expression if the sorts of the expression and the hole are identical. Sorts are syntactical entities, so it's OK to talk about them being identical, after all syntactical entities can be faithfully numbered and “identical” simply means “the same number”.

When generalising to allow value-dependent sorts `S(x)` we run into a problem. Values are semantic entities, so they can be equal without being represented by identical expressions. How can we even talk about sorts being identical or not if they depend on values?

Fortunately, values `x` occurring as sort arguments `S(x)` rules are not just any values, but values given by expressions of the very same theory, so it might be possible to provide an algorithm that computes canonical forms `|x|` so that equal values are mapped to identical normal forms. The operation `|_|` is where the computational aspect really comes into play.

For many sorts of interest it is is not possible to algorithmically extract canonical forms from values. For instance this is impossible for `n`-ary predicates with `n > 0`: word problem for their sorts is semiundecidable in the theory of predicate logic. If two predicates are indeed equal, systematic application of all possible identities will eventually find a path from one to another, but if they are distinct, this process will simply proceed indefinitely; we cannot in general prove distinctness of two predicates due to halting problem, which precludes existence of canonical forms. In such cases we can assign non-canonical normal forms `|_|` to values and find or introduce a (doubly dependent) sort `Id(a, b)` inhabited by identification paths from `a` to `b`. In our case we luckily already have one: two predicates can be shown equivalent precisely if we have a proof of the sort `Prf((A implies B) and (B implies A))`. This sort has to have property that it allows to plug expressions of the sort `Prf(A)` into holes of the sort `Prf(B)` if we have `p : Id(x, y)`, that is `p : Prf((A implies B) and (B implies A))`.

In simple cases can have an algorithm that syntactically transforms expressions of the sort `Prf(A)` into expressions of the sort `Prf(B)`. This is unfortunatelly not alwasy possible. What turns out to be possible is an algorithm that syntactically transform the recipient expression with hole of the sort `Prf(A)` into an equivalent expression with the corresponding hole of the sort `Prf(B)` owing to additional flexibility that this syntactic transform can also change the resulting sort of the expression into an equivalent but non-identical one. Lifting expressions along identification paths gets really tricky when we work with systems where sorts can depend on values themselves being of a dependent sort. Luckily there is a whole well-developed area of mathematics dealing with lifting equivalences over equivalences — the abstract homotopy theory. Below we will establish that effective algebraic theories with dependent sorts correspond to weak model categories the same way as Lawvere algebraic theories correspond to finite-product categories.

**TODO:** Show a real example that employs induction-recursion

## Internal types and Bidirectionalism

The proof calculus we outlined above is internally untyped, i.e. the variables bound by quantifiers do not have type declarations. Requiring a variable to have certain data type can be implemented by logical predicates, like this `(∀(n) isNat(n) implies P(n) )`. 

If we want our proof calculus to support proofs by induction, we have to use typed variables instead:
```
 P : Prop(ℕ)    base : P(0)    step : (P(n) implies P(n + 1))
——————————————————————————————————————————————————————————————
  ℕind(P, step, base) : ∀(n : ℕ) P(n)
```

To accomodate induction we need a much more complicated system of dependent sorts featuring a sort of (internal) data types and a substantial amount of infrastructure. Fortunatelly, the flexibility provided by the notion of dependent sorts and normalization maps `|_|` turns out to be flexible enough even to internalize itself. (Apart from algorithm totality-checking. If a system contains a total “programming language” inside, it cannot be powerfull enough to encode the normalization maps used for defining the system. The only way for a system striving to define its own syntax inside, is to use “levitating” algorithms for the normalization maps, which are interpreted (and termination-checked) by the ambient system and look as black boxed from inside the system, as first introduced in “The Gentle Art of Levitation” by J. Chapman.)

To present algebraic theories as above we'll have to define inductive type families like `P(context)`,
where context is list of types of variables the predicate uses. Typically, we'll have to define the
internal type `Ty` of variable types together with an evaluation function `|_| : Ty -> *`, both defined
mutually with type family `P` and what not.

## Handling internal dependent types
That's how we can define the type of contexts from the type `Ty` naïvely:  
For `n : ℕ` let us use the notation `↓n` for the type of size n usually known as `Fin n`. Given a vector of
types `Con := (↓n) → Ty` we can define a tuple of values of the respective types as `vals : (↓n) → Con`.

By using the prototype Δ instead of ℕ we can deal with dependencies and thinnings!

**TODO:** Provide an example, perhaps ML71 with `Type : Type`.

# Semantics of type families over prototypes

## Example of unbiased lax monoidal categories
**TODO**

## The doctrine of weak monoidal categories
**TODO**

## Constructing a weak monoidal category from an FQIIT-definition
**TODO**

## Initial algebra semantics for FQII type families
**TODO**

