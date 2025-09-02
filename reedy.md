Reedy Types and Dependent Type Families
=======================================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com), [JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)

Building on the unpublished ideas of C. McBride and ideas from
[“Displayed Type Theory and Semi-Simplicial Types”](https://arxiv.org/abs/2311.18781)
by A. Kolomatskaia and M. Shulman,
we propose a novel extension for univalent Martin-Löf Type Theories (MLTTs) for internalizing Reedy categories.

Indexing and fibering over Reedy types provide effective machinery to deal with syntaxes that include binding
and become indispensable when internalizing the syntax and semantics of type theories themselves.
In this way, we obtain convenient tooling and uniformly establish the existence of initial models for structures
like [weak `ω`-categories](https://arxiv.org/abs/1706.02866), [virtual equipments](https://arxiv.org/abs/2210.08663),
(∞,1)-toposes
once the [Higher Observation Type Theory (HOTT)](https://ncatlab.org/nlab/show/higher+observational+type+theory)
is complete.

Finally, this approach should lead to a
[homoiconic](https://homotopytypetheory.org/2014/03/03/hott-should-eat-itself/) univalent type theory,
i.e. one capable of representing its syntax as an inductive family
and thus performing structural induction over it.

# Why do we need dependent type families?

Finitary type families abstractly embody formalized languages.
For example, consider the following simple language of arithmetic
and logical expressions:^[This paper is written in literate dependent Kotlin, see \url{https://akuklev.github.io/kotlin/kotlin_literate.pdf}. We use an Agda-like syntax for inductive definitions, except using angle brackets for type parameters and irrelevant function parameters, allowing to concisely introduce records as inductive types with a unique generator.]
```kotlin
|\textbf{\textcolor{dgreen}{data}}| ExpressionKind
Numeric
Logical

|\textbf{\textcolor{dgreen}{data}}| Expr : ExpressionKind → Type
Literal(n : Int)         : Expr Numeric
Sum(a b : Expr Numeric)  : Expr Numeric
Mul(a b : Expr Numeric)  : Expr Numeric
Div(a b : Expr Numeric)  : Expr Numeric
Pow(a b : Expr Numeric)  : Expr Numeric
Neg(a : Expr Numeric)    : Expr Numeric
Log(a : Expr Numeric)    : Expr Numeric

Eq(a b : Expr Numeric)   : Expr Logical
Lt(a b : Expr Numeric)   : Expr Logical
Or(a b : Expr Logical)   : Expr Logical
Not(a : Expr Logical)    : Expr Logical
```

Dependent type families allow scaling up this approach to languages with scoped binders
(variables, type definitions) including general-purpose programming languages themselves.

Data types defined that way are inhabited by abstract syntax trees
corresponding to finite expressions of the language, and they come
with a recursive descent analysis operator enabling
type-driven design of correct-by-construction analysers and interpreters facilitating
robust type checking, compilation, static analysis, and abstract interpretation in general.

As for IDEs, inductive type families enable designing biparsers for
those languages, parsers that maintain a one-to-one mapping
between the source code and the respective annotated abstract syntax
tree, enabling both fast incremental reparsing and mechanized refactoring.

To represent languages with typed variables, one introduces the type `Ty`
representing variable types of the language, and the type family `Tm (ctx : `{$^*$}`)`
of terms in a given context given by a list of types.
Definition of term substitution can be vastly simplified
if one recasts the type of contexts as a size-indexed type family `Ctx (size : LΔ)`,
which requires the notion of lax types (such as `LΔ`) to enable context extension.
In case of dependently typed languages, `Ty` is not a type, but a type family `Ty (c : Ctx)`,
where the contexts are iterated dependent pairs
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Ctx
Empty : Ctx
Append(prefix : Ctx, head : Ty prefix)
```
To define substitution, we have to recast `Ctx` as a simplicial type family `Ctx (shape : Δ)`,
which requires the notion of Reedy types (such as `Δ`) that enable selection of subcontexts.
Bidirectionally typed languages split terms into a type family of normal forms satisfying a given type `Nf (c : Ctx, t : Ty c)` and a fibered family of reducible expressions
that synthesize their types and normal forms `Rx : (c : Ctx)ᵈ ↓ (ty : Ty c, Nf (c, ty))`.

# Setting and basics

Our base theory will be the Higher Observational Type Theory with an infinite tower of cumulative
universes `Type : Type⁺ : Type⁺⁺ : ···` featuring □-modality-based polymorphism.

All universes will be closed under dependent product, dependent sum types, and
quotient inductive types.

The simplest types of this kind are the finite datatypes (also known as enums)
defined by enumerating their possible values:^[Fancy aliases for plain identifiers can be introduced in backticks. See \href{https://akuklev.github.io/kotlin/kotlin_academic.pdf}{\texttt{kotlin\\_academic.pdf}} for details.]
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Bool
  False   `ff`
  True    `tt`
```
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Unit
  Point   `()`
```
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Void {}    // no elements at all 
```

We can generalize them to sum types
by allowing indexed families of possible values:^[We omit the type of `X` in `Possibly<X>`, because parameter types can be omitted if inferrable.]
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Possibly<X>
  Nothing
  Value(x : X)
```

Each inductive type comes along with a dual typeclass:^[Typeclasses are introduced as records with a marked (by `this`), possibly higher-kinded, typal parameter, but turn into a subtype of their marked parameter’s type, e.g. `Boolᴿ <: Type`, so every `T : Boolᴿ` is both a type and an instance of `Boolᴿ<T>`, which does not introduce ambiguities since types and families cannot have fields, while typeclass instances are records and consist from their fields. See \href{https://akuklev.github.io/kotlin/kotlin_typeclasses.pdf}{\texttt{kotlin\\_typeclasses.pdf}} for details.]
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Boolᴿ<this Y>(ifTrue  : Y,
                   ifFalse : Y)
```
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Possiblyᴿ<X, this Y>(ifNothing : Y,
                          ifValue(x : X) : Y)
```

Instances of these typeclasses represent by-case analysis of the respective sum types.

Inhabitants of inductive types `x : T` can be converted into functions^[Result type in definitions can be omitted in assignment-style definitions as here.]
(known as Church representations) that
evaluate their by-case analysers: `xᶜ : ∀<Y : Tᴿ> Y`:
```kotlin
|\textbf{\textcolor{dgreen}{def}}| False<Y : Boolᴿ>ᶜ = Y.ifFalse
|\textbf{\textcolor{dgreen}{def}}|  True<Y : Boolᴿ>ᶜ = Y.ifTrue
```
```kotlin
|\textbf{\textcolor{dgreen}{def}}| Nothing<X, Y : Possiblyᴿ<X>>ᶜ        = Y.ifNothing
|\textbf{\textcolor{dgreen}{def}}|   Value<X, Y : Possiblyᴿ<X>>(x : X)ᶜ = Y.ifValue(x)
```

What if we want to return values of different types for `True` and `False`?
We can first define a function from booleans into types `Y : Bool → Type` and then a dependent case analyser
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Boolᴹ<this Y : Bool → Type>(ifTrue  : Y True,
                                 ifFalse : Y False)
```

To apply dependent case analysers to inhabitants of the respective type, we
need a special operator called induction for reasons explained below:
```
I-ind<Y : Iᴹ>(x : I) : Y(x)
```

Non-finite inductive types admit (strictly positive) recursion in type definitions,
enabling such types as natural numbers, lists, and trees:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Nat `ℕ`
  Zero `0`
  PosInt(pred : ℕ) `pred⁺`
```
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Int `ℤ` :> Nat
  NegInt(opposite : PosInt)   // So, Int is either Nat or NegInt
```
```kotlin
|\textbf{\textcolor{dgreen}{data}}| List<T> `T|$^*$|`
  EmptyList : T|$^*$|
  NonEmptyList(head : T, tail : T|$^*$|) : T|$^*$|
```
```kotlin
|\textbf{\textcolor{dgreen}{data}}| BinTree<T>
  Leaf
  Node(label: T, left : BinTree<T>, right : BinTree<T>)
```
```kotlin
|\textbf{\textcolor{dgreen}{data}}| VarTree<T>
  Leaf
  Node(label: T, branches : VarTree<T>|$^*$|)
```
```kotlin
|\textbf{\textcolor{dgreen}{data}}| InfTree<T>
  Leaf
  Node(label: T, branches : Nat → InfTree<T>)
```

All above examples except infinitely branching trees are finitary inductive types,
i.e. inductive types with the property that all of their generators have a finite
number of parameters, and all these parameters are of finitary inductive types.
Finitary inductive types may be infinite, but their inhabitants can be encoded
by natural numbers or equivalently finite bit strings.

Finitary inductive types embody single-sorted languages.
They are inhabited by abstract syntax trees corresponding to finite expressions
of the language formed by their generators.

“Case analysis” for the type of natural numbers provides n-ary iteration operator:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Natᴿ<this Y>(base : Y,
                  next(p : Y) : Y
```
Analysing a natural number `n` by `R : Natᴿ<Y>` yields `nᶜ<R>() = (R.next)ⁿ R.zero`,
allowing to iterate arbitrary functions given number of times. In general,
“case analysis” turns into “recursive descent analysis”. For lists and trees we
obtain the respective fold operators.

Type-valued functions on natural numbers `Y : Nat → U` can encode arbitrary predicates,
and a dependent `Nat`-analyser `Natᴹ<Y>` encodes an induction motive: it establishes
a proof of the base case `Y(zero)` and the inductive step `Y(n) → Y(n⁺)`.
Dependent case analysis operator turns induction motives into to proof the predicate
for all natural numbers, that is why it is also known as induction operator.
The presence of induction witnesses that inductive types contain only inhabitants that
can be obtained by finite compositions of their generators.
Which is also the reason why data types described in terms of their generators are
called inductive types.

While ordinary inductive types are freely generated,
quotient inductive types additionally contain generators of identities between their inhabitants,
so we can define rational numbers:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Rational(num : Int, den : PosInt) `ℚ`
  expand<num, den>(n : PosInt) : Rational(num, den) = Rational(num · n, den · n)
```
Here, in addition to listing generators, we require that some actions
on generators (expanding the fraction or permuting list elements) must
be irrelevant for all predicates and functions defined on these types.

An inductive definition may simultaneously define a family of types dependent on one another.
This is not limited to finite families: we can allow type families indexed by an arbitrary type `J`:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| SizedList<T> : Nat → Type
  EmptySizedList : Vec<T> 0
  NonEmptySizedList<n>(head : T, tail : SizedList<T> n) : SizedList<T> n⁺
```
This way we can also introduce finite types of a given size (used as an implicit conversion):
```kotlin
|\textbf{\textcolor{dgreen}{data operator}}| asType : Nat → Type
  Fst<size> : size⁺
  Nxt<size>(prev : size) : size⁺
```
Now we can use numbers as types which come in handy for advanced collections:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| HList<T : Nat → Type><n : Nat>(items : n → T n)    // Heterogeneous lists
```
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Collection<T><size : Nat>(items : size → T)        // Finite multisets
  permute<size, items>(p : size!) : Collection(items) = Collection(items ∘ p)
```
```kotlin
|\textbf{\textcolor{dgreen}{data}}| FinSet<T><size : Nat>(items : size → T)            // Finite sets
  multipermute<n, m, items>(inj : n ↣ m) : FinSet(items) = FinSet(items ∘ inj)
```
where `T!` is the type of automorphisms (permutations) of the type `T`, `X ↣ Y` the type of injections.

# Lax types: internalizing inverse categories

Consider the quotient inductive type of eventually-zero sequences:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| EvZeroSeq
  Zeros : EvZeroSeq
  Prepend(head : Nat, tail : EvZeroSeq)
```
```kotlin
  expand : Prepend(0, Zeros) = Zeros
```

As we have seen above, we can turn the type of lists to a size-indexed type family over `Nat`,
but we cannot make `ZeroEndingSequence` into a type family over `Nat` because
`extend` generates equality between “lists” of different sizes.
We need a “lax” index type instead of `Nat`:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| LaxNat(n : Nat) `LΔ` : ℓType
  LaxNat(n) [m : Nat⟩ LaxNat(n + m)
  [n⟩ [m⟩ ↦ [(n +) m⟩
```

To each universe `U` we'll have an associated lax universe `ℓU` occupied by the types like the one above.
Lax inductive types are stratified directed counterparts of quotient inductive types.

Ordinary types `T` : `U` admit types `(x ≃ y)` : `U` of identifications between their elements `x` `y` : `T`,
written `(x = y) : Prop` for strict data types.
Similarly, lax types `S : ℓU` admit extender types: for every element `s : S`,
there is a type family `s↑ : Pᵈ`. We will write `s ↑ t` for `s↑ t`.

Quotient inductive types admit generators of identities `x = y` between their elements.
Lax types allow generators of extenders like `s [n⟩ t` that generate inhabitants
of the type `s ↑ t`. Sources of extenders must be structurally smaller than their targets
to enable typechecking. Whenever we define an extender `s [n⟩ t` , we must also
define how it acts on all possible extenders `e : t ↑ t'` yielding
some `[f n⟩ : s ↑ t'`. This action must be given by some function `f`
to ensure associativity by construction (because function composition is). Putting everything together, lax types form _strictly associative inverse categories_.

Every function we define on a lax type must have an action on all generators,
including extender generators, mapping them either to identities or extenders between results (functoriality).   
To have an example, let us define addition for
`LaxNat`s:
```kotlin
|\textbf{\textcolor{dgreen}{def}}| add : LaxNat² → LaxNat
  (LaxNat(n), LaxNat(m)) ↦ LaxNat(m + n)
  (n[k⟩, m) ↦ add(n, m) [k⟩
  (n, m[k⟩) ↦ add(n, m) [k⟩ 
```

Let us denote universes of `J`-indexed type families by `Jᵈ` instead of `J → Type`.
It does not make any difference ordinary types `J : U` ,
but for lax types it provides additional flexibility required to introduce `SizedZeroEndingSequence` as desired.
```kotlin
|\textbf{\textcolor{dgreen}{data}}| SizedZeroEndingSequence : LaxNatᵈ
  Zeros : SizedEvZeroSeq LaxNat(0)
  Prepend<n>(head : Nat, tail : SizedEvZeroSeq n) : EvZeroSeq (LaxNat(1) + n)
```
```kotlin
  expand : ???
```

Before we fill in the gap in the above definition, note that type families are functions on their index type,
so they must act on the extenders: they must map them either to identities or extenders between function results.
If we deal with type-valued functions on lax types `S → U`, extenders can only be mapped to
identities, but type families `Sᵈ` are more than type-valued functions:
they allow mapping extenders to extenders between the respective types defined as follows.

Let `F : Jᵈ` be a type family, and `e : s ↑ t` for some `s t : J`.
Then `F(e) : ∀<Y> (F(t) → Y) → (F(s) → Y)`.
We also have a dependently typed version.
```
F(e) : ∀<Y : F(t)ᵈ> (∀(x : F(t)) Y(x)) → (∀(x : F(s)) F(e) Y)(x))
```

Now we can fill in the gap in the definition of `ZeroEndingSizedSequence`. The type
of the equality generator `f = append(f, 0)` does not typecheck yet, but we can
decompose it into an application^[Anonymous functions are written like `{ n : Int ↦ n + 1 }` or `{ it + 1 }`. Types can be omitted if inferrable.] `{ it = append(f, 0) } f` and apply the domain
restriction to the function part by applying `ZeroEndingSizedSequence n[extend 1⟩`:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| EvZeroSeq : LaxNatᵈ
  Zeros : SizedEvZeroSeq LaxNat(0)
  Prepend<n>(head : Nat, tail : SizedEvZeroSeq n) : SizedEvZeroSeq (LaxNat(1) + n)
```
```kotlin
  expand : SizedEvZeroSeq 0[extend 1⟩ { Prepend(0, Zeros) = it } Zeros 
```
\newpage
# Lax algebraic theories

Models of single-sorted algebraic theories arise as dual typeclasses
for quotient inductive types we will call prototypes of those theories.
Monoids arise as models for the following type:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Monoidᴾ
  e : Monoidᴾ
  (∘) : Monoidᴾ → Monoidᴾ → Monoidᴾ
```
```kotlin
  unitorL : x = e ∘ x
  unitorR : x = x ∘ e
  associator : (x ∘ y) ∘ z = x ∘ (y ∘ z)
```

The dual typeclass `Monoidᴾᴿ<T>` will be automatically called `Monoid<T>`.
The canonical examples of monoids are lists under concatenation (free monoids) and endomorphisms under composition:
```kotlin
object List<T> : Monoid(EmptyList, (++))         // Implicitly resolvable instances 
object Endo<T> `T⟲`: Monoid<T → T>(id, (∘))      // of typeclasses are introduced as
object Auto<T> `T!`: Group<T ↔ T>(id, (∘), ( ⁻)) // companion objects of typeformers
```

We can also provide an unbiased definition for monoids, where the composition operation
is not taken to be binary, but can have any finite arity including zero for the neutral
element `e`.
Let us introduce several types:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| PTree<T>
  Leaf(label : T)
  Node(branches : PTree<T>|$^*$|)
```
```kotlin
|\textbf{\textcolor{dgreen}{data}}| SizedPTree<T> : ℕᵈ
  Leaf(label : T) : SizedPTree<T> 1
  Node<sizes : ℕ|$^*$|>(branches : HList<T> sizes) : SizedPTree<T> (sum sizes)
```
A `pr : Parenthesization(n : ℕ)` is just a `SizedPTree<Unit> n` that acts
on lists `xs : T`$^*$ turning them into respective trees `pr(xs) : PTree<T>`.

Now we can proceed to the definition of an unbiased monoid:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Monoidᴾ
  compose : Monoidᴾ|$^*$| → Monoidᴾ
```
```kotlin
  expand(xs : Monoidᴾ|$^*$|, pr : Parenthesization xs.size)
  : compose(xs) = (pr(xs) ▸map compose)  
```

If we can orient equalities so they map structurally smaller terms to structurally
larger ones, we can reformulate the theory as a lax type with extenders instead
of identities. Algebraic theories with extenders are known as lax algebraic theories.
```kotlin
|\textbf{\textcolor{dgreen}{data}}| LaxMonoidᴾ : ℓType
  compose : LaxMonoidᴾ|$^*$| → LaxMonoidᴾ
```
```kotlin
  compose(xs) [pr : Parenthesization xs.size⟩ (pr(xs) ▸map compose)
```
```kotlin
  [pr⟩ [pr'⟩ ↦ [expand (pr' ∘) p⟩  
```

When mapping into ordinary types, extenders can only be mapped into identities,
so exchanging identities for extenders does not affect set-like models, but the
lax formulation provides an explicitly confluent system of rules making the
theory stratified. Stratifiability of the sort algebra is necessary for
generalized algebraic theories to have explicit syntactic free models and
an effective model structure on the category of their models.

\newpage
# Fibered types

Many operations on containers have the following property:
the shape of the resulting container only depends on the shapes of the arguments.
For example, size of the list computed by `concatenate`, `map`, and `reverse`
can be computed based on the sizes of the input lists.

To account for that, let us introduce a notion of fibered types and functions between
them, namely the functions with the property described above.

A fibered type is given by a pair of a type `E` and a function `f : E → B` written
as `E / f`.
We will denote the type of such terms as `E ↓ B` and occasionally `(e : E) ↓ B(e)`
in case of dependent functions.

Fibered types above some base type `B : U` form a type family `↓B` and `E ↓ B := ↓B E`
is just a reverse application:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| ↓B : Uᵈ
  (E : U) / (f : E → B) : E ↓ B 
```

For example, we can take the type of lists `T`{\aSt} and the function
`size`: `T`{\aSt}` / size : T`{\aSt}` ↓ ℕ`.

A function between fibered types is a pair of functions `(f / b) : (X / p) → (Y / q)`,
so that the following square commutes by construction:
```
 X --[f]--> Y
 |p         |q
 V          V
 A --[b]--> B
```

Consider a few examples of functions on fibered types:
```kotlin
|\textbf{\textcolor{dgreen}{def}}| reverse<T> / id  : (T|$^*$| / size)  → (T|$^*$| / size)
|\textbf{\textcolor{dgreen}{def}}| concat<T>  / add : (T|$^*$| / size)² → (T|$^*$| / size)
|\textbf{\textcolor{dgreen}{def}}| flatten<T> / sum : (T|$^*$| / size)|$^*$| → (T|$^*$| / size)
```
```kotlin
|\textbf{\textcolor{dgreen}{def}}| map<X, Y>(f : X → Y) / id : (X|$^*$| / size)  → (Y|$^*$| / size)
```

Inductive-recursive definitions are mutually dependent definitions of an inductive type
and a recursive function on that type.
Such definitions naturally generate a fibered type.
```kotlin
|\textbf{\textcolor{dgreen}{data}}| V : ↓Type
  MyUnit / Unit
  MyBool / Bool
  MyPi(X : V, Y : |X| → V) / ∀(x : |X|) |Y(x)|
```
We will use `|_|` as the default name for the fibering function unless it is explicitly named.
A similar notion of fibered types in that sense was first introduced in
[“Fibred Data Types”](https://doi.org/10.1109/LICS.2013.30)
by N. Ghani, L. Malatesta; F. Nordvall Forsberg, and A. Setzer.

Type families `T : Xᵈ` can be fibered over type families `Y : Xᵈ`.
For this case,
we will introduce the notation `(x : X)ᵈ ↓ Y(x)`.
Unless `X : U` is a shape, it is equivalent to
`∀(x : X) (U ↓ Y(x))`.

Fibered types allow introducing dependent extender types:
for a type `X : U` and a fibered type `Y : Y' / X`, extenders `X ↑ Y` are terms
`e : ∀<Z : Xᵈ> (∀(x : X) Z(x)) → (∀(y : Y') Z(|y|))` so that `{ |e(f(it))| } = f` by construction.

`Σ`-type former is tightly connected to fibered types.
For every type family `Y : Bᵈ`, we have the fibered type `Σ'Y / fst : ΣY ↓ B`.
On the other hand, `Σ<J : U> : Jᵈ → U` maps type families into types, so for every J we have
a fibered type `Jᵈ / Σ<J>`.

# Matryoshka types: internalizing direct categories

So far we only applied the operator ( ᵈ) to types `T : U`, but
this operator has been introduced in Displayed Type Theory for all terms, including type families `F : Bᵈ` for some `B : U`
```kotlin
Fᵈ : Bᵈ → U
Fᵈ(E : Bᵈ) = ∀<i> (F i) → E i
```

Let us now extend the definition of ( ᵈ) to fibered types:
```
(X / |·|)ᵈ : ∀(x : X) (|x|ᵈ Y)ᵈ
```

Now let us introduce matryoshka types fibered over type families indexed by themselves:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| SΔ1 : ↓SΔ1ᵈ
  Fst / Void
  Snd / data
    Dep : |\textbar|Snd|\textbar| Fst
```

Here we define a type with two generators `Fst` and `Snd`, and for each one a type family
`|x| : SΔ1ᵈ`.
In this case, `|Fst|` is empty and `|Snd|` contains a unique element `Dep : |Snd| Fst`.

Let us now consider a type family `Y : SΔ1 / |·|)ᵈ`. Let us first apply it to `Fst`:
```
Y(Fst) : (|Fst|ᵈ Y)ᵈ
Y(Fst) : (|Void|ᵈ Y)ᵈ
Y(Fst) : (Unit)ᵈ
Y(Fst) : Type
```

So, `Y(Fst)` is just any type. Now let us apply it to `Snd`:
```
Y(Fst) : (|Snd|ᵈ Y)ᵈ
```
`|Snd|` is itself a type family fibered over `SΔ1`, so |Snd|ᵈ expects an argument of the same type as `|Snd|` and morally reduces to the “dependent function type” `∀<xs> (|x| xs) → Y xs` (not a valid expression as `xs` is not a single argument, but a telescope).

Fortunately, `|Snd|` is nonempty for only one argument, namely `Fst`, so we have
```
Y(Snd) : (Y(Fst))ᵈ
```

Thus, our type family is merely a dependent pair `Σ(T : Type) (T → Type)`.
We can now define dependent types as type families.
Let us try a more complex example:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| SΔ2 : ↓SΔ2ᵈ
  El1 / Void
  El2 / data
    Dep : |\textbar|El2|\textbar| El1
  El2 / data
    Dep : |\textbar|El3|\textbar| El2 ??
```

We run into a problem: `|El3|` is a type family over a fibered type,
so `|El3| El2` expects yet another argument, and it should be of the type
`|El3| El1`. We have no other way but to create a suitable element:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| SΔ2 : ↓SΔ2ᵈ
  El1 / Void
  El2 / data
    Dep : |\textbar|El2|\textbar| El1
  El2 / data
    Dep1 : |\textbar|El3|\textbar| El1
    Dep2 : |\textbar|El3|\textbar| El2 Dep1
```

For the whole thing to typecheck, indexes of the types `|x|` should be structurally smaller than `x`.
As we now see, such types form strictly associative direct categories.

Vocabularies `V` of theories with dependent sorts can be expressed as finite matryoshka types, theories being typeclasses of families `Carrier : Vᵈ`. Algebraic theories with dependent sorts are typeclasses dual to type families `Prototype : Vᵈ`. Categories themselves have the vocabulary
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Cell2₊ : ↓Cell2₊ᵈ
  Ob  / Void
  Mor / data 
    Source : |\textbar|Mor|\textbar| Ob
    Target : |\textbar|Mor|\textbar| Ob
```

The canonical infinite example is the type of abstract semi-simplices
```kotlin
|\textbf{\textcolor{dgreen}{data}}| SΔ : ↓SΔᵈ
  Zero / Void
  Next(s : SΔ) / data
    Prev(p : |\textbar|s|\textbar|) : |\textbar|Next(s)|\textbar| p
    Last : |\textbar|Next(s)|\textbar| s Prev(s)
```
Type families over SΔ are known as semi-simplicial type families, infinite type telescopes
```kotlin
(T₁ : Type,
 T₂(x₁ : T₁) : Type,
 T₃(x₁ : T₁, x₂ : T₂ x₁) : Type,
 T₄(x₁ : T₁, x₂ : T₂ x₁, x₃ : T₃ (x₁, x₂)) : Type,
 ...)
```

As we have done with natural numbers, we can define an implicit conversion from semi-simplices to types,
yielding their truncated versions `Unit`, `SΔ1`, `SΔ2`,
etc. This way we can define a dependent version of heterogeneous lists:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| DList<T : SΔᵈ><n : SΔ>(items : n → T n)
```

# Reedy types: internalizing Reedy categories

Reedy categories are a joint generalization of direct and inverse categories,
and can be represented by lax matryoshka inductive types,
which we will from now on call Reedy types and denote their universes by `яU`.

In particular, we can add extenders to `SΔ` to ensure that functions on `Tₙ` can be also applied to `Tₙ₊₁`.
Let us start with an incomplete definition:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Δ  : яType
  Zero / Void
  Next(s : Δ) / data
    Prev(p : |\textbar|s|\textbar|) : |\textbar|Next(s)|\textbar| p
    Last : |\textbar|Next(s)|\textbar| s Prev(s)
```
```kotlin
  Zero[n : Nat⟩ (n⁺ᶜ Next)(Zero)
  Next(s)[n : Nat, f : Fin(n⁺ + (s as ℕ)) → Fin(s as ℕ)⟩ (n⁺ᶜNext)(s)
  [n⟩ [n', f'⟩ ↦ [n', f'⟩
  [n, f⟩ [n', f'⟩ ↦ [n', { it ∘ f } f'⟩
```

Extenders define type families on a fibered type, so they have to specify action on selectors.
In this way, we will specify intertwining identities between selectors and extenders
(i.e. face and degeneracy maps as they are known for geometric shapes).
Here is a complete definition:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Δ  : яType
  Zero / Void
  ...TODO: Not just write, but make the stuff typecheck!










|\textbf{\textcolor{dgreen}{data operator}}| asType : Δᵈ
  ...TODO: Not just write, but make the stuff typecheck!





  
```

Type families on `Δ` are the infamous simplicial type families
that allow mutual definition of types and contexts when describing dependently typed theories:
```kotlin
data Ty : Ctxᵈ
  ...language-specific
  
def Ctx : Δ → Type
  Zero ↦ Unit
  Next(s) ↦ Ty this(s)
```

In bi-directionally presented computational type theories, `Ty`
must be defined mutually (inductive-inductive-recursively) with the type family of normal forms `Nf (c : Ctx, t : Ty c)`
satisfying a given type  and a fibered family of reducible expressions
that synthesize their types and normal forms `Rx : (c : Ctx)ᵈ ↓ (ty : Ty c, Nf (c, ty))`.

In theories like `CaTT` of globular weak `ω`-categories,
there are multiple kinds of judgements (`⊢`, `⊢`$\_\texttt{ps}$, and `⊢`$\_\texttt{ps}$),
and each one of them has to be represented by a type family indexed by inputs of the judgements and fibered over their outputs.

The putative Higher Observational Type Theory on which our developments are based, requires simultaneous substitutions,
requiring a cubical type family of judgement sorts.

\newpage
# Categories as models of a reedy prototype

Let us revisit the category vocabulary, adding an extra extender:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Cell2 : яType
  Ob  / Void
  Mor / data 
    Source : |\textbar|Mor|\textbar| Ob
    Target : |\textbar|Mor|\textbar| Ob
```
```kotlin
  Ob [よ⟩ Mor / ff
```

Just like we defined a monoid prototype above, we can define a prototype for categories as
an indexed quotient-inductive type family:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Catᴾ : Cell2ᵈ
  id<o : Catᴾ Ob> : (Catᴾ Mor)(o, o)
  (▸)<x, y, z> : (Catᴾ Mor)(x, y) → (Catᴾ Mor)(y, z) → (Catᴾ Mor)(x, z)
```
```kotlin
  unitorL<x, y> : ∀(f : (Catᴾ Mor)(x, y)) f = id ▸ f
  unitorR<x, y> : ∀(f : (Catᴾ Mor)(x, y)) f = f ▸ id
  associator<f, g, h> : (f ▸ g) ▸ h = f ▸ (g ▸ h)
```

The dual typeclass is precisely the usual definition of a category:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Cat<this Ts : Cell2ᵈ>(
  id<o> : Ts.mor(o, o),
  (▸)<x, y, z> : Ts.mor(x, y) → Ts.mor(y, z) → Ts.mor(x, z)
```
```kotlin
  ... subject to unitality and associativity
)
```

Yoneda extender induces equivalence between isomorphism and equivalence for objects:
```kotlin
∀<x, y> (a ≃ b) ≃ Σ(f : Ts.mor(x, y)
                    g : Ts.mor(y, x)) (f ▸ g = id) and (f ▸ g = id)            
```

But more importantly, it imposes functoriality on functions between categories:
```kotlin
f : ∀<Xs Ys : Cat> Xs.Ob  → Ys.Ob
g : ∀<Xs Ys : Cat> Xs.Obⁿ → Ys.Ob    // for any type n
h : ∀<Xs Ys : Cat> Xs.Ob|$^*$| → Ys.Ob    // for any monadic container
```

Applying these functions to the embeddings `o[よ⟩` one obtains their action on morphisms,
which must commute with `Cat`-structure, i.e. compositions.

This way we can even introduce monoidal (or lax monoidal) structure on categories as
follows:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| MonoidalCat<this Ts : Cat>(m : ∀<i> Monoid<Ts i>)
|\textbf{\textcolor{dgreen}{data}}| LaxMonoidalCat<this Ts : Cat>(m : ∀<i> LaxMonoid<Ts i>)
```

In fact, we can lift any typeclass `C<this T>` to `J`-indexed type families by
```kotlin
|\textbf{\textcolor{dgreen}{data}}| (C ↗ J)<this T : Jᵈ>(c : ∀<i> C<T i>)
```

Exactly as we did for monoids, we can proceed to derive an unbiased definition
a lax prototype.
To our understanding, lax categories are precisely the virtual double
categories, “the natural place in which to enrich categories”. Since
we now can describe weak `ω`-categories algebraically, it is worth studying
if categories weakly enriched in `ω`-categories are `ω`-categories themselves.

\newpage
# Displayed algebraic structures and parametricity

We already have the `Monoid` typeclass, so let us define their category.
First, we need a notion of monoid homomorphisms, which can be given by a “function class”:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| MonoidMorphism<X Y : Monoid>(this apply : X → Y, ...axioms)
```
So far we need a type `Ob` of objects rather than a typeclass, so let us define the
category of small monoids (ones with carriers inside the first universe `Type`):
```kotlin
object Monoid : Cat<{Ob ↦ Monoid, Mor ↦ MonoidMorphism}>(id, (∘))
```
The [□-based approach to polymorphism](https://akuklev.github.io/polymorphism) allows
automatically deriving categories `Monoid⁺` of `Type⁺`-sized monoids, `Monoid⁺⁺` and so on,
and transferring proofs and constructions upwards this hierarchy.
With the display operator `( ᵈ)` we can do even better.
It turns a typeclass like `Cat` into a displayed typeclass, a typeclass of typeclasses.
In this way,
we can introduce a companion object making the typeclass of `Monoids` into a (size-agnostic) displayed category:
```kotlin
object Monoid : Catᵈ<{Ob ↦ Monoid, Mor ↦ MonoidMorphism}>(...)
```

Homomorphisms can be defined uniformly for all algebraic theories.
A type class `T` is called algebraic if it is a dual for some inductive type `Tᴾ` called its prototype.
Given an instance `X : T` of an algebraic typeclass, let us consider the typeclass `Tᵈ<X>`.
Its instances consist of a type family indexed by elements of `X`
(a multivalued function on `X`) and an instance `Y : T` on its values.
In other words, its instances are all possible promorphisms `X ⇸ Y` (many-to-many homomorphisms) on `X`.
Ordinary homomorphisms are the univalent (= many-to-one) promorphisms:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Hom<X : T>(this pm : Tᵈ X, ∀(x) isContr(pm x))
```
This way we can uniformly derive the category of models for every algebraic theory:
```kotlin
object Monoid : Catᵈ
object Group : Catᵈ
object Ring : Catᵈ
object Cat : (Cat ↗ Cell2)ᵈ
```

The last line requires some explanation: The typeclass `Cat` itself is a typeclass of families over `Cell2`.
To obtain the typeclass of such type family classes, we must lift the typeclass `Cat` to families over `Cell2`
(as described in the previous section) and build a displayed type.
This process can be iterated yielding
```Cat : (Cat ↗ Cell2)ᵈ : ((Cat ↗ Cell2)ᵈ ↗ Cell2)ᵈ : ···```

Lifting parametric proofs and constructions upwards such hierarchies can be achieved
by generalizing the operation `↗` to typeclasses of `S`-indexed families,
so unary □-parametricity can be generalized to its `S`-ary form.
In this way, we expect
to have a satisfying solution to all size issues arising in ordinary and higher
category theory.

Exactly as type universes `Type⁺ⁿ`, universes of models for algebraic theories are not merely categories:
they come with an inbuilt notion of promorphisms `(X ⇸ Y)` and distinguished families of fibrations `X ↓ Y`
and extensions `X ↑ Y`.
Lax and/or dependently sorted algebraic theories exhibit non-invertible higher morphisms
and thus form weak `ω`-categories.
With this amount of coherent structure, our theory should be capable of formalizing the [nLab](http://ncatlab.org).

\newpage
# Future work

So far we have only considered dependent type formers valued in ordinary types, and
type families (valued in universes as categories), but it should be possible to
introduce broader dependent type formers in directed universes `яU` using an approach
modelled after [“Type Theory for Synthetic ∞-categories”](https://arxiv.org/abs/1705.07442)
by E. Riehl and M. Shulman.^[ \url{https://rzk-lang.github.io/}]

Besides Reedy types, higher directed universes `яType⁺` and upwards are also populated by
large types equipped with appropriate structure: ordinary universes, universes of algebraic structures, 
universes of type families (“presheaf universes”),
and conjecturally also sheaves which can be presented as fibered model-valued families.

Since universes of lax algebraic theories exhibit higher morphisms, ultimately we shall be pursuing stacks.