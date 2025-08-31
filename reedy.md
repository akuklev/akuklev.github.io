Reedy Types and Type Families Thereover
=======================================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com), [JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)

Building on the unpublished ideas of C. McBride and ideas from “Displayed Type Theory and Semi-Simplicial Types”
by A. Kolomatskaia and M. Shulman, we propose a novel extension for univalent Martin-Löf Type Theories (MLTTs) for internalizing Reedy categories.

Indexing and fibering over Reedy types provide effective machinery to deal with syntaxes that include binding
and become indispensable when internalizing the syntax and semantics of type theories themselves.
In this way, we obtain convenient tooling and uniformly establish the existence of initial models for structures
like [weak `ω`-categories](https://arxiv.org/abs/1706.02866), [virtual equipments](https://arxiv.org/abs/2210.08663),
(∞,1)-toposes
once the [Higher Observation Type Theory (HOTT)](https://ncatlab.org/nlab/show/higher+observational+type+theory)
is complete.

Finally, this approach should lead to a [homoiconic](https://homotopytypetheory.org/2014/03/03/hott-should-eat-itself/) univalent type theory,
i.e. one capable of representing its own syntax as a generalized inductive type
and thus also performing structural induction over it.

# Why do we need advanced type families?

Finitary type families abstractly embody formalized languages.
For example, consider the following simple language of arithmetic
and logical expressions:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| ExpressionKind
  Numeric
  Logical

|\textbf{\textcolor{dgreen}{data}}| Expr : ExpressionKind → *
  Literal(n : Int)         : Expr Numeric
  Sum(a b : Expr Numeric)  : Expr Numeric
  Mul(a b : Expr Numeric)  : Expr Numeric
  Div(a b : Expr Numeric)  : Expr Numeric
  Pow(a b : Expr(Numeric)  : Expr Numeric
  Neg(a : Expr Numeric)    : Expr Numeric
  Log(a : Expr Numeric)    : Expr Numeric
  
  Eq(a b : Expr Numeric)   : Expr Logical
  Lt(a b : Expr Numeric)   : Expr Logical
  Or(a b : Expr Logical)   : Expr Logical
  And(a b : Expr Logical)  : Expr Logical
  Not(a : Expr Logical)    : Expr Logical
```

If we allow generalized types as indexes, this approach scales up to languages with scoped binders (variables, type definitions) including general-purpose
programming languages themselves.

Data types defined that way are inhabited by abstract syntax trees
corresponding to finite expressions of the language, and they come
with a recursive descent analysis operator enabling
type-driven design of correct-by-construction analysers and interpreters.
This includes type checking, compilation, control flow analysis,
as well as static analysis and abstract interpretation in general.

As for IDEs, inductive type families enable designing biparsers for
those languages, parsers that maintain a one-to-one mapping
between the source code and the respective annotated abstract syntax
tree, enabling both fast incremental reparsing and mechanized refactoring.

To represent languages with typed variables, one introduces the type `Ty`
representing variable types in the language, and the type family `Tm : Ctxᵈ`
of terms in a given context, where contexts are lists of types `Ctx := Ty`{$^*$}.
Definition of term substitution can be vastly simplified if we make the type
`Ctx` of contexts fibered over the lax type `LaxNat` that enables context
extension and selection of subcontexts.

In case of dependently typed languages,  we’ll have a type family `Ty : Ctxᵈ`
of variable types available in a given context `c : Ctx`, and the type of contexts
is an iterated dependent pair type
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Ctx
  Empty : Ctx
  Append(prefix : Ctx, head : Ty prefix)
```
fibered over the Reedy type Δ that enables context extension and
selection of subcontexts and respecting type dependencies, which is vital for the definition of the type family
`Ty : Ctxᵈ` and the type family `Tm : (c : Ctx, Ty c)ᵈ` of terms of a
given type in a given context.

Bi-directionally typed languages (computational type theories) also require a fibered type family `Redex : (c : Ctx)ᵈ ↓ (ty : Ty c, Tm ty)`
of reducible expressions that synthesize their types.

# Setting and basics

Our base theory will be the Higher Observational Type Theory with an infinite tower of cumulative
universes `* : *⁺ : *⁺⁺ : ···` featuring □-modality-based polymorphism.

All universes will be closed under dependent product, dependent sum types, and
quotient inductive types.

The simplest types of this kind are the finite datatypes (also known as enums) defined by enumerating
their possible values:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Bool
  True    `tt`
  False   `ff`
  
|\textbf{\textcolor{dgreen}{data}}| Unit
  Point
  
|\textbf{\textcolor{dgreen}{data}}| Void {}    // no elements at all 
```

We can generalize them to sum types by allowing infinite families of “possible values”
parametrized by some other type:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Possibly<X>
  Nothing
  Value(x : X)
```

Each inductive type comes along with a dual typeclass:
```kotlin
|\textbf{\textcolor{dgreen}{typeclass}}| Boolᴿ<this Y>
  true  : Y
  false : Y
```
```kotlin
|\textbf{\textcolor{dgreen}{typeclass}}| Possiblyᴿ<X, this Y>
  nothing : Y
  value(x : X) : Y
```

Instances of these typeclasses represent by-case analysis of the respective sum types.

Inhabitants of inductive types `x : T` can be converted into functions
evaluating their by-case analysers: `xᶜ : ∀<Y : Tᴿ> Y`:
```kotlin
|\textbf{\textcolor{dgreen}{def}}| True<Y : Boolᴿ>ᶜ = Y.true
|\textbf{\textcolor{dgreen}{def}}| False<Y : Boolᴿ>ᶜ = Y.false

|\textbf{\textcolor{dgreen}{def}}| Nothing<X, Y : Possiblyᴿ<X>>ᶜ  = Y.nothing
|\textbf{\textcolor{dgreen}{def}}| Value<X, Y : Possiblyᴿ<X>)(x : X)ᶜ  = Y.value(x)
```

These functions are known as Church representations.

What if we want to return values of different types for `True` and `False`?
If we have universes (types of types), we can first define a function from
booleans into some universe `R : Bool → U` and then a dependent case analyser
```kotlin
|\textbf{\textcolor{dgreen}{typeclass}}| Boolᴹ<this Y : Bool → *>
  true  : Y(True)
  false : Y(False)
```

To apply dependent case analysers to inhabitants of the respective type we
need a special operator called induction for reasons explained below:
```
I-ind<Y : Iᴹ>(x : I) : Y(x)
```

Non-finite inductive types admit (strictly positive) recursion in type definitions,
allowing to introduce such types as natural numbers, lists, and trees:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Nat `ℕ`
  Zero `0`
  Next(pred : ℕ) `pred⁺`
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
|\textbf{\textcolor{dgreen}{typeclass}}| Natᴿ<this Y>
  zero : Y
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

While ordinary inductive types are freely generated by their generators,
quotient inductive types may additionally contain constructors of identities
between inhabitants.

This way we can define rational numbers and unordered collections:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Rational
  Frac(num : Int, den : PosInt)   `num / den`
  expand<num, den>(n : PosInt) : frac(num, den) = frac(num · n, den · n)
  
|\textbf{\textcolor{dgreen}{data}}| Collection<T>
  Bag<n : FinType>(items : n → T)
  permute<n, items>(p : n!) : Bag(items) = Bag(items ∘ p)
```
where `n!` is the type of automorphisms on the type `n`, i.e. permutations in the case of finite types.

That is, in addition to listing generators, we require that some actions
on generators (expanding the fraction or permuting list elements) must
be irrelevant for all predicates and functions defined on these types.

# Lax types: internalizing inverse categories

For a type `J : U` let `Jᵈ` denote the respective universe of type families indexed by `J`.
A typical example is length-indexed lists:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| SizedList<T> : Natᵈ
  EmptySizedList : Vec<T> 0
  NonEmptySizedList<n>(head : T, tail : SizedList<T> n) : SizedList<T> n⁺
```


Now consider the quotient inductive type of eventually-zero sequences:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| ZeroEndingSequence
  Zeros : ZeroEndingSequence
  Append(prefix : ZeroEndingSequence, head : Nat)
  extend(f : ZeroEndingSequence) : f = Append(f, 0)
```

As we have seen above, we can turn the type of lists to a length-indexed type family over `Nat`,
but we cannot make `ZeroEndingSequence` into a type family over `Nat` because
`extend` generates equality between “lists” of different lengths. We need
a “lax” index type instead of `Nat`:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| LaxNat : $*
  Lax(n : Nat) : LaxNat
  Lax(n) [m : Nat⟩ Lax(n + m)
  [n⟩ [m⟩ ↦ [(n +) m⟩
```

To each universe `U` we'll have an associated lax universe `$U` occupied by the types like the one
above. Lax inductive types are stratified directed counterparts of quotient inductive types.
For every pair of their elements `x y : T` of a set-like type `T : U` there is a type `(x = y) : U`
of identifications between `x` and `y`.

Lax types `S : $U` admit extender types instead: for every element `s : S`,
there is a type family `s↑ : Pᵈ`. We will write `s ↑ t` for `s↑ t`.

Quotient inductive types admit constructors of identities `x = y` between their elements.
Lax types allow constructors of extenders like `s [n⟩ t` that generate inhabitants
of the type `s ↑ t`. Sources of extenders must be structurally smaller than their targets
to enable typechecking. Whenever we define an extender `s [n⟩ t` , we must also
define how it acts on all possible extenders `e : t ↑ t'` yielding
some `[f n⟩ : s ↑ t'`. This action must be given by some function `f`
to ensure associativity by construction (because function composition is).

This way, lax types form strictly associative inverse categories.

Every function we define on a lax type must have an action on all constructors,
including extender constructors, which amounts to functoriality.

To have an example, let us define addition for
`LaxNat`s:
```kotlin
|\textbf{\textcolor{dgreen}{def}}| add : LaxNat² → LaxNat
  (Lax(n), Lax(m)) ↦ Lax(m + n)
  (n[k⟩, m) ↦ add(n, m) [k⟩
  (n, m[k⟩) ↦ add(n, m) [k⟩ 
```

With `LaxNat` we can transform `ZeroEndingSequence` into a type family:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| ZeroEndingSizedSequence : ↓LaxNat
  Zeros : ZeroEndingSizedSequence lax(0)
  Append<n>(prefix : ZeroEndingSizedSequence n, head : Nat)
  : ZeroEndingSizedSequence (lax(1) + n) 
```
```kotlin
  extend<n>(f : ZeroEndingSizedSequence n) : ???
```

Before we fill in the gap in the above definition, note that type families also seem to be functions on their index type,
so they must act on the extender constructors: they must map extender constructors to identities or extenders
between function results. If we deal with type-valued functions on lax types `S → U`, extenders can only be mapped to
identities, but type families `Sᵈ` are more than type-valued functions: they allow mapping extenders to extenders
between types which we define as follows. For types `X Y : U`, the type `X ↑ Y` is a pair of a function `b : Y → X` and
domain extension operator `e : ∀<Z> (X → Z) → (Y → Z)` so that for every `f : X → Z`, we have equality by construction
(definitional equality) `b ∘ e(f) = f`.

Let `F : Iᵈ` be a type family, and `e : s ↑ t` for some `s t : I`.
Then `F(e) : ∀<Y> (F(s) → Y) → (F(t) → Y)`. We also have a dependently typed version.
```
F(e) : ∀<Y : F(s)ᵈ> (∀(x : F(s)) Y(x)) → (∀(x : F(t)) F(e) Y)(x))
```

Now we can fill in the gap in the definition of `ZeroEndingSizedSequence`. The type
of the equality constructor `f = append(f, 0)` does not typecheck yet, but we can
decompose it into an application `{ it = append(f, 0) } f` and apply the domain
extension to the function part by applying `ZeroEndingSizedSequence n[extend 1⟩`:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| ZeroEndingSizedSequence : LaxNatᵈ
  Zeros : ZeroEndingSizedSequence Lax(0)
  Append<n>(prefix : ZeroEndingSizedSequence n, head : Nat)
  : ZeroEndingSizedSequence (Lax(1) + n) 
```
```kotlin
  extend<n>(f : ZeroEndingSizedSequence n)
  : ZeroEndingSizedSequence n[extend 1⟩ { it = Append(f, 0) } f
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

The dual typeclass `Monoidᴾᴿ<T>` will be automatically simply called `Monoid<T>`.

We can also provide an unbiased definition for monoids, where the composition operation
is not taken to be binary, but can have any finite arity including zero for the neutral
element `e`. Let's introduce several types:
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
  expand(xs : Monoidᴾ|$^*$|, pr : Parenthesization xs.length)
  : compose(xs) = (pr(xs) ▸map compose)  
```

If we can orient equalities so they map structurally smaller terms to structurally
larger ones, we can reformulate the theory as a lax type with extenders instead
of identities. Algebraic theories with extenders are known as lax algebraic theories.
```kotlin
|\textbf{\textcolor{dgreen}{data}}| LaxMonoidᴾ : $*
  compose : LaxMonoidᴾ|$^*$| → LaxMonoidᴾ
```
```kotlin
  compose(xs) [pr : Parenthesization xs.length⟩ (pr(xs) ▸map compose)
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
For example, length of the list computed by `concatenate`, `map`, and `reverse`
can be computed based on the lengths of the input lists.

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
`length`: `T`{\aSt}` / length : T`{\aSt}` ↓ ℕ`.

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
|\textbf{\textcolor{dgreen}{def}}| reverse<T> / id  : (T|$^*$| / length)  → (T|$^*$| / length)
|\textbf{\textcolor{dgreen}{def}}| concat<T> / add  : (T|$^*$| / length)² → (T|$^*$| / length)
|\textbf{\textcolor{dgreen}{def}}| flatten<T> / sum : (T|$^*$| / length)|$^*$| → (T|$^*$| / length)
```
```kotlin
|\textbf{\textcolor{dgreen}{def}}| map<X, Y>(f : X → Y) / id : (X|$^*$| / length)  → (Y|$^*$| / length)
```

Inductive-recursive definitions are mutually dependent definitions of an inductive type
and a recursive function on that type.
Such definitions naturally generate a fibered type.
```kotlin
|\textbf{\textcolor{dgreen}{data}}| V : * ↓ * 
  unit / Unit
  bool / Bool
  pi(X : V, Y : |X| → V) / ∀(x : |X|) |Y(x)|
```
We will use `|_|` as the default name for the fibering function unless it is explicitly named. A similar notion of fibered types in that sense was first introduced in [“Fibred Data Types”](https://doi.org/10.1109/LICS.2013.30) by N. Ghani et al.

Type families `T : Xᵈ` can be fibered over type families `Y : Xᵈ`. For this case, we'll introduce the notation `(x : X)ᵈ ↓ Y(x)`. Unless `X : U` is a shape, it is equivalent to
`∀(x : X) (U ↓ Y(x))`.

Fibered types allow introducing dependent extender types:
for a type `X : U` and a fibered type `Y : Y' / X`, extenders `X ↑ Y` are terms of the type
`e : ∀<Z : Xᵈ> (∀(x : X) Z(x)) → (∀(y : Y') Z(|y|))` so that `{ |e(f(it))| } = f` by construction.

`Σ`-type former is tightly connected to fibered types.
On one hand, for every type family `Y : Bᵈ`, we have the fibered type `Σ'Y / fst : ΣY ↓ B`.
On the other hand, `Σ<J : U> : Jᵈ → U` maps type families into types so for every J we have
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
|\textbf{\textcolor{dgreen}{data}}| |\bbD| : * ↓ |\bbD|ᵈ
  Fst / Void
  Snd / data
    Dep : |$\vert$|Snd|$\vert$| Fst
```

Here we define a type with two generators `Fst` and `Snd`, and for each a type family
`|x| : `{\ddD}`ᵈ`. In this case, |Fst| is empty and |Snd| contains a unique element `Dep : |Snd| Fst`.

Let us now consider a type family `Y : (`{\thinspace\bbD}` / |·|)ᵈ`. Let us first apply it to `Fst`:
```
Y(Fst) : (|Fst|ᵈ Y)ᵈ
Y(Fst) : (|Void|ᵈ Y)ᵈ
Y(Fst) : (Unit)ᵈ
Y(Fst) : *
```

So, `Y(Fst)` is just any type. Now let us apply it to `Snd`:
```
Y(Fst) : (|Snd|ᵈ Y)ᵈ
```
`|Snd|` is itself a type family fibered over \bbD, so |Snd|ᵈ expects an argument of the same type as `|Snd|` and yields a “dependent function type” `∀<xs> (|x| xs) → Y xs`. This expression is not a valid type because `xs` is not a single argument, but a telescope.

Fortunately, `|Snd|` is nonempty for only one argument, namely `Fst`, so we have
```
Y(Snd) : (Y(Fst))ᵈ
```

Thus, our type family is merely a dependent pair `Σ(T : *) (T → *)`! We can now define dependent types as type families. Let us try a more complex example:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Δ2⁺ : *⟲    // Shorter notation for T : T ↓ Tᵈ
  El1 / Void
  El2 / data
    Dep : |$\vert$|El2|$\vert$| El1
  El2 / data
    Dep : |$\vert$|El3|$\vert$| El2 ??
```

We run into a problem: `|El3|` is a type family over a fibered type,
so `|El3| El2` expects yet another argument, and it should be of the type
`|El3| El1`. We have no other way but to create a suitable element:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Δ2⁺ : *⟲
  El1 / Void
  El2 / data
    Dep : |$\vert$|El2|$\vert$| El1
  El2 / data
    Dep1 : |$\vert$|El3|$\vert$| El1
    Dep2 : |$\vert$|El3|$\vert$| El2 Dep1
```

For the whole thing to typecheck indexes of the types `|x|` should be structurally smaller than `x`. As you now see, such types form strictly associative direct categories.

Vocabularies `V` of theories with dependent sorts can be expressed as finite matryoshka types, theories being typeclasses of families `Carrier : Vᵈ`. Algebraic theories with dependent sorts are typeclasses dual to inductive type families `Prototype : Vᵈ`. Categories themselves have the vocabulary
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Cell2⁺ : *⟲
  Ob  / Void
  Mor / data 
    Source : |$\vert$|Mor|$\vert$| Ob
    Target : |$\vert$|Mor|$\vert$| Ob
```

A foundational infinite example is the semi-simplicial shape type
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Δ⁺ : *⟲
  Zero / Void
  Next(s : Δ⁺) / data
    Prev(p : |$\vert$|s|$\vert$|) : |$\vert$|Next(s)|$\vert$| p
    Last : |$\vert$|Next(s)|$\vert$| s Prev(s)
```

Type families over Δ⁺ are known as semi-simplicial types and represent infinite sequences of sequentially dependent types
```kotlin
(T₁ : *,
 T₂(x₁ : T₁) : *,
 T₃(x₁ : T₁, x₂ : T₂ x₁) : *,
 T₄(x₁ : T₁, x₂ : T₂ x₁, x₃ : T₃ (x₁, x₂)) : *,
 ...)
```

# Reedy types: internalizing Reedy categories

Reedy categories are common generalization of direct and inverse categories, and can be represented by lax matryoshka inductive types which we'll call reedy types from now on.

In particular, we can add extenders to Δ⁺ to ensure that functions on `Tₙ` can be also applied to `Tₙ₊₁`. Let us start with an incomplete definition:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Δ  : $*⟲
  Zero / Void
  Next(s : Δ⁺) / data
    Prev(p : |$\vert$|s|$\vert$|) : |$\vert$|Next(s)|$\vert$| p
    Last : |$\vert$|Next(s)|$\vert$| s Prev(s)
```
```kotlin
  Zero[n : Nat⟩ (n⁺ᶜ Next)(Zero)
  Next(s)[n : Nat, f : Fin(n⁺ + (s as ℕ)) → Fin(s as ℕ)⟩ (n⁺ᶜNext)(s)
  [n⟩ [n', f'⟩ ↦ [n', f'⟩
  [n, f⟩ [n', f'⟩ ↦ [n', { it ∘ f } f'⟩
```

Extenders define type families on a fibered type, so they have to specify action on selectors. In this way, we'll specify intertwining identities between selectors and extenders (i.e. face and degeneracy maps as they are known for geometric shapes).
For the complete definition with detailed description, see Appendix I.

Type families on Δ are the infamous simplicial types essential for dependently typed theories.

# Categories as models of a reedy prototype

Let us revisit the category vocabulary, adding an extra extender:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Cell2 : : $*⟲
  Ob  / Void
  Mor / data 
    Source : |$\vert$|Mor|$\vert$| Ob
    Target : |$\vert$|Mor|$\vert$| Ob
```
```kotlin
  Ob [よ⟩ Mor / ff
```

Just like we defined a monoid prototype above, we can define a prototype for categories as
an indexed quotient-inductive type family:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Catᴾ : Cell2ᵈ
  id{o : Catᴾ Ob} : (Catᴾ Mor)(o, o)
  (▸){x, y, z} : (Catᴾ Mor)(x, y) → (Catᴾ Mor)(y, z) → (Catᴾ Mor)(x, z)
```
```kotlin
  unitorL{x, y} : ∀(f : (Catᴾ Mor)(x, y)) f = id ▸ f
  unitorR{x, y} : ∀(f : (Catᴾ Mor)(x, y)) f = f ▸ id
  associator{f g h} : (f ▸ g) ▸ h = f ▸ (g ▸ h)
```

The dual typeclass is precisely the usual definition of a category:
```kotlin
|\textbf{\textcolor{dgreen}{typeclass}}| Cat<this Ts : Cell2ᵈ>
  id{o} : Ts.mor(o, o)
  (▸){x, y, z} : Ts.mor(x, y) → Ts.mor(y, z) → Ts.mor(x, z)
```
```kotlin
  ... subject to unitality and associativity
```

Yoneda extender induces equivalence between isomorphism and equivalence for objects:
```kotlin
∀{x, y} (a ≃ b) ≃ Σ(f : Ts.mor(x, y)
                    g : Ts.mor(y, x)) (f ▸ g = id) and (f ▸ g = id)            
```

But more importantly, it imposes functoriality on functions between categories:
```kotlin
f : ∀<Xs Ys : Cat> Xs.Ob  → Ys.Ob
g : ∀<Xs Ys : Cat> Xs.Obⁿ|\!| → Ys.Ob    // for any type n
h : ∀<Xs Ys : Cat> Xs.Ob|$^*$| → Ys.Ob    // for any monadic container
```

Applying these functions to the embeddings `o[よ⟩` one obtains their action on morphisms,
which must commute with `Cat`-structure, i.e. compositions.

This way we can even introduce monoidal (or lax monoidal) structure on categories as
follows:
```kotlin
|\textbf{\textcolor{dgreen}{typeclass}}| MonoidalCat<Ts : Cat> extends Monoid<Ts.Ob> {}
|\textbf{\textcolor{dgreen}{typeclass}}| LaxMonoidalCat<Ts : Cat> extends LaxMonoid<Ts.Ob> {}
```

Exactly as we did for monoids, we can proceed to derive an unbiased definition
a lax prototype.
To our understanding, lax categories are precisely the virtual double
categories, “the natural place in which to enrich categories”. Since
we now can describe weak `ω`-categories algebraically, it is worth studying
if categories weakly enriched in `ω`-categories are `ω`-categories themselves.

\newpage
# Displayed algebraic structures

The other nice thing is that since we have defined categories as models for an inductive type,
we automatically have the typeclass of displayed categories, and all algebraic typeclasses are instances of it:
```kotlin
Group : Catᵈ
Ring : Catᵈ
Cat : Catᵈ
```
Furthermore, we can iterate, and thus `Catᵈ : Catᵈᵈ`, etc. And since constructions and proofs also can be lifted,
any statement we have proven for all small categories `prf<C : Cat>` also can be applied to displayed categories,
say like the category `Grp : Catᵈ` of all groups and the category of all categories `Cat : Catᵈ` itself.

# Universes of models are model categories with proarrows

Displayed models for inductive types have the form
```kotlin
|\textbf{\textcolor{dgreen}{typeclass}}| ℕᴿᵈ<M : ℕᴿ, this Ts : |M| → *>
  zero : Ts(M.zero)
  next : ∀{n : M} Ts(n) → Ts(M.next n)
```
allowing to define the type of motives `ℕᴹ` for the induction operator `ℕ-ind`:
```kotlin
|\textbf{\textcolor{dgreen}{def}}| ℕᴹ<this P : ℕᵈ> = ℕᴿᵈ<ℕ, P>
```
```kotlin
ℕ-ind<P : ℕᴹ> : ∀{n} P(n)
```

For each model `M : ℕᴿ`, the inhabitants `Pm : ℕᴿᵈ<M>` are promorphisms (many-to-many correspondences, sometimes also called weak homomorphisms) on `M` with the target given by
```kotlin
|\textbf{\textcolor{dgreen}{instance}}| Pm.target : ℕᴿ<M × Pm>
  zero: (M.zero, Pm.zero M.base)
  step: { n : M, x : (Pm n) ↦ (M.step n, Pm.next (M.next n) x) }
```

We can single out homomorphisms as the univalent (= many-to-one) promorphisms
```kotlin
|\textbf{\textcolor{dgreen}{def}}| isUniv<src : ℕᴿ, pm : ℕᴿᵈ src> = ∀{n} isContr(pm n),
```
making the type of `ℕ`-models into a ∞-precategory (Segal type),
which turns out to be a ∞-category (Complete Segal type) due to a well-known fact that the equivalences `(≃)<ℕᴿ>` of `ℕ`-models correspond to their isomorphisms.

Categories of models also carry a weak model structure that coincides with the one given by extenders between types and fibered types for ordinary universes `U` which can be seen as universes of models for the empty theory. For lax and/or generalized algebraic theories, they may exhibit non-invertible higher morphisms and thus form weak `ω`-categories.
In particular, we expect to have an infinite typeclass hierarchy
```
ωCat : ωCatᵈ : ωCatᵈᵈ : ···
```

Together with [□-modality based approach to polymorphism](https://akuklev.github.io/polymorphism), we expect
to have a satisfying solution to all size issues arising in ordinary and higher
category theory. In fact, we hope that the presented type theory is capable of
eventually formalizing the [nLab](http://ncatlab.org) in its entirety.

\newpage
# Future work

So far we have only considered dependent type formers valued in ordinary types, and
type families (valued in universes as categories), but it should be possible to
introduce broader dependent type formers in lax universes `$U` using an approach
modelled after “Type Theory for Synthetic ∞-categories” by E. Riehl and M. Shulman.

Besides lax inductive types, lax universes are also populated by large types equipped with appropriate structure. As we have seen above, not only Reedy types are equipped with extenders and selectors (= weak model categories). It also applies to universes, universes of algebraic structures, universes of type families (“presheaf universes”), and conjecturally also sheaves which can be presented as fibered model-valued families.

Since universes of lax algebraic theories exhibit higher morphisms, ultimately we shall be pursuing stacks.