Higher Categorical Type Theory
==============================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com), [JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)

Building on the unpublished ideas of C. McBride and ideas from “Displayed Type Theory and Semi-Simplicial Types”
by A. Kolomatskaia and M. Shulman, we propose a novel extension for univalent Martin-Löf Type Theories (MLTTs)
that allows internalizing Reedy categories.

Indexing and fibering over shape types provide effective machinery to deal with syntaxes that include binding
and become indispensable when internalizing the syntax and semantics of type theories themselves.
In this way, we obtain a convenient tooling and uniformly establish the existence of initial models for structures
like [weak ω-categories](https://arxiv.org/abs/1706.02866), [virtual equipments](https://arxiv.org/abs/2210.08663), 
(∞,1)-toposes
once the [Higher Observation Type Theory (HOTT)](https://ncatlab.org/nlab/show/higher+observational+type+theory)
is complete.

Finally, this approach should lead to a homoiconic univalent type theory (see “Type Theory should eat itself”),
i.e. one capable of representing its own syntax as a generalized inductive type
and thus also performing structural induction over it.

# Motivation

Finitary type families abstractly embody formalized languages.
For example, consider the following simple language of arithmetic
and logical expressions:
```
data ExpressionKind
  Numeric
  Logical

data Expr : ↓ExpressionKind
  Literal(n : Int)          : Expr(Numeric)
  Sum(a b : Expr(Numeric))  : Expr(Numeric)
  Mul(a b : Expr(Numeric))  : Expr(Numeric)
  Div(a b : Expr(Numeric))  : Expr(Numeric)
  Pow(a b : Expr(Numeric))  : Expr(Numeric)
  Neg(a : Expr(Numeric))    : Expr(Numeric)
  Log(a : Expr(Numeric))    : Expr(Numeric)
  
  Eq(a b : Expr(Numeric))   : Expr(Logical)
  Less(a b : Expr(Numeric)) : Expr(Logical)
  And(a b : Expr(Logical))  : Expr(Logical)
  Or(a b : Expr(Logical))   : Expr(Logical)
  Not(a b : Expr(Logical))  : Expr(Logical)
```

This approach scales up to languages that may declare and bind named
entities (variables, constants, internal types) including general-purpose
programming languages themselves.

Data types defined that way are inhabited by abstract syntax trees
corresponding to finite expressions of the language, and they come
with a recursive descent analysis operator that enabling
type-driven design of correct-by-construction analysers and interpreters.
This includes type checking, compilation, control flow analysis,
as well as static analysis and abstract interpretation in general.

As for IDEs, inductive type families enable designing biparsers for
those languages, i.e. parsers that maintain one-to-one mapping
between the source code and the respective annotated abstract syntax
tree, enabling both fast incremental reparsing and mechanized refactoring.

* * *

To represent languages with typed variables, one introduces the type `Ty`
representing variable types in the language, and the type family `Tm : ↓Ctx`
of terms in a given context, where contexts are lists of types `Ctx := Ty*`.
Definition of term substitution can be vastly simplified if we make the type
`Ctx` of contexts fibered over the shape type `LaxNat` that enables context
extension and selection of subcontexts.

In case of dependently typed languages, the we’ll have a type family `Ty : ↓Ctx`
of variable types available in a given context `c : Ctx`, and the type of contexts
is an iterated dependent pair type
```
data Ctx
  Empty : Ctx
  Append(prefix : Ctx, head : Ty prefix)
```
fibered over the shape type Δ that enables context extension and
selection of subcontexts and respecting type dependencies, which is
a absolutely vital for the definition of the aforementioned type family
`Ty : ↓Ctx` and the type family `Tm : ↓(c : Ctx, Ty c)` of terms of a
given type in a given context.

Bi-directionally typed languages (computational type theories) also
require a fibered type family `Redex : ↓(c : Ctx) ↑(ty : Ty c, Tm ty) `
of reducible expressions together with a function 
`|r : Redex| : Σ(ty : Ty c) Tm ty` that computes their normal forms.

Now as we have motivated the need for all this stuff, let's dive in.

# Setting and basics

Our base theory will be the Higher Observational Type Theory with an infinite tower of cumulative
universes `* : *⁺ : *⁺⁺ : ···` featuring □-modality-based polymorphism.

All universes will be closed under dependent product, dependent sum types, and
quotient inductive types.

The simplest types of this kind are the finite datatypes (also known as enums) defined by enumerating
their possible values:
```
data Boolean
  True
  False
  
data Unit
  Point
  
data Void
  # no elements at all 
```

We can generalize them to sum types by allowing infinite families of “possible values”
parametrized by some other type:
```
data Possibly<X>
  Nothing
  Value(x : X)
```

Each inductive type comes along with a dual typeclass:
```
typeclass Booleanᴿ<this Y>
  true  : Y
  false : Y
```
```
typeclass Possiblyᴿ<X, this Y>
  nothing : Y
  value(x : X) : Y
```

Instances of these typeclasses represent by-case analysis of the respective sum types.

Inhabitants of inductive types `x : T` can be converted into functions
evaluating their by-case analysers: `xᶜ : ∀<Y : Tᴿ> Y`:
```
def Trueᶜ<Y : Booleanᴿ>() = Y.true
def False<Y : Booleanᴿ>() = Y.false

def Nothingᶜ<X, Y : Possiblyᴿ<X>>()  = Y.nothing
def Value<X, Y : Possiblyᴿ<X>)(x : X)ᶜ  = Y.value(x)
```

These functions are known as Church representations.

What if we want to return values of different types for `True` and `False`?
If we have universes (types of types), we can first define a function from
booleans into some universe `R : Boolean → 𝒰` and then a dependent case analyser
```
typeclass Booleanᴹ<this Y : Boolean → *>
  true  : Y(True)
  false : Y(False)
```

To apply dependent case analysers to inhabitants of the respective type we
need special operator called induction for reasons explained below:
```
I-ind<Y : Iᴹ>(x : I) : Y(x)
```

Non-finite inductive types admit (strictly positive) recursion in type definitions,
allowing introduce such types as natural numbers, lists, and trees:
```
data Nat `ℕ`
  Zero `0`
  Next(pred : ℕ) `pred⁺`
```
```
data List<T> `T*`
  EmptyList : T*
  NonEmptyList(head : T, tail : T*) : T*
```
```
data BinTree<T>
  Leaf
  Node(label: T, left : BinTree<T>, right : BinTree<T>)
```
```
data VarTree<T>
  Leaf
  Node(label: T, branches : VarTree<T>*)
```
```
data InfTree<T>
  Leaf
  Node(label: T, branches : Nat → InfTree<T>)
```

All above examples except infinitely branching trees are finitary inductive types,
i.e. inductive types with the property that all of their generators have a finite
number of parameters, and all these parameters are of finitary inductive types.
Finitary inductive types may be infinite, but their inhabitants can be encoded
by natural numbers or, equivalently finite bit strings.

Finitary inductive types embody single-sorted languages.
They are inhabited by abstract syntax trees corresponding to finite expressions
of the language formed by their generators.

“Case analysis” for the type of natural numbers provides n-ary iteration operator:
```
typeclass Natᴿ<this Y>
  zero : Y
  next(p : Y) : Y
```
Analysing a natural number `n` by `R : Natᴿ<Y>` yields `nᶜ<R>() = (R.next)ⁿ R.zero`,
allowing to iterate arbitrary functions given number of times. In general,
“case analysis” turns into “recursive descent analysis”. For lists and trees we
obtain the respective fold operators.

Type-valued functions on natural numbers `Y : Nat → 𝒰` can encode arbitrary predicates,
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
```
data Rational
  frac(num : Int, den : PosInt)
  expand<num, den>(n : PosInt) : frac(num, den) = frac(num · n, den · n)
  
data Collection<T>
  bagOf<n : FinType>(items : n → T)
  permute<n, items>(p : n!) : bagOf(items) = bagOf(items ∘ p)
```
where `n!` is the type of automorphisms on the type `n`, i.e. permutations in case of finite types.

That is, in addition to listing generators, we require that some actions
on generators (expanding the fraction or permuting list elements) must
be irrelevant for all predicates and functions defined on these types.

# Type families and inverse categories

For a type `J : 𝒰` let `Jᵈ` denote the respective universe of type families indexed by `J`.
A typical example is length-indexed lists:
```
data Vec<T> : Natᵈ
  nil : Vec<T> 0
  cons<n>(head : T, tail : Vec<T> n) : Vec<T> n⁺
```


Now consider the quotient inductive type of eventually-zero sequences:
```
data ZeroEndingSequence
  nil : ZeroEndingSequence
  append(prefix : ZeroEndingSequence, head : Nat)
  extend(f : ZeroEndingSequence) : f = append(f, 0)
```

As we have seen above, we can turn the type of lists to a length-indexed type family over `Nat`,
but we cannot make `ZeroEndingSequence` into a type family over `Nat` because
`extend` generates equality between “lists” of different lengths. We need
a “lax” index type instead of `Nat`:
```
shape LaxNat
  lax(n : Nat) : LaxNat
  lax(n) [extend (m : Nat)⟩ lax(n + m)
  [extend n⟩ [extend m⟩ ↦ [extend n + m⟩
```

To each universe `𝒰` we'll have an associated shape universe `$𝒰` occupied by the types like the one
above. Inductive shape types are stratified directed counterparts of quotient inductive types.
For every pair of their elements `x y : T` of and ordinary type `T : 𝒰` there is a type `(x = y) : 𝒰`
of identifications between `x` and `y`.

Shape types `S : $𝒰` admit extension types instead: for every element `s : S`,
there is a type family `s↑ : Pᵈ`. We will write `s ↑ t` for `s↑ t`.

Quotient inductive types admit generators of identities `x = y` between their elements. 
Shape types allow extension generators like `s [extend n⟩ t` that generate inhabitants 
of the type `s ↑ t`. Sources of extenders must be structurally smaller than their targets
to enable typechecking. Whenever we define an extension `s [extend n⟩ t` , we must also
define how this extension acts on all possible extensions `e : t ↑ t'` yielding
some `[extend f(n)⟩ : s ↑ t'`. This action must be given by some function `f`
so ensure associativity by construction (because function composition is).

This way, shape types form strictly associative inverse categories.

Every function we define on a shape type must have an action on all constructors,
including extension constructors, which amounts to functoriality.

To have an example, let us define addition for
`LaxNat`s:
```
def add : LaxNat² → LaxNat
  (lax(n), lax(m)) ↦ lax(m + n)
  (n[extend k⟩, m) ↦ add(n, m) [extend k⟩
  (n, m[extend k⟩) ↦ add(n, m) [extend k⟩ 
```

With `LaxNat` we can transform `ZeroEndingSequence` into a type family:
```
data ZeroEndingSizedSequence : ↓LaxNat
  nil : ZeroEndingSizedSequence lax(0)
  append<n>(prefix : ZeroEndingSizedSequence n, head : Nat) : ZeroEndingSizedSequence (lax(1) + n) 
  extend<n>(f : ZeroEndingSizedSequence n) : ???
```

Before we fill in the gap in the above definition, note that type families also seem to be functions on their index type,
so they must act on the extension constructors: they must map extension constructors to identities or extensions
between function results. Extensions between types are domain extensions for functions defined
on those types, i.e. for a types `X Y : *`, the type `X ↑ Y` is `∀<Z> (X → Z) → (Y → Z)`.
Let `F : Iᵈ` be a type family, and `e : s ↑ t` for some `s t : I`.
Then `F(e) : ∀<Y> (F(s) → Y) → (F(t) → Y)`. We also have a dependently typed version.
```
F(e) : ∀<Y : F(s)ᵈ> (∀(x : F(s)) Y(x)) → (∀(x : F(t)) F(e) Y)(x))
```

Now we can fill in the gap in the definition of `ZeroEndingSizedSequence`. The type
of the equality constructor `f = append(f, 0)` does not typecheck yet, but we can
decompose it into an application `{ it = append(f, 0) } f` and apply the domain
extension to the function part by applying `ZeroEndingSizedSequence n[extend 1⟩`:
```
data ZeroEndingSizedSequence : LaxNatᵈ
  nil : ZeroEndingSizedSequence lax(0)
  append<n>(prefix : ZeroEndingSizedSequence n, head : Nat) : ZeroEndingSizedSequence (lax(1) + n) 
  extend<n>(f : ZeroEndingSizedSequence n)
  : ZeroEndingSizedSequence n[extend 1⟩ { it = append(f, 0) } f
```

# Lax algebraic theories via shapes

Models of single-sorted algebraic theories arise as dual typeclasses
for quotient inductive types we will call prototypes of those theories.
Monoids arise as models for the following type:
```
data MonoidPt
  e : MonoidPt
  (∘) : MonoidPt → MonoidPt → MonoidPt

  unitorL : x = e ∘ x
  unitorR : x = x ∘ e
  associator : (x ∘ y) ∘ z = x ∘ (y ∘ z)
```

We can also provide an unbiased definition for monoids, where the composition operation
is not taken to be binary, but can have any finite arity including zero for the neutral
element `e`. Let's introduce several types:
```
data PTree<T>
  Leaf(label : T)
  Node(branches : PTree<T>*)
```
```
data SizedPTree<T> : ℕᵈ
  Leaf(label : T) : SizedPTree<T> 1
  Node<sizes : ℕ*>(branches : HList<T> sizes) : SizedPTree<T> (sum sizes)
```
A `pr : Parenthesization(n : ℕ)` is just a `SizedPTree<Unit> n` that acts
on lists `xs : T*` turning them into respective trees `pr(xs) : PTree<T>`.

Now we can proceed to the definition of an unbiased monoid:
```
shape MonoidPt
  compose : LaxMonoidPt* → LaxMonoidPt

  expand(xs : LaxMonoidPt*,
         pr : Parenthesization(xs.length)
  : compose(xs) = (pr(xs) map compose)  
```

If we can orient equalities so they map structurally smaller terms to structurally
larger ones, we can reformulate the theory as a shape type with extensions instead
of identities. Algebraic theories with extenders are known as lax algebraic theories.
```
shape LaxMonoidPt
  compose : LaxMonoidPt* → LaxMonoidPt

  compose(xs) [expand (pr : Parenthesization(l ▸length))⟩ (pr(xs) map compose)
  [expand pr⟩ [expand pr'⟩ ↦ [expand (pr' ∘) p⟩  
```

When mapping into set-like types, extensions can only be mapped into identities,
so exchanging identities for extensions does not affect set-like models, but the
extension formulation provides an explicitly confluent system of rules making
the theory stratified. Stratifiability of the sort algebra is necessary for
generalized algebraic theories to have explicit syntactic free models and effective
model structure on the category of their models.

# Fibered types and direct categories

Many operations on containers have the following property:
the shape of the resulting container only depends on the shapes of the arguments.
For example, length of the list computed by `concatenate`, `map`, and `reverse`
can be computed based on the lengths of the input lists.

To account for that let us introduce a notion of fibered types and functions between
them, namely the functions with the property described above.

A fibered type is given by a pair of a type `E` and a function `f : E → B` written
as `E / f`.
We will denote the type of such terms as `E ↓ B` and occasionally `(e : E) ↓ B(e)`
in case of dependent functions.

Fibered types above some base type `B : 𝒰` form a type family `↓B` and `E ↓ B := ↓B E`
is just a reverse application:
```
data ↓B : 𝒰ᵈ
  (E : 𝒰) / (f : E → B) : E ↓ B 
```

For example, we can take the type of lists `T*` and the function `length : T* → ℕ`:
`T* / length : T* ↓ ℕ`. 

A function between fibered types is a pair of functions `(f / b) : (X / p) → (Y / q)`,
so that the following square commutes by construction:
```
 X --[f]--> Y
 |p         |q
 V          V
 A --[b]--> B
```

Consider a few examples of functions on fibered types:
```
reverse<T> / id  : (T* / length)  → (T* / length)
concat<T> / add  : (T* / length)² → (T* / length)
flatten<T> / sum : (T* / length)* → (T* / length)

map<X, Y>(f : X → Y) / id : (X* / length)  → (Y* / length)
```

Inductive-recursive definitions are mutually dependent definitions of an inductive type
and a recursive function on that type.
Such definitions naturally generate a fibered type.

**TODO:** Σ-closed universe example

We will use `|_|` as the default name of fibering function unless it is explicitly named.

Fibered types allow formulating dependent type extensions:
for a type `X : 𝒰` and a fibered type `Y : Y' / X`, extensions `X ↑ Y` are terms of the type
`∀<Z : X → 𝒰> (∀(x : X) Z(x)) → (∀(y : Y') Z(|y|))`.

`Σ`-type former is tightly connected to fibered types.
On one hand, for every type family `Y : Bᵈ`, we have the fibered type `Σ'Y / fst : ΣY ↓ B`.
On the other hand, `Σ<J : 𝒰> : Jᵈ → 𝒰` maps type families into types so for every J we have
a fibered type `Jᵈ / Σ<J>`.

Above we only used the operator ( ᵈ) on types `T : 𝒰` to denote type-families `Tᵈ`, but
this operator was actually introduced in “Displayed Type Theory and Semi-Simplicial Types”
for all terms.
Let us extend its definition to fibered types as follows.
For `Y : (F / f)ᵈ`, where `f : F → B`, and `x : F` let:
```
Y(x) : Bᵈ (f x) Y
```

Еhe significance of this definition comes to light when we consider
that inductive types can be self-fibered:
```
shape 𝔻 : * ↓ 𝔻
  fst / (Void / exfalso)
  snd / (Unit / { fst })
```

Here we define a type with two generators `fst` and `snd`, and a function `|x : 𝔻| : (* ↓ 𝔻)`,
i.e. for every generator `c` we have a type `|c|` fibered over `𝔻`.
For `fst`, this type `|fst|` is empty. For `snd`, `|snd|` is a unit type together with a function
mapping its unique element to `fst`.

Inductive self-fibered types form strictly associative direct categories. (TODO: Clarify)

A type family `Y : ↓(𝔻 / |·|)` indexed over this type satisfies the following typing rule:
```
Y(x : 𝔻) : (* ↓ 𝔻)ᵈ |x| Y
```

Since `𝔻` only has two elements, we can split cases:
```
Y(fst) : (* ↓ 𝔻)ᵈ |fst| Y
Y(snd) : (* ↓ 𝔻)ᵈ |snd| Y
```
which in turn reduces to
```
Y(fst) : (* ↓ 𝔻)ᵈ (Void / { it }) Y
Y(snd) : (* ↓ 𝔻)ᵈ (Unit / { fst }) Y
```
further reducing to
```
Y(fst) : (∀(u / f : (Void / { it })) Y(f(u))) → 𝒰
Y(snd) : (∀(u / f : (Unit / { fst })) Y(f u)) → 𝒰
```

Product over empty domain is `Unit`, and the product over unit domain is just one element:
```
Y(fst) : Unit → 𝒰
Y(snd) : Y(fst) → 𝒰
```
So our type family is merely a dependent pair `Σ(T : 𝒰) (T → 𝒰)`!

With self-fibered index types we can define dependent pairs as dependent function types.
Signatures of theories with dependent sorts can be expressed as finite direct categories,
so first-order and higher-order theories with dependent sorts can be expressed as type
classes parametrized by such families.
Algebraic theories with dependent sorts can be
expressed via inductive type families indexed over a finite self-fibered index type S.
In particular categories are models of an algebraic theory over the shape
```
shape □¹⁺ : * ↑ □¹⁺
  Ob  / (Void / exfalso)
  Mor / (Bool / { Ob })
```

To deal with ∞-categories, one can introduce a shape types `CellType` containing cell types
of every dimension `n : Nat`.

Dually to our lax natural numbers, we can introduce a self-indexed type `Δ⁺`:
```
shape Δ⁺ : * ↑ Δ⁺
  simplex(n : Nat) / ((Σ(m) Fin(m) → Fin(n)) / simplex(m))
```

Type families over Δ⁺ are semi-simplicial types.
Type families over thin (i.e. with at most one arrow between any two inhabitants)
self-indexed types are also known as very dependent types.

# Putting everything together: representing Reedy categories
Most notably, we can combine extensions (degeneracy maps) and selections (face maps)
yielding strictly associative Reedy categories like the simplicial category Δ:
```
shape Δ  : * ↑ Δ
  simplex(n : Nat) / ((Σ(m) Fin(m) → Fin(n)) / simplex(m)) 
  extend : (s : Δ) → when(s)
    simplex(n) ↦ (Σ(m) Fin(m) → Fin(n)) → s ↑ simplex(m)
    ... simplicial identities
```

Type families `F : ↓Δ` on Δ are the simplicial types.

As we already mentioned above, the shape type Δ is vital for defining the syntax of dependent typed theories.

# Universes as categories

As we have seen above, not only inductive shapes have the notion of extensions; universes do as well.
It is not hard to see that it also applies to universes of type families, universes of fibered types,
and universes of fibered type families.
In fact, universes of fibered types or type families will also exhibit selectors iff they are fibered
over self-fibered types.
Here we will show that it also applies to universes of models for any given algebraic theory,
including infinitary algebraic theories with dependent sorts and their generalized form as long 
their sort algebras are stratified.

In fact, in all of these cases, the categories `𝒱` also carry a natural weak model structure and
are equipped with proarrows (“multivalued morphisms”) `sᵈ t` for each `s t : 𝒱`.

# Categories as models for an inductive type

There can be more then one dependency between two inhabitants of an inductive prototype:
```
shape □¹⁺ : * ↑ □¹⁺
  Ob  / (Void / exfalso)
  Mor / (Bool / { Ob })
```


Now let us define the following indexed quotient-inductive type family:
```
data CatTh : □¹⁺ → *
  id : ∀{o : CatTh Ob} (CatTh Mor){source: o, target: o}
  (▸) : ∀{x y z : CatTh Ob} (CatTh Mor)(x, y)
                          → (CatTh Mor)(y, z)
                          → (CatTh Mor)(x, z)

  unitorL : ∀{x y} f = id ▸ f
  unitorR : ∀{x y} f = f ▸ id
  associator : ∀{f g h} (f ▸ g) ▸ h = f ▸ (g ▸ h)
```

Now consider the type of models for this type:
```
typeclass CatTh-Mod<Ts : Δ¹⁺ → *>
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
prototype □¹
  ob / ???
  mor / ???

  よR : ob ↑ mor
  よL : ob ↑ mor
  // higher identities, essentially free + 
  [source⟩⟨よR] ↦ [source⟩
  [target⟩⟨よL] ↦ [target⟩
```

Now given `Ts : □¹ → *`, for every `o : Ts.Ob` we'll have Yoneda embeddings
```
o よR : ∀(target : Ts.Ob) Ts.Mor(source: o, target)
o よL : ∀(source : Ts.Ob) Ts.Mor(source, target: o)
```
that allow to derive 
```
univalence : ∀{X Y : Ts.ob} (a ≃ b) ≃ Σ(f : Ts.hom{source: X, target: Y})
                                      Σ(g : Ts.hom{source: Y, target: X})
                                      (f ▸ g = id) and (f ▸ g = id)            
```

# Induced algebraic structure (Lax monoidal category example)

Structures defined as models for an inductive type compose extremely well. Consider `↓□¹`-valued models `LaxTh-Mod<↓□¹>` 
of the lax monoid prototype, and then consider the `LaxTh-Mod<↓□¹>`-valued models of `CatTh`. 
This way we obtain lax monoidal categories `CatTh-Mod<LaxTh-Mod<↓□¹>>`!

# Displayed algebraic structures

The other nice thing is that since we have defined categories as models for an inductive type,
we automatically have the typeclass of displayed categories, and all algebraic typeclasses are instances of it:
```
Group : Catᵈ
Ring : Catᵈ
Cat : Catᵈ
```
Furthermore, we can iterate, and thus `Catᵈ : Catᵈᵈ`, etc. And since constructions and proofs also can be lifted,
any statement we have proven for all small categories `prf<C : Cat>` also can be applied to displayed categories, 
say like the category `Grp : Catᵈ` of all groups and the category of all categories `Cat : Catᵈ` itself.

# Promorphisms in universes of models

Displayed models for inductive types have the form
```
typeclass ℕᴿᵈ <M : ℕᴿ, this Ts : |M| → *>
  zero : Ts(M.zero)
  next : ∀{n : M} Ts(n) → Ts(M.next n)
```
allowing do define the type of induction motives and the induction operator:
```
def ℕᴹ<this P : ℕᵈ> = ℕᴿᵈ<ℕ, P>

ℕ-ind<P : ℕᴹ>(n : ℕ) : P(n)
```

For each model `M : ℕᴿ`, the inhabitants `Pm : ℕᴿᵈ<M>` are promorphisms (many-to-many corresponcences,
sometimes also called weak homomorphisms) on `M` with the target given by
```
instance Pm.target : ℕᴿ<M × Pm>
  zero: (M.zero, Pm.zero M.base)
  step: { n : M, x : (Pm n) ↦ (M.step n, Pm.next (M.next n) x) }
```

We can single out homomorphisms as the functional (= many-to-one)
promorphisms `Σ(src : ℕᴿ<T>, pm : ℕᴿᵈ src) (f : ∀(n) (m : (pm n)) × ∀(n' : pm n) n ≃ m`,
making the type of ℕ-models into a ∞-precategory (Segal type),
which turns out to be a ∞-category (Complete Segal type) as it is well-known that the equivalences `(≃)<ℕᴿ>`
of ℕ-models correspond to their isomorphisms.

The presented construction generalizes to all generalizations of inductive types.
