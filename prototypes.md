Higher Categorical Type Theory
==============================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com), [JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)

Building on the unpublished ideas of C. McBride,
we propose a novel extension for univalent Martin-Löf Type Theories (MLTTs) that allows
internalizing Reedy categories as so called shape types.

Indexing and fibering over shape types provides effective machinery
for dealing with syntaxes that include binding,
and become indispensable when internalizing the syntax and semantics of type theories themselves. 
Bidirectional presentations of dependent type theories turn out to be inductive-inductive-recursive definitions.

Semantically, fibered quotient inductive-inductive type definitions (FQIITs) are effective presentations of weak model
categories whose structure-preserving functors correspond to elimination motives.
In strong analogy to the functorial semantics of Lavwere algebraic theories,
these functors themselves form a category of models, with their natural transformations serving as model homomorphisms.

We conjecture of initial models in an arbitrary (∞,1)-topos conditionally on the existence of an
appropriate large cardinal: probably, an inaccessible for small and a Mahlo cardinal for large FQIITs respectively.

Such result would uniformly establish the existence of initial models for structures
admitting an effective bidirectionally algebraic presentation,
including [weak ω-categories](https://arxiv.org/abs/1706.02866),
[virtual equipments](https://arxiv.org/abs/2210.08663), 
(∞,1)-toposes once the [Higher Observation Type Theory (HOTT)](https://ncatlab.org/nlab/show/higher+observational+type+theory) is complete.

In the end, our theory should be homoiconic, i.e. capable of representing their own syntax in terms of inductive types
and performing structural induction over it (also known as “eating themselves”).



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
universes `* : *⁺ : *⁺⁺ : ···` featuring □-modality based polymorphism.

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
  EmptyList : List<T>
  NonEmptyList(head : T, tail : List<T>) : List<T>
```
```
data BinTree<T>
  Leaf
  Node(label: T, left : BinTree<T>, right : BinTree<T>)
```
```
data VarTree<T>
  Leaf
  Node(label: T, branches : List<VarTree<T>>)
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

For a type `J : 𝒰` let `↓J` denote the respective universe of type families indexed by `J`.
A typical example are length-indexed lists:
```
data Vec<T> : ↓Nat
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
  extend(n : Nat) : (l : LaxNat) → when(l)
    lax(m) ↦ l ↑ lax(n + m)
    extend(m) ↦ extend(n + m)
```

While quotient inductive types admit constructors of identities between their elements,
inductive shape types admit constructors of extensions “between” their elements.
In synthetic types, for any two elements `x y : T` we have an identity type
`x = y : 𝒰`. In shape types, for every element `x : P` we have a `P`-indexed
type family `↑l : ↓P`. (We'll use the shorthand `s ↑ t` for `↑s t`.)

Inhabitants of `s ↑ t` the extenders from the element `s` to the element `t`.
Sources of extenders must be structurally smaller than their targets to enable typechecking.

Every function we define on a shape type must have an action on all constructors,
including extension constructors. The action of an extension constructor on the
other extension constructors are their composition. The action of an
extension constructor on extension constructors must have the form
of function application, i.e. `extend(m) ↦ extend(f m)` so the typechecker
can ensure that the composition is associative by construction.

This way, shape types form strictly associative inverse categories.

To have an example for other functions, let us define addition for
`LaxNat`s:
```
def add : LaxNat² → LaxNat
  (lax(n), lax(m)) ↦ lax(m + n)
  (extend(n) _, _) ↦ extend(n)
  (_, extend(n) _) ↦ extend(n) 
```

With `LaxNat` we can transform `ZeroEndingSequence` into a type family:
```
data ZeroEndingSizedSequence : ↓LaxNat
  nil : ZeroEndingSizedSequence lax(0)
  append<n>(prefix : ZeroEndingSizedSequence n, head : Nat) : ZeroEndingSizedSequence (lax(1) + n) 
  extend<n>(f : ZeroEndingSizedSequence n) : ???
```

Before we fill in the gap in the above definition, note that type families also seem to be functions on their index type,
so they must act on the extension constructors.
However, the only proper action would be domain extension for functions defined
on those type families. Let `F : ↓I` be a type family, and `e : s ↑ t` for some `s t : I`.
Then `F(e) : ∀<Y> (F(s) → Y) → (F(t) → Y)`. We also have a dependently typed version.
```
F(e) : ∀<Y : ↓F(s)> (∀(x : F(s)) Y(x)) → (∀(x : F(t)) F(e) Y)(x))
```

Now we can fill in the gap in the definition of `ZeroEndingSizedSequence`. The type
of the equality constructor `f = append(f, 0)` does not typecheck yet, but we can
decompose it into an application `{ it = append(f, 0) } f` and apply the domain
extension to the function part by applying `ZeroEndingSizedSequence (extend(1) n)`:
```
data ZeroEndingSizedSequence : ↓LaxNat
  nil : ZeroEndingSizedSequence lax(0)
  append<n>(prefix : ZeroEndingSizedSequence n, head : Nat) : ZeroEndingSizedSequence (lax(1) + n) 
  extend<n>(f : ZeroEndingSizedSequence n)
  : ZeroEndingSizedSequence (extend(1) n) { it = append(f, 0) } f
```

# Fibered types and direct categories

Many operations on containers have the following property:
the shape of the resulting container only depends on shapes of the arguments.
For example, length of the list computed by `concatenate`, `map`, and `reverse`
can be computed based on the lengths of the input lists.

Let us introduce a notion of fibered types.
For every type `B : 𝒰` we'll have a type family `↓B` indexed by types `T : 𝒰`.
We will use the shorthand `S ↓ T` for `↑T S`.
```
inductive ↓B : ↓𝒰
  fiberedType(F : 𝒰, f : F → B) : F ↓ B 
```

For shortness let us denote `fiberedType(F, f)` by `F / f`. 

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

In general, the function `f` in `X / f` may be a dependent function `f : ∀(x : X) Y(x)`,
so we can introduce dependently fibered types `(x : X) ↓ Y(x)`.
 
Inductive-recursive definitions are mutually dependent definitions of an inductive type
and a recursive function on that type.
Such definitions naturally generate a fibered type.

TODO: Universe example


As already mentioned in the previous section, for a type `J : 𝒰` we have the type `↓J`
of `J`-indexed type families.
The type former `Σ<J> : ↓J → 𝒰` makes it a fibered type: `↓J / Σ : ↓J ↑𝒰`.

For every type-valued function `Y : B → 𝒰`, we have the fibered type `ΣY / fst : ΣY ↑B`.
Owing to equality, we can invert this operation (for ordinary types, not shape types):
for every fibered type `F / f : F ↑B` we have a function
`{ b : B ↦ Σ(x : F) f(x) = b} : B → 𝒰`.


Fibered types have non-trivial behaviour with respect to type families indexed
over them.
For a fibered type `F / f : F ↑B` and a type-family `Y : ↓(F / f)` indexed over
it, and an element `x : F` we have the following rule:
```
Y(x) : Bᵈ (f x) Y
```
where `Bᵈ` is displayed counterpart of `B` as introduced in [[dTT]] paper.

Inductive types can be self-fibered:
```
shape 𝔻 : * ↑ 𝔻
  fst / (Void / exfalso)
  snd / (Unit / { fst })
  def select : 𝔻 → * ↑ 𝔻
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

Notably, universes of types, type families, and fibered types/type families also carry a shape structure
with selections given by fibered types and extensions given by type families and a compatible proarrow
equipment given by display operator ( ᵈ).
Universes of models for any given algebraic theory also carry a shape structure and a compatible proarrow
equipment.

* * *

Every inductive type comes with a ∞-procategory of its models.
An inductive definition does not only generate the type (ℕ) itself,
but also coinductive dual, the structure of a ℕ-model on an arbitrary type `T`.
```
typeclass ℕᴿ<this T : *>
  zero : T
  next : T → T
```
and its canonical instance
```
instance ℕ : ℕᴿ<ℕ>
  zero: 0
  next: ( ⁺)
```

Non-dependent elimination rule (recursion) has the following signature:
```
( )ᶜ : ℕ → ∀<T : ℕᴿ> T
```

Models of single-sorted algebraic theories arise as models for quotient inductive types,
for example monoids arise as models for the following type:
```
inductive MonTh
  e : MonTh
  (∘) : MonTh → MonTh → MonTh

  unitorL : x = e ∘ x
  unitorR : x = x ∘ e
  associator : (x ∘ y) ∘ z = x ∘ (y ∘ z)
```

To each type we can apply the ( ᵈ)-operator to obtain its displayed version.
Displayed models for inductive types have the form
```
typeclass ℕᴿᵈ <M : ℕᴿ, this Ts : |M| → *>
  zero : Ts(M.zero)
  next : ∀{n : M} Ts(n) → Ts(M.next n)
```
allowing do define the type of induction motives and the induction operator:
```
def ℕᴹ<this P : ℕ → *> = ℕᴿᵈ<ℕ, P>

ℕ-ind<P : ℕᴹ>(n : ℕ) : P(n)
```
 
For each model `M : ℕᴿ`, the inhabitants `Pm : ℕᴿᵈ<M>` are promorphisms (many-to-many corresponcences,
sometimes also called weak homomorphisms) on `M` with the target given by
```
instance Pm.target : ℕᴿ<M × Pm>
  base: (M.zero, Pm.zero M.base)
  step: { n : M, x : (Pm n) ↦ (M.step n, Pm.next (M.next n) x) }
```

We can single out homomorphisms as the functional (= many-to-one)
promorphisms `Σ(src : ℕᴿ<T>, pm : ℕᴿᵈ src) (f : ∀(n) (m : (pm n)) × ∀(n' : pm n) n ≃ m`,
making the type of ℕ-models into a ∞-precategory (Segal type),
which turns out to be a ∞-category (Complete Segal type) as it is well-known that the equivalences `(≃)<ℕᴿ>` 
of ℕ-models correspond to their isomorphisms.

The presented construction generalizes to all generalizations of inductive types.

# Induced algebraic structure (Lax monoids example)

Let us introduce the type of natural number lists indexed by their sum:
```
data SumsTo : ℕ → *
  nil : SumsTo 0
  cons : ∀{n : ℕ} (head : ℕ, tail : SumsTo n ) → SumsTo (head + n)
```

Now we can write a function `unflatten` that takes a `list : List<T>` and
an additive decomposition `s : SumsTo(list ▸length)` into a `listOfLists : List<List<T>>` with
`listOfLists ▸flatten = list` and `listOfLists ▸map {.length} = s`.

Now we can define the following
```
shape LaxTh
  compose : List<LaxTh> → LaxTh

  compose(l) ⟨parenthesize(s : SumsTo(l ▸length))] compose(l ▸unflatten(s))
```

The models `LaxTh-Mod` for this prototype are the unbiased lax monoids.


## Categories as models for an inductive type

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

Structures defined as models for an inductive type compose extremely well. Consider `↓□¹`-valued models `LaxTh-Mod<↓□¹>` 
of the lax monoid prototype, and then consider the `LaxTh-Mod<↓□¹>`-valued models of `CatTh`. 
This way we obtain lax monoidal categories `CatTh-Mod<LaxTh-Mod<↓□¹>>`!

The other nice thing is that since we have defined categories as models for an inductive type, we automatically have the structure of a displayed category on categories:
```
Cat : Catᵈ
```
Furthermore, we can iterate, and thus `Catᵈ : Catᵈᵈ` etc. And since constructions and proofs also can be lifted,
any statement we have proven for all small categories `prf<C : Cat>` also can be applied to displayed categories, 
say like the category `Grp : Catᵈ` of all groups and the category of all categories `Cat : Catᵈ` itself. 
Seems like dream of size-agnostic category theory came true.
Well, except we want to have the same for ω-categories `ωCat : ωCatᵈ : ωCatᵈᵈ : ···`.
