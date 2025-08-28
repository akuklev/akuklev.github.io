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



# Motivation for fibered type families

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

Bi-directionally typed languages also
require a fibered type family `Redex / type : ↓(c : Ctx) ↑(Ty c) ` of
reducible expressions synthesizing their types.

Now as we have motivated the need for all this stuff, let's dive in.

# Type families and inverse categories

For a type `J : 𝒰` let `↓J` denote the respective universe of type families indexed by `J`.
A typical example are length-indexed lists:
```
data Vec<T> : ↓Nat
  nil : Vec<T> 0
  cons<n>(head : T, tail : Vec<T> n) : Vec<T> n⁺
```

Ordinary inductive types are freely generated by their generators.
Quotient inductive types may additionally contain constructors of relations (i.e. identities) between inhabitants.

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

A more interesting example is given by the type of eventually-zero sequences:
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
    lax(m) ↦ ↑l lax(n + m)
    extend(m) ↦ extend(n + m)
```

While quotient inductive types admit constructors of identities between their elements,
inductive shape types admit constructors of extensions “between” their elements.
In synthetic types, for any two elements `x y : T` we have an identity type
`x = y : 𝒰`. In shape types, for every element `x : P` we have a `P`-indexed
type family `↑l : ↓P`. Its elements are the extenders from the element
`l`, and their indexes are the targets of extensions. Sources of extenders
must be structurally smaller than their targets to enable typechecking.

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
data ZeroEndingSizedSequence : LaxNat↓
  nil : ZeroEndingSizedSequence lax(0)
  append<n>(prefix : ZeroEndingSizedSequence n, head : Nat) : ZeroEndingSizedSequence (lax(1) + n) 
  extend<n>(f : ZeroEndingSizedSequence n) : ???
```

Before we fill in the gap in the above definition, note that type families also seem to be functions on their index type,
so they must act on the extension constructors.
However, the only proper action would be domain extension for functions defined
on those type families. Let `F : ↓I` be a type family, and `e : ↑n m` for some `n m : I`.
Then `F(e) : ∀<Y> (F(n) → Y) → (F(m) → Y)`. We also have a dependently typed version.
```
F(e) : ∀<Y : ↓F(n)> (∀(x : F(n)) Y(x)) → (∀(x : F(m)) F(e) Y)(x))
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
For every type `B : 𝒰` we'll have a type family `↑B` indexed by types `T : 𝒰`.
In contrast to ordinary type families, `↑B` act as a postfix operators on their index `T`:
```
inductive ↑B : ↓𝒰
  fiberedType(F : 𝒰, f : F → B) : F ↑B 
```

For shortness let us denote `fiberedType(F, f)` by `F / f`.

For example, we can take the type of lists `T*` and the function `length : T* → ℕ`:
`(T* / length) : T* ↑ℕ`.

As already mentioned in the previous section, for a type `J : 𝒰` we have the type `↓J`
of `J`-indexed type families.
The type former `Σ<J> : ↓J → 𝒰` makes it a fibered type: `↓J / Σ : ↓J ↑𝒰`.

For every type-valued function `Y : B → 𝒰`, we have the fibered type `ΣY / fst : ΣY ↑B`.
Owing to equality, we can invert this operation (for ordinary types, not shape types):
for every fibered type `F / f : F ↑B` we have a function
`{ b : B ↦ Σ(x : F) f(x) = b} : B → 𝒰`.

In case of fibered inductive types `F / f`,
the type `F` and the function `f` can be defined simultaneously in a mutually
dependent fashion, which is already supported in some dependently-typed languages
as inductive-recursive types.

A function between fibered types is a pair of functions `(f / b) : (X / p) → (Y / q)`,
so that the following square commutes by construction:
```
 X --[f]--> Y
 |p         |q
 V          V
 A --[b]--> B
```

(Functions `f` and `b` can be defined by induction simultaneously in a mutually
dependent fashion when necessary.)

Consider a few examples of functions on fibered types:
```
reverse<T> / id  : (T* / length)  → (T* / length)
concat<T> / add  : (T* / length)² → (T* / length)
flatten<T> / sum : (T* / length)* → (T* / length)

map<X, Y>(f : X → Y) / id : (X* / length)  → (Y* / length)
```

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
shape 𝔻 / select : * ↑𝔻
  fst : 𝔻
  snd : 𝔻
  def select : 𝔻 → * ↑𝔻
    fst ↦ (Void / { it })
    snd ↦ (Unit / { fst })
```

Inductive self-fibered types form strictly associative direct categories. (TODO: Clarify)

A type family `Y : ↓(𝔻 / select)` indexed over this type satisfies the following typing rule:
```
Y(x : 𝔻) : (* ↑𝔻)ᵈ (select x) Y
```

Since `𝔻` only has two elements, we can split cases:
```
Y(fst) : (* ↑𝔻)ᵈ (select fst) Y
Y(snd) : (* ↑𝔻)ᵈ (select snd) Y
```
which in turn reduces to
```
Y(fst) : (* ↑𝔻)ᵈ (Void / { it }) Y
Y(snd) : (* ↑𝔻)ᵈ (Unit / { fst }) Y
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
shape CellType / select : * ↑CellType
  Ob : CellType
  Mor : CellType
  def select : CellType → * ↑CellType
    Ob ↦ (Void / { it })
    Mor ↦ (Bool / { Ob })
```

To deal with ∞-categories, one can introduce a shape types `CellType` containing cell types
of every dimension `n : Nat`.

Dually to our lax natural numbers, we can introduce a self-indexed type `Δ⁺`:
```
shape Δ⁺ / select : * ↑Δ⁺
  simplex(n : Nat) : Δ⁺
  def select : Δ⁺ → * ↑Δ⁺
    simplex(n) ↦ (Σ(m) Fin(m) → Fin(n)) / simplex(m)
```

Type families over Δ⁺ are semi-simplicial types.
Type families over thin (i.e. with at most one arrow between any two inhabitants)
self-indexed types are also known as very dependent types.

Most notably, we can combine extensions (degeneracy maps) and selections (face maps)
yielding strictly associative Reedy categories like the simplicial category Δ:
```
shape Δ / select : * ↑Δ
  simplex(n : Nat) : Δ
  extend : (s : Δ) → when(s)
    simplex(n) ↦ (Σ(m) Fin(m) → Fin(n)) → ↑s simplex(m)
    ... simplicial identities part I
  def select : Δ⁺ → * ↑Δ⁺
    simplex(n) ↦ (Σ(m) Fin(m) → Fin(n)) / simplex(m)
    ... simplicial identities part II
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
structure ℕᴿ<this T : *>
  base : T
  next : T → T
```
and its canonical instance
```
instance ℕ : ℕᴿ<ℕ>
  base: 0
  next: ( ⁺)
```

Non-dependent elimination rule (recursion) has the following signature:
```
( )ᶜ : ℕ → ∀<T : *> ℕᴿ → T
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
structure ℕᴿᵈ <M : ℕᴿ, this Ts : |M| → *>
  base : Ts(M.base)
  next : ∀{n : M} Ts(n) → Ts(M.next n)
```
allowing do define the type of induction motives and the induction operator:
```
def ℕᴹ<this P : ℕ → *> = ℕᴿᵈ<ℕ, P>

ℕ-ind<P> : ℕᴹ<P> → ∀(n : ℕ) P(n)
```
 
For each model `M : ℕᴿ`, the inhabitants `Pm : ℕᴿᵈ<M>` are promorphisms (many-to-many corresponcences,
sometimes also called weak homomorphisms) on `M` with the target given by
```
instance Pm.target : ℕᴿ<M × Pm>
  base: (M.base, Pm.base M.base)
  step: { n : M, x : (Pm n) ↦ (M.step n, Pm.next (M.next n) x) }
```

We can single out homomorphisms as the functional (= many-to-one)
promorphisms `Σ(src : ℕᴿ<T>, pm : ℕᴿᵈ src) (f : ∀(n) (m : (pm n)) × ∀(n' : pm n) n ≃ m`,
making the type of ℕ-models into a ∞-precategory (Segal type),
which turns out to be a ∞-category (Complete Segal type) as it is well-known that the equivalences `(≃)<ℕᴿ>` 
of ℕ-models correspond to their isomorphisms.

The presented construction generalizes to all generalizations of inductive types.
We expect them to also work mutatis mutandis for positive fibered inductive-inductive-recursive definitions.

# Induced algebraic structure (Lax monoids example)

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

Structures defined as models for an inductive type compose extremely well. Consider `↓Δ¹`-valued models `LaxTh-Mod<↓Δ¹>` 
of the lax monoid prototype, and then consider the `LaxTh-Mod<↓Δ¹>`-valued models of `CatTh`. 
This way we obtain lax monoidal categories `CatTh-Mod<LaxTh-Mod<↓Δ¹>>`!

The other nice thing is that since we have defined categories as models for an inductive type, we automatically have the structure of a displayed category on categories:
```
Cat : Catᵈ
```
Furthermore, we can iterate, and thus `Catᵈ : Catᵈᵈ` etc. And since constructions and proofs also can be lifted,
any statement we have proven for all small categories `prf<C : Cat>` also can be applied to displayed categories, 
say like the category `Grp : Catᵈ` of all groups and the category of all categories `Cat : Catᵈ` itself. 
Seems like dream of size-agnostic category theory came true.
Well, except we want to have the same for ω-categories `ωCat : ωCatᵈ : ωCatᵈᵈ : ···`.
