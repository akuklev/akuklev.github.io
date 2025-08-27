With synthetic equality constructors it is possible to define the type of eventually-zero sequences:
```
synthetic ZeroEndingSequence
  nil : ZeroEndingSequence
  append(prefix : ZeroEndingSequence, head : Nat)
  extend(f : ZeroEndingSequence) : f = append(f, 0)
```

It is possible to convert the type of lists to a type family over `Nat`:
```
inductive Vec<T> : Nat → *
  nil : Vec<T> 0
  cons<n>(head : T, tail : Vec<T> n) : Vec<T> n⁺
```

We cannot make `ZeroEndingSequence` into a type family over `Nat` because
`extend` generates equality between “lists” of different lengths. We need
a “lax” index type instead of `Nat`:
```
prototype LaxNat
  lax(n : Nat) : LaxNat
  extend(n : Nat) : (l : LaxNat) → when(l)
    lax(m) ↦ l↑ lax(n + m)
    extend(m) ↦ extend(n + m)
```

While synthetic types admit constructors of identities between their elements,
prototypes admit constructors of extensions “between” their elements.
In synthetic types, for any two elements `x y : T` we have an identity type
`x = y : 𝒰`. In prototypes, for every element `x : P` we have a `P`-indexed
type family `l↑ : P → 𝒰`. Its elements are the extenders from the element
`l`, and their indexes are the targets of extensions. Sources of extenders
must be structurally smaller than their targets to enable typechecking.

Every function we define on a prototype must have an action on all constructors,
including extension constructors. The action of an extension constructor on the
other extension constructors are their composition. The action of an
extension constructor on extension constructors must have the form 
of function application, i.e. `extend(m) ↦ extend(f m)` so the typechecker
can ensure that the composition is associative by construction.

This way, prototypes form strictly associative inverse categories.

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
synthetic ZeroEndingSizedSequence : LaxNat → *
  nil : ZeroEndingSizedSequence lax(0)
  append<n>(prefix : ZeroEndingSizedSequence n, head : Nat) : ZeroEndingSizedSequence (lax(1) + n) 
  extend<n>(f : ZeroEndingSizedSequence n) : ???
```

Before we fill in the gap in the above definition, note that type families also seem to be functions on their index type,
so they must act on the extension constructors.
However, the only proper action would be domain extension for functions defined
on those type families. Let `F : I → *` be a type family, and `e : n↑ m` for some `n m : I`.
Then `F(e) : ∀<Y> (F(n) → Y) → (F(m) → Y)`. We also have a dependently typed version.
```
F(e) : ∀<Y : F(n) → *> (∀(x : F(n)) Y(x)) → (∀(x : F(m)) F(e) Y)(x))
```

Now we can fill in the gap in the definition of `ZeroEndingSizedSequence`. The type
of the equality constructor `f = append(f, 0)` does not typecheck yet, but we can
decompose it into an application `{ it = append(f, 0) } f` and apply the domain
extension to the function part by applying `ZeroEndingSizedSequence (extend(1) n)`:
```
synthetic ZeroEndingSizedSequence : LaxNat → *
  nil : ZeroEndingSizedSequence lax(0)
  append<n>(prefix : ZeroEndingSizedSequence n, head : Nat) : ZeroEndingSizedSequence (lax(1) + n) 
  extend<n>(f : ZeroEndingSizedSequence n)
  : ZeroEndingSizedSequence (extend(1) n) { it = append(f, 0) } f
```

* * *



Many operations on containers have the following property:
the shape of the resulting container only depends on shapes of the arguments.
For example, length of the list computed by `concatenate`, `map`, and `reverse`
can be computed based on the lengths of the input lists.

Let us introduce a notion of fibered types. A fibered type is given by a type 
(e.g. lists `T*`) and a function on that type (e.g. `length : T* → ℕ`),
written as `(T* / length) : 𝒰 / ℕ`. In case of fibered inductive types `X / f`,
the type `X` and the function `f` can be defined simultaneously in a mutually
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

The above functions are not just any functions, but functions on fibered types:
```
reverse<T> / id  : (T* / length)  → (T* / length)
concat<T> / add  : (T* / length)² → (T* / length)
flatten<T> / sum : (T* / length)* → (T* / length)

map<X, Y>(f : X → Y) / id : (X* / length)  → (Y* / length)
```

For every `Y : B → 𝒰`, we have the fibered type `(ΣY, fst) : 𝒰 / B`.

Type families indexed by fibered types `Y : (X / f) → *` where `f : X → B` 
reduce to: `Y : ∀(x : X) → Bᵈ (f x) Y`.

An inductive type can be self-fibered: `I / (I → 𝒰)`, e.g.
```
inductive D / arr : (𝒰 / (𝒰 / D))
  Fst : D
  Snd : D
  def arr : D → (𝒰 / D)
    Fst ↦ (Void / _)
    Snd ↦ (Unit / { _ ↦ Fst })
```

An inductive self-fibered type is automatically an inverse category where
composition enjoys associativity by construction. (TODO: Clarify)

A type family `Y : (D / arr) → *` indexed over this type has the form
`Y : ∀(x : D) → (𝒰 / (D / arr))ᵈ (arr x) Y`. 
Since `D` only has two elements, we can split cases:
```
Y(Fst) : (𝒰 / (D / arr))ᵈ (arr Fst) Y
Y(Snd) : (𝒰 / (D / arr))ᵈ (arr Snd) Y
```
which in turn reduces to
```
Y(Fst) : (𝒰 / (D / arr))ᵈ (Void / _) Y
Y(Snd) : (𝒰 / (D / arr))ᵈ (Unit / { _ ↦ Fst }) Y
```
further reducing to
```kotlin
Y(Fst) : (∀(u / f : (Void / _)) Y(f(u))) → 𝒰
Y(Snd) : (∀(u / f : (Unit / { _ ↦ Fst })) Y(f u)) → 𝒰
```

Product over empty domain is `Unit`, and the product over unit domain is just one element:
```kotlin
Y(Fst) : Unit → 𝒰
Y(Snd) : Y(Fst) → 𝒰
```
So our type family is simply a dependent pair `Σ(T : 𝒰) (T → 𝒰)`!





# Why type families?

A programming language used for compilers, static analysis tools, and IDEs
can greatly benefit from having inductive type families.

Let us postpone the exact definition and start by the motivation and an example.
Closed inductive type families abstractly embody formalized languages.
For example, consider the following simple language of arithmetic
and logical expressions:
```
synthetic ExpressionKind
  Numeric
  Logical

synthetic Expr : (ExpressionKind)-> *
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

Now let us intruduce synthetic type families step by step.

## Sum types

Let us start from finite datatypes (also known as enums) defined by enumerating their possible values:
```
synthetic Boolean
  True
  False
```

We can generalize them to so-called sum types by allowing infinite families of “possible values”
parametrized by some other type:
```
synthetic Possibly<X>
  Nothing
  Value(x : X)
```

Each synthetic type comes along with a dual “case analyser” type:
```
structure Booleanᴿ<Y>
  true  : Y
  false : Y
```
```
structure Possiblyᴿ<X, Y>
  nothing : Y
  value(x : X) : Y
```

Inhabitants of synthetic types `x : T` can be converted into functions
`xᶜ : ∀<Y> Tᴿ<Y> → Y`, which is known as Church encoding:
```
def <Y> Trueᶜ(m : Booleanᴿ<Y>)  = m.true
def <Y> Falseᶜ(m : Booleanᴿ<Y>) = m.false

def <X, Y> Nothingᶜ(m : Possiblyᴿ<X, Y>)  = m.nothing
def <X, Y> Value(x : X)ᶜ(m : Possiblyᴿ<X, Y>)  = m.value(x)
```

What if we want to return values of different types for `True` and `False`?
If we have universes (types of types), we can first define a function from
booleans into some universe `R : Boolean → 𝒰` and then a dependent case analyser
```
structure Booleanᴹ<Y : Boolean → *>
  true  : Y(True)
  false : Y(False)
```

To apply dependent case analysers to inhabitants of the respective type we
need special operator called induction for reasons explained below:
```
I-ind : ∀<Y> Iᴹ<Y> → ∀(x : I) Y(x)
```

# Inductive types

The next step is to allow well-founded recursion in type definitions.
In this way we can introduce natural numbers, lists, and trees:
```
synthetic Nat `ℕ`
  Zero `0`
  Next(pred : ℕ) `pred⁺`
```
```
synthetic List<T>
  EmptyList : List<T>
  NonEmptyList(head : T, tail : List<T>) : List<T>
```
```
synthetic BinTree<T>
  Leaf
  Node(label: T, left : BinTree<T>, right : BinTree<T>)
```
```
synthetic VarTree<T>
  Leaf
  Node(label: T, branches : List<VarTree<T>>)
```
```
synthetic InfTree<T>
  Leaf
  Node(label: T, branches : Nat → InfTree<T>)
```

All above examples except infinitely branching trees are closed inductive types:
all of their generators have a finite number of parameters of closed inductive types.
Close inductive types embody single-sorted languages. They are inhabited by
abstract syntax trees corresponding to finite expressions of the language
formed by their generators.

“Case analysis” for the type of natural numbers provides n-ary iteration operator:
```
structure Natᴿ<Y>
  zero : Y
  next(p : Y) : Y
```
Analysing a natural number `n` by `m : Natᴿ<Y>` yields `cᶜ(m) = (m.next)ⁿ b.zero`,
allowing to iterate arbitrary functions given number of times. In general,
“case analysis” turns into “recursive descent analysis”. For lists and trees we
obtain the respective fold operators.

Type-valued functions on natural numbers `Y : Nat → 𝒰` can encode arbitrary predicates,
and a dependent `Nat`-analyser `Natᴹ<Y>` encodes an induction motive: it establishes
a proof of the base case `Y(zero)` and the inductive step `Y(n) → Y(n⁺)`.
Dependent case analysis operator turns induction motives into to proof the predicate
for all natural numbers, that is why it is also known as induction operator.
The presence of induction witnesses that inductive types contain only inhabitants that
can be obtained by finite compositions of their generators. Which is also the reason
why data types described in terms of their generators are called inductive types.

# Synthetic types

Inductive types are freely generated by their generators. Synthetic types (also known
as quotient inductive types) are described in terms of generators and relations.

This way we can define rational numbers and unordered collections:
```
synthetic Rational `QQ`
  frac(num : Int, den : PosInt)
  expand<num, den>(n : PosInt) : frac(num, den) = frac(num · n, den · n)
  
synthetic Collection<T>
  bagOf<n : FinType>(elements : n → T)
  permute<n, elements>(p : n!) : bagOf(elements) = bagOf(elements ∘ p)
```
Let `n!` be the type of permutations 

That is, in addition to listing generators, we require that some actions
on generators (expanding the fraction or permuting list elements) must
be irrelevant for all predicates and functions defined on these types.

# Algebraic theories

`Iᴿ<T>` equips `T` with a structure of an I-algebra. These structures form
a displayed category, with an initial object given by `I` and its generators.

`Iᵈ<T>` is the free I-algebra on `T`, an initial object among I-algebra
structures on `T`. The container `Iᵈ` is thus automatically a monad.

A monadic map from `Iᵈ<T>` to `T` is the same as the structure `Iᴿ<T>`.

!!! And it is the same as an Quillen equivalence from ??? to `T`.

```
(l : List<T>) ~> Vec<T>(l.length)

T -[just]-> Expr<T>
  <-[eval]- 
  
Any `eval` that commutes with `just` is monadic?

Expr<T> -
```

# Type families

But what about languages that contain multiple sorts of expressions
and the ones where expression can contain variables?



In this case, instead of a single closed inductive type Expr we have a type family
`Expr : Ctx -> *`, that describes expression within a given context.
In the simplest case, the context is just a natural number — the number of variables.
The type `Expr(0)` denotes closed expressions, `Expr(1)` expressions with one variable,
`Expr(2)` expressions with two variables, and so on. In fact, `Ctx` is not just the type
`Nat`, but carries additional information. For every `ctx : Ctx` we have (subcontext)
selectors `h : ctx↓` and context extenders `h : ctx↑` mapping `ctx` either to a 
smaller or a larder context `|h|` respectively.

Let us call types augmented by selectors and extenders prototypes. One of the simplest
prototypes is `Δ⁺`, which is a glorified type of natural numbers, where selectors
`p : n↓` are the ways to select `m < n` elements among `n` and extenders `e : n↑` are
the ways to put additional variables before, between, and after existing ones.
Selectors and extenders have their target shapes denoted by `|x|`.

Extenders of prototypes carry over to type families indexed over them.
In particular, extenders in `Ctx` carry over to expressions.
That is, every expression `expr : Expr(ctx)` extends to an expression in the larger context:
For `e : ctx↑`, we have `(e expr) : Expr(e ctx)`.

In general, contexts may contain more information than the number of variables.
For instance, their types. In this case, the type `Ctx` is not `Δ⁺` itself, but
fibered over `Δ⁺` by the projection `length : Ctx => Δ⁺`.

Selectors and extenders in `S` carry over to the types fibered over `S`. That is,
given a type of contexts `ctx : Ctx(length = n)`, we can apply a selector `p : n↓`
obtaining the type of subcontexts `(p ctx) : Ctx(length = |p|)`.
All selectors in `Ctx` must come from selectors in `Δ⁺`.
The type of contexts itself may also describe extenders that add additional
variables of given types to the context.
All extenders in `Ctx` must have a preimage in `Δ⁺`.

Selectors 

* * *

??? What do selectors do?

* * *

Algebraic theories = self-fibered prototypes

Unbiased monoid prototype?

Define “we have tensor product on `Ob`” by
“we have a monadic function eval : `List<Ob> -> Ob`”, where monadicity means
```
∀(l : List<List<T>>) we have an extension from
  eval(l.map(eval))
to
  eval(l.flatten)
```

Assume we have a type of monoidal expressions `VariadicTree<T>`, and for every non-flat `t` it only extension
maps it to `t.flatten`. Then we have an action of these extensions on functions from `VariadicTree<T>`, rendering
functions monadic (does it?).

??? Can we obtain such VariadicTrees as algebras over the unbiased monoid prototype?


# Synthetic types

Postulate that the order of list elements must be irrelevant
Postulate that multiplying numerator and denominator by the same positive integer must be irrelevant

