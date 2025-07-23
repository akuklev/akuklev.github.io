Introduction to Higher Observational Construction Calculus
==========================================================

§ Brief History
---------------

The endavour of formalizing mathematical proofs on a computer is by no means new. The idea was
already envisioned in [[Leibniz1684]]. The first successful attempt to develop a formalised language
and a proof verifier on a computer was the Automath project by N. de Bruijn in 1967, while in 1973
A. Trybulec developed the Mizar system, a proof assistant still in use today. The Mizar Mathematical
Library was the largest coherent body of strictly formalised mathematics in existence as of 2009 [[Wiedijk2009]].

The evolution of proof-assisting languages largely mirrors the evolution of programming languages.
The Mizar system is based on standard set theory ZFC, but set theory is a very "low level" language
where any non-trivial statement, let alone proof, is essentially unreadable due to the exorbitant
length and a flood of "implementation details" that have nothing to do with the mathematical ideas
being conveyed. To address this problem, Mizar System developed an advanced layer of macros. As it
always the case for advanced meta-programming languages, a type system had to be introduced to
regulate composability and enforce abstraction. Eventually, high-level semantics for the macro
language emerged, allowing to “debug” the high-level code instead of the low-level assembly code
it elaborates into.

Languages of modern proof assistants are cross-platform high-level languages that can be certainly
compiled into the language of ZFC, but support other “target architectures”, known as topoi.

An elementary topos is a category endowed with just enough structure to faithfully model both
first-order theries (such as graphs, groups, rings, fields, vector spaces, partially ordered
sets, etc) and higher-order theories (such as topological spaces). Elementary topoi do not
necessarily have canonical mathematical objects such as natural or real numbers. Topoi
containing canonical natural numbers arithmetic topoi (or W-topoi). They admit construction
of all countable combinatorial objects, countable groups, countable fields etc. If they
additionally admit Cauchy-completions, they are called analytic topoi. Such topoi contain
canonical real numbers and admit constructions of all separable topological spaces).

The category of all ZFC sets and functions between them is a prime example of an analytic topos,
but not the minimal one. The race to develop an elegant and effective formalized languages for
all arithmetic topoi and all analytic topoi respectively took three decades and entered its
endgame in 2013 with the development of Homotopy Type Theory. Right now it seems to be in its
final phase.

§ Formalised Languages
----------------------

A formalised language is an artificial language for which there is a precise formal definition of
syntax [[EM43455]]. Expressions of a formalised language are formal combinations of some initial
symbols, formed by definite rules of formation of expressions in the given language. In contrast
to the theory of formal langauges, theory of formalised languages does not treat expressions as
linear strings of symbols taken from a fixed alphabet; expressions of formalised langauges are
taken to be abstract syntax trees, where every node is an application of some formation rule of
the respective language.

Formalised languages are in general multi-sorted. Expresions of the language belong to particular
sorts, and formation rules require the constituents to be of certain sort. For example:
```
 a : Attribute   n : Noun-Phrase
—————————————————————————————————
        a n : Noun-Phrase
```

While some formalised languages only have a finite number of sorts, complex formalised languages
have a whole infinite algebra of types, where types can be composed by such operations as cartesian
product or disjoint sum. In this case it becomes non-trivial to see if a particular expression has
a required type to be used as a constituent for some particular formation rule. Algebra of types
has to have a decidable relation `X ≼ Y`, called “conversion”, that specifies when an expression
of type `X` is allowed to be used where type `Y` is required. As it turns out, it is far from
being trivial to devise a formalized general-purpose typed language for mathematical proofs
and constructions with decidable conversion.

Formalised languages dealing with typed free variables are known as type theories. Formulae of
multi-sorted first-order theories involve typed quantifiers (∃ and ∀), thus their formalised
languages are type theories. The branch of mathematics studying syntax and semantics of type
theories is somewhat inconveniently also known as type theory.

§ Construction Calculi
----------------------

The term _Construction Calculi_ employed in the title of this paper refers to type theories that
are intended to serve as general purpose structuralist foundations of mathematics. At times we
will also mention type theories not striving to serve as general purpose foundational frameworks,
these will be referred to as _domain-specific type theories_.

Construction calculi must be able to express
* typed higher-order logic including proofs,
* formal axiomatic theories (such as Eucledian geometry) together with formal constructions on them,
* canonical mathematical objects such as natural and (analytic) real numers, lists, sequences,
functions, relations, etc. Such canonical objects are introduced there as inductive types.

Construction calculi generally feature three classes of types: inductive types, behavioral
(co-inductive) types, and universes.


§§ Inductive types
------------------

In type theory, _inductive types_ are the types freely generated by a set of possibly recursive _generators_:
```
#Inductive Nat
  0    : Nat
  (_') : Nat → Nat
```

Here, the type `Nat` is introduced as the type freely generated by one non-recursive generator `0` of
type `Nat` and a recursive generator `(_')` (writen as a postifx apostrophe) of type `Nat → Nat`.
With this definition, the set of possible Nat-values is given by
&nbsp; `0, 0', 0'', 0''', ...`
The symbols `0` and `(_')` do not refer to some predefined entities, they are introduced right here as generators
of the type `Nat`. They represent nothing other than themselves and are irreducible. There is nothing else happening
“behind the schenes” - this definition of natural numers is entirely self sufficient.

Inductive types may be _polymorphic_, i.e. have typal _parameters_ (enclosed in square brackets):
```
#Inductive List[T̲]
  Empty : List[T]
  (::)  : T → (List[T] → List[T])
```

This definition introduces the polymorphic type `List[T]` parametrized by the type `T` of its elements.
The underline under `T̲`, in the first line is the so-called _freshness marker_, it is there to express
that `T` is not a constant that was defined somewhere else, but a variable being introduced at this
very spot. The second line introduces a rather boring generator `Empty` of `List[T]`, much like 0 in
the definition of `Nat`. The third line introduces an infix operator `::`, which is a family of
recursive generators:
For each inhabitant `head : T` it defines a recursive generator
&nbsp; `(head ::) : List[T] → List[T]`
that appends `head` to the right hand side argument `tail : List[T]` so that non-empty lists can be
generated by succesively appending elements to the `Empty` list. Note, that the arrow operator is
right-associating, so `T → (List[T] → List[T])` can be written simply as `T → List[T] → List[T]`.
The `Empty` together with the infix operator `::` defines the following set of possible values of `List[T]`:
&nbsp; `Empty, x :: Empty, x :: y :: Empty, x :: y :: z :: Empty, ...`
for `x, y, z, ...` being of type `T`.

There is also a notion of _inductive type family_ indexed over an other inductive type. For example,
consider the type family of vectors of fixed length:
```
#Inductive Vec[T̲] : Nat → *
  Empty : Vec[T](0)
  (::)  : T → Vec[T](n̲) → Vec[T](n')
```

Here `Vec[T̲]` is not one type, but a whole _family of types_, one for each natural number `n`.
The “type” `Nat → *` of `Vec[T]` means “a function mapping natural numbers to types“ modulo issues
stemming from the fact that the class of all types `*` is not really a type itself and requires
somewhat careful handling to avoid running into the [barber issues](https://en.wikipedia.org/wiki/Barber_paradox).
The generator `Empty` satisfies the type `Vec[T](0)`, vector of `T`s of zero length.
Generators `(head ::)` take a vector `tail : Vec[T](n)` of _some_ length `n` and generate
a vector of length `n' = n + 1`.

§§ Behavioural types
--------------------

Behavioural types are described not in terms of generators, but in terms of _extractors_. For behavioral types
one remains completely agnostic about nature of their values as long as they provide a given “interface“.
Consider the type of possibly infinite streams:
```
#Structure Stream[T̲]
  head : T
  tail : Maybe[ Stream[T] ]

where
#Inductive Maybe[T̲]
  Nothing      : Maybe[T]
  Value(t̲ : T) : Maybe[T]
```

Here the inhabitants of the type `Stream[T]` are defined as values with distinguished extractors `head`, yielding
a value of the type `T`, and `tail` yielding either the rest of the stream or the value `Nothing` if the stream
ends there.

Values of behavioural types can be defined by specifying actions of their extractors (recursion is allowed). To give
an example, let us define the Fibonacci sequence. Fibonacci sequence is a sequence, in which each number is the sum
of the two preceding ones. A Fibonacci sequence can be defined for any two initial elements, while _the_ Fibonacci
sequence is a Fibonaccy sequence starting with 0 and 1:
```
(0,) 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, ...
```

Here is how to define them:
```
#Defintion fibonacci-sequence(c̲u̲r̲r̲e̲n̲t̲ p̲r̲e̲v̲i̲o̲u̲s̲ : Nat) : Stream[Nat]
  h̲e̲a̲d̲ ↦ current
  t̲a̲i̲l̲ ↦ fibonacci-sequence((current + previous), current)

#Default the-fibonacci-sequence
  fibonacci-sequence(1, 0)
```

The `fibonacci-sequence(n, m)` yields `n` when asked for a `head` and `fibonacci-sequence(n + m, n)` when asked for
a tail.

§§ Functions
------------

Functions `f : X → Y` can be seen as a trivial case of behavioral types: behavioral types with a family
of non-recursive extractors parametrized by values `x : X`:

```
#Structure Function[X̲, Y̲]
  apply : X → Y
```

While it is customary in computer science to use the word “function” for partial functions (that might sometimes
fail to yield a result), in mathematics and type theories by “functions” we mean total and deterministic
functions.

That's how one defines a function on `Nat`:

```
#Define double : Nat → Nat
  0 ↦ 0
  (n̲)' ↦ ( double(n) )''
```

Functions on inductive types can be defined by exhaustive pattern matching on their generators. In case of recursive
generators, definitions are allowed to be inductive. In the above example one performs an exhaustive pattern matching
on natural numbers: natural number is either a zero `0`, or a successor `n'` of a natural number `n`. Thus one
defines the value of the function `double` case by case first for zero `0` and then for successor `n'`, in the latter
case the value `double(n)` is already “known”. The ability to define functions (terminating, total functions) on
inductive types by pattern matching on their generators reflects the defining property of inductive types: their
values are guaranteed to be finitary compositions of their generators.


§§ Canonical Objects vs Open World Assumption
---------------------------------------------

Types are not either inductive or behavioral. Some types have both presentations:
```
#Inductive Pair[X̲, Y̲]
  pair : X → Y → Pair[X, Y]

#Structure Pair[X̲, Y̲]
  fst : X
  snd : Y
```

Some types can be only defined by combining inductive and behavioral definitions, e.g.
`List[ Stream[Nat] ]` and `Maybe[Nat → Nat]`.

Let us call types that can be defined using solely inductive definitions, canonically inductive.

§Definition: Canonically inductive types are inductive types that either a finite number of
generators (like `Nat`) or only generator families parametrized by other canonically inductive
types. For example, the types `Nat`, `List[Nat]` and `List[List[Nat]]` are canonically inductive,
while the type `List[Nat → Nat]` is not.

Canonically inductive types have remarkable properties:
* Sets of their values are either finite, or countably infinite: a bijection with the type of
natural numbers can be constructed within the type theory.
* Equality of their values can be algorithmically checked in a finite time.
* In constructive type theories (including Construction Calculi) closed expressions `expr : T` of
canonically indictive types `T` can be algorithmically evaluated in finite time.

That is the defining property of computational type theories. For example, in 2016 G. Brunerie has
managed to prove type theoretically that a particular homotopy group has the form ℤ/nℤ. From such a
proof one can trivially extract an expression defining this `n : ℤ`, a tremendoulsy long and
complicated expression. By the fact that the proof was carried out in a constructive type theory we
knew that this expression can be evaluated. In early 2022 one has actually managed to evaluate it
algorithmically after a few simplifications were done.

Philosophically speaking, canonically inductive types constitute closed totalities: we know exactly
what their values are, how they are built from below as finitary formal combinations of some initial
symbols, namely as composition trees of generators of their respective types.

Behavioural (and mixed) types are quite the opposite. In contrast to values of canonically inductive
types (which are exhausted by ones that can be explicitly written down), a value `s : Stream[Nat]`
might be a thing “living outside of the computer” being “measured” by `head` and `tail`. Equality
of two streams `s g : Stream[Nat]` cannot be in general verified in finite time: such verification
would in general require to check numerical equality for an infinite number of terms. This property
does not only apply to the cases when one of the streams “lives outside of the computer”. It holds
already for streams that can be explicitly written down and are algorithmically computable, which
is known as halting problem.

With help of a Cantorian diagonal argument it can be shown constructively within the system itself,
that there can be no explicit bijection between the type `Stream[Nat]` and natural numbers `Nat`.
Yet it does not mean that there are strictly more such streams than natural numbers: such question
is not well posed within constructive approach. We know that at least all computable streams exist,
and we don't try to pinpoint how many “other” streams there are, while being able to deal with any
of them. A function of `s : Stream[Nat]` can neither require `s` to be computable, nor find out if
it is. Constructive foundations embrace the open-world assumption and accept behavioral types to be
inherently open totalities.


§§ Universes
------------

Besides inductive and behavioral types, Construction Calculi feature universes: the types of types.
The base universe `𝒰` is guaranteed to contain all canonically inductive types and is closed under
applications of all polymorphic type formers, both inductive and coinductive, e.g. `Nat : 𝒰`,
`List[ Stream[ Function[Nat, Nat] ] ] : 𝒰`. The universe `𝒰⁺` contains everything from the universe
`𝒰 ⊂ 𝒰⁺`, besides that it contains `𝒰 : 𝒰⁺` itself and is again closed under applications of any
polymorphic typeformers, so it contains types like `List[𝒰]` and `Function[Nat, 𝒰]`. Analogously
we define `𝒰⁺⁺`, `𝒰⁺⁺⁺` and so on for any finite number of superscript plus signs. This way one
achieves that any finite collection of explicitly definable types lives in a sufficiently large
universe, without any universe living in itself, which would cause inconsistencies.

Universes are open totalities in the most strict sense: they don't have any extractors, so in
particlar one cannot define any function from a universe by pattern matching.

§§ Propositions
---------------

Consider the degenerate inductive type

```
#Inductive Empty
  /- no constructors -/
```

This type has no constructors, and in a type theory enjoing normalization and canonicity there can be no expressions
of the type `Empty` in empty context. At the same time, a function on this type can be defined (as it is the case
for all inductive types) by pattern matching. Yet there are no constructors to match, such function has no body
and still exists. In fact there is a unique function from `Empty` to any type `X`. Fortunatelly in cannot be ever
applied because the type `Empty` has no inhabitants.

In Construction Calculi logical propositions are represented by types inhabited by proofs of respective
propositions. A function `P → Q` between two propositions by definition turns proofs of `P` into proofs of `Q` and
therefore is a proof that `P` implies `Q`. The type `Empty` encodes the canonical false proposition: it has no
proofs and if there were any proofs, (remember, there is a function form `Empty` into any type `X`) it would allow
prove all propositions `P` (together with their negations `¬P`, because they are propositions as well) therefore
trivializing the theory, which is known in logics as “ex falso quodlibet”. By the way, negation of an arbitrary
proposition `P` can be defined as `P → Empty` (`P` is false exactly we we can derive contradiction by assuming it
to be true).

All provably false propositions can be shown to be equivalent to `Empty`. One direction (`X -> Empty`) comes from
the definition of negation, the other direction (`Empty -> X`) comes from the fact that there is a function from
`Empty` into any type. The same way, any true propoistion can be shown to be equivalent to the type `Unit` with
exactly one element. Yet, one cannot show constructively that the class of all propositions `Ω` is exhausted by this
two variants: besides provably false propositions and provably true ones there can be unsettled ones. To give a
concrete example, existance of sets strictly larger than the set of natural numbers and strictly smaller than the
set of natural number sequences is an example of such an unsettled proposition in the standard set theory. It is known
as Continuum Hypothesis. Existence of such sets are neither implied nor ruled out by axioms of the set theory.
There are models of set theory without such sets and there are other perfectly valid models where such sets exist.
Futhermore, one cannot settle all propostions by adding more axioms. Gödel's incompleteness theorem states that any
axiomatic theory (with finitely generated system of axioms) has unsettled propositions at least if is powerful enough
to express natural numbers and multiplication on them as an operation.

While all true propoistions are alike and all false propositions are alike, unsettled propositions are unsettled in
their own way. It might be that one unsettled proposition is implied by another (e.g. Generalized Continuum
Hypothesis implies the Continuum Hypothesis, yet both are independent of standard set theory), or they can be
completely independent. Constructively, the class of all propositions `Ω` is bounded lattice ordered by implication
`P → Q` with bottom element `Empty` (the false proposition) and top element `Unit` (the true proposition).

The “class” of canonical propositions `Ω` is seen a as a type in most Construction Calculi. It is neither an
inductive type, nor a behavioural one, and its inhabitants are themselves types (propositions are considered
to be types inhabited by their respective proofs). Such types (types of types) are known as universes and form
a third large group of types besides inductive and behavioral ones.
For any type `X` there is a proposition “`X` is non-empty” that we'll denote `⁰X : Ω`.

As it was already mentioned, the class of canonical propositions `Ω` contains `Empty` and `Unit` and is closed
under forming functions: for `P Q : Ω`, `(P → Q) : Ω`. It is also closed under forming pairs: a pair of proofs,
one for `P` and one for `Q` is precisely the proof of `P ‹and› Q`. Via implication and negation one can also define
the logical conjunction `(‹or›)`. Together with these two logical conjunctions the type `Ω` forms a Heyting algebra,
moreover a complete one as we will see in the next section.

All constructive calculi of concern are compatible with axiom of double negation elimination `¬¬P → P` that
trivializes all structure mentioned above to classical logic where every proposition has a definite truth value
`true` or `false`, yet this axiom is not derivable constructively in general. Double negation elimination can be
derived constructivly only for a very narrow class of propositions: namely, for decidable ones (these are the ones
that can be at least in theory checked algorithmically).


§§ Predicates, Relations and Dependent Functions
------------------------------------------------

By means of indexed inductive types one can define predicates on inductive types:

```
#Inductive (_-is-even) : Nat → *
  zero-is-even : (0)-is even
  suc-of-suc-is-even(n̲ : Nat) : (n)-is even → (n'')-is even
```

Here, the predicate `-is-even` on natural numbers is defined. Equivalently, for each natural number `n`
a type `(n)-is-even` is defined, which can be either empty (which stands for false) or have an inhabitant
(which stands for true). Here the generator `zero-is-even` populates `(0)-is even`, and the generator
`suc-of-suc-is-even(n̲ : Nat)` populates `(n + 2)-is even` whenever `(n)-is even`.

While this particular predicate is decidable (one can easily check if a given number is even), in general
inductively defined predicates are not. For example it is still unknown (cf. Collatz conjecture) if the following
predicate is decidable:
```
#Inductive Collatz-Terminating : Nat → *
  ct-zero    : Collatz-Terminating(0)
  ct-one     : Collatz-Terminating(1)
  ct-half(n̲) : Collatz-Terminating(n) → Collatz-Terminating(2 · n)
  ct-triple-plus-one(n̲) : Collatz-Terminating(3·n + 1) → Collatz-Terminating(n)
```

In dependent type theories there are so called dependent function types:
For a type `X` and an inductive type family `Y : X -> *` indexed over it, there is a type
`∀(x̲ : X) Y(x)`, read “for each `x` of `X` a value of the type `Y(x)`”. For example the function
&nbsp; `f : ∀(n̲ : Nat) Vec[Nat](n)`
must yield a vector of length `n` for each number `n`.

When applied to predicates, dependent functions reassemble universal quantifier. The type
```
∀(n̲ : Nat) Collatz-Terminating(n)
```

is populated precisely by functions yielding a proof of `Collatz-Terminating(n)` for each `n`,
that is precisely by constructive proofs of the proposition `∀(n̲ : Nat) Collatz-Terminating(n)`.

To give an example how such proofs might look like consider an easier proposition:
```
∀(n̲ : Nat) ( double(n) )-is-even
```

Functions are defined by pattern matching, and we are allowed to unfold the definition of `double` while matching:
```
#Define prf : ∀(n̲ : Nat) ( double(n) )-is-even
  0    ↦ zero-is-even : ( double(0) )-is-even
  (n̲)' ↦ suc-of-suc-is-even( double(n) )(prf(n) : ( double(n) )-is-even) : ( double(n') )-is-even
```

The class of all propositions `Ω` is closed under forming arbitrary conjunctions:
For any family of propositions `P : X → Ω` one can form `∀(x̲ : X) P(x) : Ω`, which means Ω is a complete Heyting
algebra. Since `Ω` a complete Heyting algebra and contains any proposition definable within HOCC, subsets of any type
`T` can be identified with predicates `P : T → Ω`. In fact, we can even introduce special syntax for subset types
`{t̲ : T | P(t)}`, for example `{n̲ : Nat | (n)-is-even ‹and› (10 ≤ n) }`.

Relations on a type can be defined as twice indexed inductive types:
```
#Inductive (≤) : Nat → Nat → *
  ≤-refl(n̲) : (n ≤ n)
  ≤-succ(n̲ m̲) : (n ≤ m) → (n ≤ m')
```

Each inductive type automatically comes with an indictively defined equality relation that exactly follows the pattern
of its generators. For example, for the type of natural numbers the equality relation can be given as:
```
#Inductive (=) : Nat → Nat → *
  0= : (0 = 0)
  (n̲)'= : (n' = n')
```

For behavioral types, equality follows the pattern of their extractors and represents observational equivalence,
that is two “things” are equal precisely if applying same extractors yields same values. In particular, for two
functions `f g : X → Y` the equality is given by
```
pointwise : ∀(x̲ : X) f(x) = f(y)
```

In particular, in type theory two implementations of the same function are considered equal as functions if they
yield equal results on equal arguments.



[Leibniz1684]: Leibniz, G. W. (1684), “Meditationes de cognitione, veritate et ideis”, Acta Eruditorum

[Wiedijk2009]: Wiedijk, Freek (2009). “Formalizing Arrow's theorem”. Sādhanā. 34 (1): 193–220. doi:10.1007/s12046-009-0005-1. https://hdl.handle.net/2066%2F75428

[EM43455]: V.N. Grishin, “Formalized language” Encyclopedia of Mathematics. URL: http://encyclopediaofmath.org/index.php?title=Formalized_language&oldid=43455
