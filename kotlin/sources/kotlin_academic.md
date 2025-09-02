Academic Kotlin
===============

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com),
[JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)
& [Radboud Univ. Nijmegen](https://sws.cs.ru.nl/Person/Guests)

Modified form of \href{http://akuklev.github.io/kotlin/kotlin_literate.pdf}{Literate Kotlin}
can be used for computer science papers and in mathematics as a language for constructions and proofs.
These applications require dedicated extensions, we'll outline in this memo.
High abuse potential makes some of them undesirable for a general-purpose programming language,
so we propose introducing a separate dialect: Academic Kotlin.

# Concise signatures

In academic applications, the signatures of functions and polymorphic types get quite convoluted.
For reasonable readability, it is essential to keep them as short as possible.
Significant improvements can be achieved with space-separated lists of variables sharing the same type
```kotlin
|\textbf{\textcolor{dgreen}{def}}| plus(x y : Int) : Int
```
and name-based default type conventions:
```kotlin
|\textbf{\textcolor{dgreen}{reserve}}| m : Int, |\textbf{\textcolor{dgreen}{prefix}}| n : Int, |\textbf{\textcolor{dgreen}{suffix}}| count : Int
```
With this declaration, all identifiers reading `m` (and also indexed ones, like `m2`),
and multipart identifiers with the first part `n` or the last part
`count` (e.g. `nUsers` and `pointCount`) are assumed `Int` by default.
[Dependent default type
conventions](http://agda.readthedocs.io/en/v2.7.0/language/generalization-of-declared-variables.html)
facilitate concise polymorphic signatures.

# Aliases

Mathematics and academic computer science require short variable names and concise notation for formulas,
but short names need descriptions, and fancy operators need pronounceable names.
We propose a dual naming scheme,
with pronounceable alphanumeric default identifiers and descriptions/concise notations
(which may include non-`ASCII` characters and introduce custom symbolic operators) as aliases,
written in backticks afterwards.

```kotlin
val n `element count` = ...              # field/variable descriptions
```
```kotlin
class List<T `element type`>             # parameter/argument descriptions
```
```kotlin
enum class Boolean `|\bbB|`                   # unicode identifiers
```
```kotlin
|\textbf{\textcolor{dgreen}{def}}| not(b : |\bbB|) `¬b`                      # prefix operators
```
```kotlin
|\textbf{\textcolor{dgreen}{def}}| factorial(n : ℕ) `n!`                # postfix operators
```
```kotlin
data class Pair<out X, out Y> `X × Y`    # infix operators
```
```kotlin
|\textbf{\textcolor{dgreen}{def}}| floor(x : Float) `⌊x⌋`               # closed operators with parameters
```
```kotlin
|\textbf{\textcolor{dgreen}{def}}| List<T>.get(idx : ℕ) `this[idx]`     # postfix operators with parameters
```

Note that operators can have parameters,
e.g. the indexed access operator `arr[i]` is a postfix operator with parameter `( [_])` .
In mathematics, many binary operators, such as tensor and semidirect products,
may have optional parameters represented as subscripts or superscripts.
Parsing techniques developed for the Agda programming language allow handling such operators.

To refer to operators directly, we propose the following notation:
```
 ::(-) for ::minus        ::(- ) for ::unaryMinus        ::( --) for ::dec
```
Spaces on the right or left indicate prefix and postfix operators, respectively.

# Operator tightness
By default, operators should have unspecified precedence, so expressions like `-n!`
should be treated as syntax errors due to the ambiguity `(-n)!` vs `-(n!)`.
Expressions `a ∘ b ∘ c` for binary infix operators should also be rejected
due to the ambiguity `(a ∘ b) ∘ c` vs `a ∘ (b ∘ c)`.
However, we propose to support vararg infix operators `` plus(vararg x : Float) `+` : Float ``,
in which case chains `a + ··· + c` are interpreted as `plus(a,..., c)`.

We propose to specify the tightness of operators by annotations extending the `OperatorCategory` interface.
Unlike numbers, operator categories are merely required to form a directed acyclic graph
and do not have to be pairwise comparable, which is a good thing:
non-obvious expressions should not be given arbitrary meanings.
Furthermore, operator categories can specify custom interpretations for chains of operators belonging to that category:
The category `@EqRel` of comparison operators resolves their chains `a < b ≤ c` into conjunctions `(a < b and b ≤ c)`.

Infix operators can have different right and left tightness.
Minus always binds tighter on the right, so that `a - b - c` would resolve to `(a - b) - c`.
It can also be defined to bind tighter than `(+)` on the right,
but not on the left, so `a + b - c + d` would parse as `((a + b) - c) + d`.

Combining all these techniques we can even embrace the infamous Donald Knuth’s path notation
```kotlin
draw a -- b -- c --cycle              # A triangle, (--)-lines are straight
draw a ~~ b ~~ c ~~cycle              # A circle through abc, (~~)-lines are curved
draw a ~~ b ~~ c ~- d -- e --cycle    # (~-) connect smoothly only on the left side

draw a ~~ b ~~[tension: 1.5, 1]~~ c ~~ d
draw a [curl: k]~~ c ~~[curl: k] d
draw a ~~ b [up]~~ c [left]~~ d ~~ e.
draw (0,0) ~~[controls: (26.8,-1.8), (51.4,14.6)]~~
(60,40) ~~[controls: (67.1,61.0), (59.8,84.6)]~~ (30,50)
```
enabling a \METAFONT{}/Ti\emph{k}Z-compatible declarative reactive technical illustration framework for
dynamic figures in interactive textbooks and educational apps.

# Implicit definitions \label{let-blocks}

Implicit definitions enable declarative programming whenever objectives can be described by conditions.
They are ubiquitous in mathematical texts,
so supporting the widest possible class of them is highly desirable for a language used in academia.
We propose the following notation:
```kotlin
|\textbf{\textcolor{dgreen}{let}}| x y : Float               |\textbf{\textcolor{dgreen}{let}}| gcd : Int                 |\textbf{\textcolor{dgreen}{try let}}| x ?t : Float
x + 2y = 5                    n \% gcd = 0                   x = a + b·t
x - y = 4                     m \% gcd = 0                   x = c + d·t
maximizing { gcd }
```

A `let` block contains conditions imposed on the indeterminates declared in its header.
Conditions must uniquely determine the values of the indeterminates except for so-called existential variables
(marked like `?t`), which are scoped within the block and not exposed.
A `let` block can only be compiled if there is an appropriate solver
for conditions of the given form on indeterminates of given types.
Solvers have to ensure the existence of a unique solution^[Take `a = c, b = d = 0` in the rightmost example. Its solution `x = c` qualifies as unique because `t` is existential.],
either at compile-time (`let` blocks) or at run-time (`try let` blocks).
Currently, we envision three specialized solvers:
- the \href{https://r6.ca/blog/20110808T035622Z.html}{*-semiring linear equation solver},
- the \href{https://doi.org/10.1007/978-3-030-55754-6_14}{mixed integer and real linear arithmetic solver},
- an SAT/SMT (boolean satisfiability/satisfiability modulo theories) solver.

Implicit definitions were also introduced into programming by Donald Knuth's \METAFONT.

# Type classes and structure hierarchies

Academic applications require typeclasses we [introduce elsewhere](http://akuklev.github.io/kotlin_typeclasses.pdf).
We propose modeling type class inheritance and nominal subtyping after the
[Arend](http://arend-lang.github.io/assets/lang-paper.pdf) language.
Type class subtyping should soundly represent hierarchies of algebraic structures,
which leads to quite intricate cases, which can be illustrated on the rig (semiring, ring without negation) example:

Diamond problem
: Ri(n)gs extend monoids in two ways: they form a monoid with respect to both addition and multiplication, which can be expressed using call-site field renaming:
```kotlin
|\textbf{\textcolor{dgreen}{data}}| Rig<this R>(…) : Monoid<R>(::times), AbMonoid<R>(::plus)
```

Circularity
: We can define the class of modules over a given rig, and define (unital associative) algebras over a given rig as a monoidal object in modules over that rig. Ultimately, we observe that a rig can be seen as an algebra over `ℕ` (ring as an algebra over `ℤ`, abelian group as a module over `ℤ`, etc), which should be ideally reflected by subtyping. This issue can be addressed by allowing nominal (bi-)convertibility to be established retroactively:

```kotlin
|\textbf{\textcolor{dgreen}{data}}| Module<R : Rig, this M>(…) : AbMonoid<M>(::plus)
```
```kotlin
typealias Algebra<R : Rig, this A> = Monoid<A>(::times) |\textbf{\textcolor{dgreen}{within}}| Module<R>
```
```kotlin
|\textbf{\textcolor{dgreen}{establish}}| Algebra<ℕ> ≡ Rig
Module<ℕ>  ≡ AbMonoid(::plus)
Rig        ≡ Monoid(::times) |\textbf{\textcolor{dgreen}{within}}| Module<ℕ>
```

# Juxtaposition as an operator

Academic Kotlin should follow the mathematical convention of “putting” invisible ($\cdot$)-operators between
consecutive uppercase and mathematical cursive (`U+1D44E`..`U+1D467`) letters:
```kotlin
|\textbf{\textcolor{dgreen}{def}}| avg(|$x,\, y$|) = |$xy$|/2
```

Digits and apostrophes should still be treated as part of the preceding identifier with digits rendered as indices.
Backticks can be used to access multi-letter uppercase identifiers: {\texttt \`}`ABC`{\texttt \`}.

It allows using the customary geometric notation for lines `AB`, triangles `△A`$_1$`B'A`$_2$ and other point-labelled
objects enabling an exceptionally concise and typographically pleasing syntax for
Lean-style tactic-based proofs in geometry.
Consider the following adaptation of `APRiL`^[\url{http://april-lang.org} — `APRiL`: A geometric PRoof Language]:
```kotlin
|\textbf{\textcolor{dgreen}{establish}}| `|\textcolor{blue}{Pythagoras' Theorem}|`                         #   △AB…C nondeg. polygon
|\textbf{\textcolor{dgreen}{given}}| △AOB |\textbf{\textcolor{dgreen}{with}}| |\scriptsize$\measuredangle$|AOB = ¼ turn                           #   |\scriptsize$\measuredangle$|AOB angle,  |\scriptsize$\angle$|AOB wedge
|\textbf{\textcolor{dgreen}{prove}}| |\textbar|AB|\textbar|² = |\textbar|AO|\textbar|² + |\textbar|OB|\textbar|²                             #   |\textbar|AB|\textbar| length, |\textbar|AB…C|\textbar| area
|\textbf{\textcolor{dgreen}{take}}| P |\textbf{\textcolor{dgreen}{on}}| [OA⟩ |\textbf{\textcolor{dgreen}{with}}| |\textbar|OP|\textbar| = |\textbar|AO|\textbar| + |\textbar|OB|\textbar|                #   [AB⟩ ray,    AB line
|\textbf{\textcolor{dgreen}{take}}| R |\textbf{\textcolor{dgreen}{on}}| [OB⟩ |\textbf{\textcolor{dgreen}{with}}| |\textbar|OR|\textbar| = |\textbar|AO|\textbar| + |\textbar|OB|\textbar|                #   |$\FacNext$|OR|$\,$| circle,|$\!\!\!$|  [AB] segment
|\textbf{\textcolor{dgreen}{take}}| Q |\textbf{\textcolor{dgreen}{on}}| |$\FacNext$|OP ∩ |$\FacNext$|OR |\textbf{\textcolor{dgreen}{with}}| Q ≠ O
|\textbf{\textcolor{dgreen}{prove}}| PORQ is |\textcolor{blue}{square}| by                               #   X |\textbf{\textcolor{dgreen}{on}}|/in/|\textbf{\textcolor{dgreen}{inside}}| shape
|\textbar|PO|\textbar| = |\textbar|OR|\textbar| = |\textbar|RQ|\textbar| = |\textbar|QP|\textbar|                           #   X |\textbf{\textcolor{dgreen}{on}}|/|\textbf{\textcolor{dgreen}{inside}}| ray/segment
|\textbar|PR|\textbar| = |\textbar|OQ|\textbar|
...                                                         
```
```kotlin
|\textbf{\textcolor{dgreen}{construct}}| |\textcolor{blue}{midpoint}| M |\textbf{\textcolor{dgreen}{of}}| [AB]                            |\textbf{\textcolor{dgreen}{construct}}| |\textcolor{blue}{centroid}| O |\textbf{\textcolor{dgreen}{of}}| ABC
|\textbf{\textcolor{dgreen}{take}}| P, Q |\textbf{\textcolor{dgreen}{on}}| |$\FacNext$|AB ∩ |$\FacNext$|BA                                 |\textbf{\textcolor{dgreen}{take}}| |\textcolor{blue}{midpoint}| A' |\textbf{\textcolor{dgreen}{of}}| [BC]
|\textbf{\textcolor{dgreen}{take}}| M |\textbf{\textcolor{dgreen}{on}}| [AB] ∩ [PQ]                                   |\textbf{\textcolor{dgreen}{take}}| |\textcolor{blue}{midpoint}| C' |\textbf{\textcolor{dgreen}{of}}| [AB]
|\textbf{\textcolor{dgreen}{take}}| O |\textbf{\textcolor{dgreen}{on}}| [AA'] ∩ [BB']
```