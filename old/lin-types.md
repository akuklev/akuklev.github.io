Speculations on Linear Dependent Types: Eventual Consistency, Entanglement, Quantum Fields, and 𝔽₁
==================================================================================================

In the present document I will sketch how to extend the Higher Observational Construction
Calculus HOCC by single-use variables and types for them, outline how in this setting the
univalent equality turns into entanglement and eventual consistency conditions, and
speculate about connections to quantum computations, quantum fields and ”field with one
element’ 𝔽₁.

§ Request Endpoints and Continuations
-------------------------------------


Assume you use a variant of intuitionistic type theory as a functional programming language but
seek to go beyond functions that just calculate. You want to write down routines that interact
with external agents. From now on we will be calling the types available in intuitionistic type
theories value types, because we'll be introducing an additional kind of types: the agent types.
In this setting user interaction will be also modelled as interaction with an agent of specified
type but unknown and unknowable internal workings.

Interactions can be represented by performing requests and calculating with their results. For any
to value types `ReqT : 𝓤` and `RespT : 𝓤` there will be an agent type `ReqT ⊸ RespT` describing
request endpoints. A request endpoint `f : ReqT ⊸ RespT` can be used as you would normally use a
function:
```
#let response = f(request)
```

But there is one caveat: the endpoint `f : ReqT ⊸ RespT` is a single-use variable, it can be used
only once and it must be either “consumed” or returned back to to the caller as a part of the
return “value”.

[Continuations](https://en.wikipedia.org/wiki/Continuation) constitute a form of request endpoint.
A routine anticipating continuation has the following signature:
```
proc(n̲o̲r̲m̲a̲l̲-̲a̲r̲g̲s̲ : X)[T̲](c̲o̲n̲t̲ : R ⊸ T) : T

 equaivalently

proc : Π(n̲o̲r̲m̲a̲l̲-̲a̲r̲g̲s̲ : X) ⋂(T̲) (R ⊸ T) ⊸ T
```

Certainly, response types can be dependent on request types:
```
 ReqT : 𝓤   (r : ReqT) ⊢ RespT(r)
———————————————————————————————————
    (r̲ : ReqT) ⊸ RespT(r) : 𝓛
```

For request endpoints that are not mandatory to use, one can use a special request to close them.
You just wrap `ReqT` into a type with additional request `Terminate`, and wrap the type `RespT`
into a type with additional responce `Terminated` which arizes iff the request was to close the
endpoint:
```
#Inductive OptionalRec[R̲e̲q̲T̲ : *] : *
  Request(r̲ : T)
  Terminate

#Inductive Resp[R̲e̲s̲p̲T̲ : ReqT → *] : OptionalRec[ReqT] → *
  Terminate ↦ Terminated
  Request(r̲) ↦ Response(r̲e̲s̲p̲ : ReqT(r))

now instead of `f : (r̲ : ReqT) ⊸ RespT(r)` you can
use `f : (r̲ : OptionalRec(ReqT)) ⊸ Resp[RespT](r)`
to have a closable request endpoint.
```

An endpoint can return another endpoints. For example, consider
```
random-number-generator : (n̲ : ℕ) ⊸ (𝟙 ⊸ Fin(100))ⁿ
```

Given a natural number `n` it generates `n` independent endpoints, each of them has a trivial
request type (the type `𝟙` with the single inhabitant `() : 𝟙`, and returns a number between 0
and 99 when invoked).

Endpoint factory has the type denoted `!I`. It produces any number of independent endpoints of
identical type. A variable of a type `x : !I` is not single-use any more, it is allowed to be used
any number of times. For value types `A` and `B`, the types `A → B` and `!A ⊸ B` are equivalent.

By returning a single endpoint as part of the responce, endpoints can represent communication
streams. If an endpoint has a type `I` with property `I = (r̲ : ReqT) ⊸ I × RespT(r)`, an endpoint
`s : I` can be used as follows:
```
#let (s₂, response₁) := s(request₁)
#let (s₃, response₂) := s₂(request₂)
...
```

Since each `sₙ` has the same name and the previous one is already consumed, one can actually
suppress induces. Then we could write code like this:
```
#let (console, _)    := console(Print("Please, enter your name: "))
#let (console, name) := console(GetString)
#let (console, _)    := console(Print("Hello, [name]!"))
```

Since there is no way to close the running endpoint, at the end of such a routine you just return
`console` back to the caller.

In general, type of the returned endpoint could also change. Assume we have the type “State”,
the types `ReqT(s̲ : State)` and `RespT(s̲ : State)(r̲ : Req(s))` now depend on the state of
the endpoint, and we have the function `next-state(s̲ : State, r̲ : ReqT(s)) : State`. Now we
can define the type `I(s̲ : State)` with the property
```
I(s) = (r̲ : ReqT(s)) ⊸ I(next-state(s, r)) × RespT(s)(r)
```

Such types are called session types. One also allow an endpoint to return multiple fresh endpoints
or no endpoint at all closing the communication. With this generalization we obtain the linear
counterpart of coinductive types. As coinductive types can be generalized to Equaliser Coinductive
Types (the dual of Quotient Inductive Types) by equational conditions, session types can be
generalized by conditions in terms of string diagrams (the linear counterpart of equations).
These string diagrams specify required indepencence structure of returned endpoints, and as well
as the eventual consistency structure. In other words, these are the rules specifying allowed out
of order execution of requests.

§ Double Sided Sequents: Pool of Processes
------------------------------------------

Judgements in intuitionistic type theories are one-sided sequents: there are several types on the
left side (they represent the context), and a single type on the right side: the type of the
expression being constructed:
```
x : X,..., z : Z ⊢ expr : T
```

Concurrent interactive systems can be described by double-sided sequents, that is sequents with
multiple expressions on the right side, which represent a pool of processes running in parallel:

```
x : X,..., z : Z ⊢ proc₁ : A,..., procₙ : C
```

The context on the left side can be dependent: type annotations to the right of `x : X` can use
`x` as a varable, and so on. Can the right side be dependent too?

Let us assume, you have a routine that requiers a request endpoint `e : 𝟙 ⊸ ℕ`. It can be viewed
as a closes routine that opens a single-use channel of dual type `ℕ ⊸ 𝟙` and waits for some
other process to use this channel. We propose to call it co-lambda abstraction:
```
  Γ, e : 𝟙 ⊸ ℕ ⊢ a(e) : A, Δ
———————————————————————————————
 Γ ⊢ (ē : 𝟙 ⊸ ℕ; a(e) ) : A, Δ
```

Now the cocontext Δ can (and, actually _must_) use variable `e` defined in the first expression of
the cocontext. Actually, the rule of inference as stated is incomplete. That's the complete version:
```
 Γ, e : 𝟙 ⊸ ℕ ⊢ a(e) : A, Δ     Γ', e : ℕ ⊸ 𝟙 ⊢ b(e) : B, Δ'
—————————————————————————————————————————————————————————————
       Γ, Γ' ⊢ (ē : 𝟙 ⊸ ℕ; a(e) ) : A, b(e) : B, Δ, Δ'
```

Of course it works not only for the type `𝟙 ⊸ ℕ` but for all dualizable agent types including
all session types. With co-lambda abstractions it is possible to implement coroutines.

§ Operations on Agent Types
---------------------------

For two values types `T Q : 𝓤` one can build their cartesian product `T × Q` containing pairs
`(t, q)` of values `t : T` and `q : Q`. We can also build dependent pair types `Σ(t̲ : T) Q(t)`.

This trivially generalizes to the case when `Q : 𝓛` is an agent type. It allows to define
disjunctive sum of two agent types `Q ⊕ P := Σ(t̲ : 𝔹) (ff ↦ Q, tt ↦ P)`. That is, an actor of
type `Q ⊕ P` is either of type `Q` or of type `P`.

Now what about cartesian product of two agent types? There, we have to options:
* Conjunctive product, i.e. simultaneous occurrence of agents `(q, p) : Q ⊗ P`. In this case the
consumer can and must consume (or return) both `q` and `p`;
* Disjunctive product, i.e. alternative occurrence of agents `w : Q & P`. In this case the consumer
choses which one to take. It either consumes `w` by `w(ff) : Q` or by `w(tt) : P`, but not both,
because `w` cannot be used twice.

This two binary connectives can be as well generalized to quantifiers where bounded variable is of
a value type.
* `∀(t̲ : T) Q(t)` denotes a family of agents (each one has to be consumed exactly once);
* `Π(t̲ : T) Q(t)` denotes a “factory that” yields one agent of the type `Q(t)` when given a `t`.

The operators `⊕`, `⊗`, `&` and `⊸` precisely reproduce the rules of Intuitionistic Linear Logic.
See “Linear Logic Propositions as Session Types” by L. Caires, F. Pfenning, and B. Toninho to see
to complete calculus including constructors how to define particular processes and interactions.
There you will find a calculus where one can spawn new processes/actors, pass messages and
continuations, etc.

Yet, there is some assymetry: we have only three quantifiers instead of four. There is one more
binary connective in the linear logic: the conjunctive sum `⅋`, which is interdefinable with `⊸`
for dualizable agent types: (`X ⊸ Y = X⟂ ⅋ Y`, `X⟂ ⅋ Y = X⟂ ⊸ Y = Y⟂ ⊸ X`).

`P ⅋ Q` stands for “a process eventually yielding a `P` and a process eventually yielding a `Q`
running in parallel”. By virtue of being commutative and associative this binary connective can
be also generalized to a quantifier `⅋(t̲ : T) Q(t)`, where `T` is a value type.

An agent of the type `w : ⅋(t̲ : T) Q(t)` in general requires the program to process all branches
(as many as there are values `t` in `T`) with each branch consuming exactly one agent `wₜ : Q(q)`.
`⅋(t̲ : T) Q(t)` represents a “pool” where agents are running simultaneously, concurrently and
interacting with each other. If one of the agents has type `Y = A ⊸ B`, it means that it currently
awaits a value of the type `A` and not running, which can lead to another agent `X` in the “pool”
stuck. The handler of `X ⅋ Y` knows how to process both actors independently, so it will feed a
value of the type `A` into the actor `Y`, so that `X` can go on, and eventually its result will be
also processed by the handler of `X ⅋ Y`.

In type theory there is still one typeformer we have not mentioned so far: the equality. As with
all other typeformers, this one will split into two duals: independence and eventual consistency.

Independence of agents `x : X` and `y : Y` is precisely what allows one to perform a multi-way
join, that is handle `(x ∥ y) : X ⅋ Y` by awaiting only `x`, only `y`, both, or “whatever comes
first”. In the last case you have to show that no race condition can occur or that it does not
affect the result, which is the eventual consistency.

NB: Eventual consistency can play a role even in the intuitionistic setting when working with
Turing-complete partial functions. Sometimes one can define two two partial functions on the
Cauchy real numbers `f g : ℝ -> Partial(T)` with `f` being guaranteed to eventually yield a
result for `x >= 0` and `g` being guaranteed to yield a result for `x <= 0`. If they can be
shown to agree in the case both yield a result, one can join them into a single function.

§ Agents and Objects
--------------------

Agents may be nondetermenistic and communicate with each other. For example, a particular request
to one remote database yield different results if we previously requested another remote database,
because they could have communicated behind the scenes. Agents that are independent from any other
agents (that is, self-enclosed) are called objects. The property of being independent can be
formulated within type theory. For objects, the concept of ownership makes sense, so that the
“pool” of agents running in parallel can be seen as a directed acyclic graph.

While all agents that can be constructed are certainly deterministic, in general both agents
(think of the agent representing the user of an interactive application) and objects (think of
the random number generator) are not required to. While objects are guaranteed not to communicate
with each other, they still can be subject to eventual consistency conditions. Some algebraically
admissible eventual consistency conditions cannot be ever achieved by deterministic (and thus
computationally constructible) objects, but such objects are not impossible. They can be realized
as nondetermenistic objects being in a state of quantum entanglement. Entangled objects can satisfy
eventual consistency conditions without communicating.


§ Element Classifier 𝔽₁ and Superposition Quantifier ⅋
------------------------------------------------------

Subsets of a type `T` are classified by functions `p : T → Ω`, where `Ω` is the type of all
propositions, also known as subobject classifier. In our generalized setting we can have the
object type that classifies single elements of other types.

We want to define the object type 𝔽₁ with the property that in can be only inhabited by two
objects `0₁ : 𝔽₁` and `1₁ : 𝔽₁`, but no two `1₁` objects can ever exist at the same time, while
at least one is guaranteed to exist. For an object with such properties the maps `f : T ⊸ 𝔽₁`
will exactly correspond to elements of `T`. As `Ω` naturally has a structure of Heyting algebra,
`𝔽₁` will naturally have a structure similar to a field, albeit with one element, see
[https://en.wikipedia.org/wiki/Field_with_one_element].

That means, for a function `v : T ⊸ 𝔽₁` and a family `f : T → X` there will be a pairing
`v ⇃ f : X`, and for each element `t : T` there will be a function `ξ(t) : T ⊸ 𝔽₁`, such
that `ξ(t) ⇃ f = f(t)`.

Imagine that `𝔽₁` can act on processes by either terminating them (case of 0) or letting them run
(case of 1). That is, for each `q : 𝔽₁` and `p : P` we have `qp : qP` where the action of `q` on
types is given by `(0₁)P = 𝟙`, and otherwise `qP = P`.

Now if we have a process factory `f : Π(t̲ : T) Q(t)` and a function `v : T ⊸ 𝔽₁`, we pair them
to obtain `p := ⸮(t̲ : T ↦ (v t)(f t)) : ⅋(t̲ : T) (v t)Q(t)`.

We can define the following operations on the type `𝔽₁`:
```
0₁ : ?𝔽₁
(+) : 𝔽₁ ⅋ 𝔽₁ ⊸ 𝔽₁
(·) : 𝔽₁ ⊗ 𝔽₁ ⊸ 𝔽₁
```

One can show these operations to fulfill axioms of a commutative semiring.

Note that since will be is no rule allowing to introduce `1₁ : 𝔽₁`, so it is impossible to form
`2 := 1 + 1`. The only definable polynomials are sums of distinct variables: To form `2a` one would
need to be able to write `a + a`, yet `a` is a single use variable and cannot be used twice. For
the same reason it is impossible to form `a² := a · a`. The element classifier `𝔽₁` is a field in
the sense that every linear equation has a solution. Indeed, it is even an algebraically closed
field in the sence that every non-constant polynomial has a solution.

In HOCC, non-dependent elimination motives of quotient inductive types precisely correspond to
single-sorted algebraic theories, with quotient inductive type itself representing the initial
“syntactic” model of the theory. $S$-sorted algebraic theories can be described by quotient
inductive type families indexed over $S$. Recently we proposed type theories by Reedy-inductive
types. By making $S$ a Reedy-inductive type we can accomodate algebraic theories with dependent
and possibly infinitary dependent signatures.

We conjecture that the linear counterpart of inductive types would correspond to
[Partial Algebraic Theories](https://arxiv.org/pdf/2011.06644.pdf), that it is possible to develop
their semantics over an arbitrary generalized field, and specializing to 𝔽₁ would recover the
usual algebraic theories (Hopf algebra over 𝔽₁ is a group, etc.).



§ Quantum Quantifiers
---------------------

The type `⅋(t̲ : T) Q(t)` represents a superposition of simultaneous processes? Can we use it to
represent superpositions of quantum states? If we somehow could, there will be a map `|f>` turning
functions `f : T → ℂ` into states `|f> : ⅋(_ : T) 𝔽₁`, and those states can be used to ‘probe’
objects of `ψ : ⅋(_ : T) 𝔽₁`. By probing, we force `ψ` into a new state (either `|f>` or `|-f>`)
and get a bit value, if it was plus or minus `f`:
```
         ψ : ⅋(_ : T) 𝔽₁    f : T → ℂ
—————————————————————————————————————————————————
 ψ.measure(f) : Σ(t̲ : 𝔹) (ff ↦ {ψ | ψ = |f>},
                          tt ↦ {ψ | ψ = |-f>})
```

If `ψ` was already equal to `|f>`, we'll always land in tht `tt` branch:
```
 ψ : ⅋(t̲ : T) Q(t)     p : ψ = |f>
———————————————————————————————————
    ψ.measure(f) = (tt, |f>)
```

We have to take into account that quantum objects have non-trivial automorphisms, at least the
“invisible” complex phase.

An object `q : ℭ` is said to be a linear U(1)-torsor, if it's automorphisms space `(q)! = U(1)` and
it can be acted on by elements of `U(1) = {c̲ : ℂ | |c| = 1 }` associatively:
```
 q : ℭ    c : U(1)
———————————————————
     cq : ℭ

 q : ℭ    b c : U(1)
—————————————————————
   b(cq) = (bc)q
```

Quantum objects belonging to the same system are equivariant with respect to simultaneous phase
rotations. It means that all quantum objects `a, b,.., c` belonging to the system share the _same_
object of automorphisms: `a! = b! = ··· = c!`, and it has the type `a! : ℭ`.

Quantum objects are precisely the objects with automorphism type being a linear type as well.
We'll be denoting the types of objects with automorphism object `c` by `ᶜI`.

Only for objects sharing the same object of automorphisms we can define disjunctive sums and
conjunctive products:
```
 c : ℭ    A B : 𝓛ᶜ
————————————————————
      A ⊕ᶜ B

 c : ℭ    A B : 𝓛ᶜ
————————————————————
     A ⊗ᶜ B
```

We also have equivariant quantifiers:
```
 T : 𝒰    c : ℭ    t : T ⊢  ᶜQ(t) : 𝓛
———————————————————————————————————————
         Σᶜ(t̲ : T) ᶜQ(t)

 T : 𝒰    c : ℭ    t : T ⊢  ᶜQ(t) : 𝓛
———————————————————————————————————————
         ∀ᶜ(t̲ : T) ᶜQ(t)
```

Let `ᶜ𝔹` denote the type of qbits. Then `∀ᶜ(_ : Fin(n)) ᶜ𝔹` describes a a quantum register
of $n$ qubits. For cohesive spaces `∀ᶜ`-quantifiers describe quantum fields over a given space.

Now the automorphism objects are not limited to ℭ. For spin-½ particles it should already a torsor
`ℭ²` of `SU(2)`, but in general it can be at least any complex Lie group. In case of gauge quantum
field theories, the automorphism object it in its turn a quantum field of gauge bosons.

The type of qubits can be defined by `𝔹ᶜ := ⅋ᶜ(_ : 𝔹) 𝔽₁`, where 𝔽₁ is the mystical field with
one element. If `c : ℭ²`, `𝔼ᶜ := ⅋ᶜ(_ : ℝ³) 𝔽₁` is the state space of a spin-½ particle on a 3d
space. It might turn out to be possible to define states of particles (and ultimately also fields)
on noncommutative spacetimes, which would allow to use a linear type as the bound in `⅋` (and,
dually, also`Π`) quantifiers, greatly improveing our understanding of the quantum field theory.
The analogy between 𝔽₁ classifying elements of a value type `T ⊸ 𝔽₁` and ℂ classifying states
of a *-algebra `𝒜 ⊸ ℂ` might shed some light on the possiblity of linearly dependent linear
types.

See. http://boole.stanford.edu/pub/ql.pdf, https://www.cl.cam.ac.uk/~mpf23/papers/Types/diff.pdf,
https://ncatlab.org/nlab/files/BPSLinear.pdf, https://math.ucr.edu/home/baez/bsz_new.pdf

<!--
§ Pool of Actors: Coroutines and Continuations
----------------------------------------------

In the usual HOTT, our judgements have asymmetric form:
```
x : X,..., y : Y ⊢ expr : T
```

We have bag of variables called context on the left and a single expression on the right.
In the concurrent setting, our “programm“ is not a single expression, but a pool of interacting
actors, each one if its type:

```
x : X,..., z : Z ⊢ actor₁ : A,..., actorₙ : Q
```

We'll have a rule to “garbage collect” the actors that have done their job and returned the
value of type `𝟙` (that contains no information). Others, who returned a value, remain there.

In this formalism, there is an alternative to lambda abstraction for linear terms. On one, we
have the rule
```
 I : 𝓛    Γ, c : I ⊢ expr : J (expr uses c exactly once), Δ
-------------------------------------------------------------
            Γ ⊢ (\c : I ↦ expr) : (I ⊸ J), Δ
```

But we have an alternative abstraction:
```
 I : 𝓛    Γ, c : I ⊢ expr : J (expr uses c exactly once), Δ
-------------------------------------------------------------
        Γ ⊢ expr : J, (/c : I) : I ⊸ 𝟙, Δ
```

Now on the right side we have a pool of actors:
The first one, `expr`, is stuck: it awaits the “promise” called `c` of the type `I` to be
satisfied. Another actor, `(/c)` expects a value of the type `I`. Once it is applied to
such a value, it would fulfill the promise named `c` by this value, finish and be
“garbage collected” from the pool of actors.

§§ CPS Reversal
----------------

Assume we have a routine anticipating a continuation:
```
proc[\T](c̲o̲n̲t̲ : R ⊸ T) : T
```

How can the caller extract the result which is not returned, but pushed into the continuation?
That's easy. We just pass `(/c : I)` as a continuation, and use the variable `c` elsewhere.
When `proc` invokes the continuation, it would just fulfill the promise `c` unstucking the
computation involving `c`.

§§ Spawning new Processes
-------------------------

To spawn a process you have to provide a process handle it will go by. Of course, you can spawn
processes recursively, or spawn a whole family of processes at once, but unless you spawn a
process factory, you have to put handles somewhere because they are single-use variables.

Let's translate
```
!print "Hello world"
spawn some-long-computation(args, callback: \result ↦ {
  !print result
})
do-something-else
```

Result:
```
#let (console, _) := console(Print("Hello world")
#let (console, subconsole) := console(CreateSubprocessConsole)
(/deferred-calculation)(
  some-long-computation(args,
    \result ↦
    #let (subconsole, _) subconsole(Print(result))
    subconsole(Close)
  )
)
do-something-else
```

§§ Algebraic effects
--------------------

Invoking single-use algebraic effects can be seen as calls to the handlers being actors in
the pool. Consider the following routine
```
store(2)
...
#let n := get-from-store
```


To make it work, it is sufficient to have the following in the pool:
```
(/store)(\n ↦ (/get-from-store)(n))
```

§§ Coroutines: The ! and ? Modalities
-------------------------------------

-->
