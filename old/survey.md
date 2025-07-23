Introspectable General-Purpose Programming Languages: Where are we now?
=======================================================================

You may have heard about purely functional programming languages such as Haskell, languages with a reputation for being a very academic and abstruse.  
Agda is an even more abstruse language — it's a dependently typed total functional programming language. Agda and a few similar languages have a remarkable capability of self-introspection: they can be used not only to write programs, but also to reason about every aspect of those programs using the very same language, i.e. formulate any desired properties of programs and write formal proofs that those properties hold. Those proofs will be checked while the programs are being compiled.

Agda used to be less expressive than Haskell: being a _total_ functional programming language, Agda employs a termination checker for recursive algorithms. For many algorithms, convincing the termination checker can be quite non-trivial. Recently Agda incorporated Guarded Computational Type Theory CTT⏲'2018. With this upgrade, it turned out to be possible to verify termination and correctness of notorious Hofmann's algorithm in a few pages worth of proof. This attests feasibility of expressing any Haskell algorithm in Agda. 

Haskell is time-proven industrially used core language.

Mature in principle


A modern general-purpose programming language is a language suitable for an entire software product of arbitrary complexity, including reactive user interface, coroutines/actors, asynchronous I/O, interactions with the external world: OS, file system, databases, queues, sockets, device drivers, remote parties. Think of Kotlin, Rust, or Scala.  
Modern general-purpose programming languages are a mess. None of them has fully specified semantics that would allow reasoning about programs. None of them is even remotely close.
Reliable static code analysis and formal verification are available for small restricted subsets at best.

In sociology, there is a phenomenon known as the Maslow's hierarchy of needs: it makes few sense solving aesthetical demands before securing one's subsistence.
Let's try to formulate our “Maslow's hierarchy”

```
  – General-purpose programming language –
–––––––– Core programming language –––––––––
```

Inside every general purpose programming language there is a core, a programming language suitable only for computaions and data processing.
Getting a general-purpose programming language right presupposes getting a core programming language right first.

* * *


* * *



Heavenly Kotlin



If you're reading this, it is safe to assume, at some point of your life you came across mainstream statically typed programming languages like C++ or Java.
In those languages type signatures are more of a “declaration of intent” kind of thing; it is possible and sometimes unavoidable to “look under the hood”
ignoring types. In the most advanced of mainstream statically typed general-purpose languages (say, Kotlin), explicit type coersions can be avoided, yet
they still have tripple equals operator (compares if two references refer to the same memory location) and similar rudiments allowing to “peep under the hood”,
and these rudiments cannot be avoided at all times. Their type systems are a “leaky abstraction”, making them disproportionately more troublesome than useful
for many purposes. Oftentimes it is reasonable to retreat to dynamically types languages like Clojure or Python, because their rudimentary type system does
not get in the way.

Now what's Type Theory and why bother?
Let's step back to statically typed languages like Java or C++.
Besides inbuilt primitive data types such as `int32`, such languages also support composite data types, such as tagged unions  X + Y and tuples X × Y.
These generalize algebraic operations of addition and multiplication: given two finite types X and Y with n and m inhabitants respectively,
their tagged union X + Y has (n + m) inhabitants, and the type of pairs X × Y has (n · m) inhabitants. For this reason, such composite types are called
polynomial data types. Algebraic datatypes generalize polynomial ones by allowing recursive definitions: `IntList := 𝟙 + Int × IntList`. It turns out,
by starting with finite datatypes and algebraic datatype definitions, one can define lots of potentially infinite data types and data structures, such
as true (as opposed to fixed-width int64) natural numbers, lists, binary trees, etc. These type definitions tell exactly how values of those types can be
analysed and syntesized, they provide full and complete semantics for variables of those types which is independent from low level implementation.
For algebraic data types, typing discipline is not a leaky abstraction. It is never necessary to “peep under the hood” and there is no gap between
“runtime types” and “compile-time types”. With algebraic data types, there is no need for inbuilt array types (arrays can be modelled as lists) or
primitive data types such as `int32` (these can be modelled as lists of bits 𝔹 := {tt, ff}). However, they are not enough: 

There is one more operation



, and
there are exactly mⁿ mathematical functions `f : n → m`.


Type systems of those languages are extensible
(it type systems of C and ALGOL68 are already extensible): 

Those languages support finite types (`enum Direction {Left, Right}`) and record types (`struct User {string name; int age}`). More advanced languages also allow tagged unions `T `


In class-based object-oriented languages 

: statically typed languages with extensible type system Those are statically typed programming language where it is possible to introduce custom data types. 

In all of those languages are defined

macroassembler.

, static type system is a leaky abstraction piggybacked onto operational 



“Under the hood” there is another, rudimentary type system: in case of C it's roughly “everything is an int”, in Java and other JVM-languages its several primitive types like `int`, “array” or “object” that cont

one can forcefully “cast” values and objects from 

Already in C it is possible to define finite types 

struct S {
  char myLetter;       // Member (char variable)
};
Many people, by the way, not only software developers, sometimes have to learn to program. And sometimes they come across such programming languages as C++ or Java - strictly typed, in which you can define your own types. Then these people learn about algebraic data types, and sometimes they start googling and reading something. And they learn that it turns out that there is some powerful mathematical theory behind type systems, and there are some mega-expressive type systems where you can strictly type printf.
Then it turns out that mainstream languages can't do such things, and if they can, the 


And where are normal programming languages based on type theory? There are none yet, though there have been several attempts. And no, because you can't jump over your head, as with Maslow's pyramid - you need water, food and a roof over your head first, and then aesthetic needs. That's the pyramid we have here:



Principled
