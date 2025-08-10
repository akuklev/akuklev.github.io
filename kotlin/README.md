Structured programming pioneered by ALGOL and
structured concurrency used in Kotlin
illustrate one of the pillars of great programming language design:
endorse correct-by-construction software design, foster clarity and predictability, aid reasoning.

The first two proposals can be seen as an introduction of far-reaching contracts 
that both foster correctness by construction and set the stage for statically
verifiable contracts
(see also [Usability Barriers for Liquid Types by J. Aldrich et al.](https://dl.acm.org/doi/10.1145/3729327)):
- [Purity, constants, and explicit effects](kotlin_purity.pdf) (1 page):
  In many cases, high-order functions such as `sortWith(comparator)`
  only have meaningful behaviour if their arguments are pure functions.
  Type-level control over the purity of functions
  and data is essential to prevent nonsensical behaviour and dangerous vulnerabilities.
- [Resources, lifecycles, and structured concurrency](kotlin_objects.pdf) (8 pages):
  Kotlin relies on scope-based resource management
  but lacks mechanisms to prevent leaking,
  guarantee lifecycle safety, and rule out conflicting actions statically.
  We devise a mechanism addressing these issues in a manner compatible with and inspired by structured concurrency.
  Our approach subsumes Rust's borrowing and is closely related to Capture Checking in Scala and OxCaml,
  but lays more focus on shifting the burden from library users to library developers.

Advanced declarative features and type-safe domain-specific languages further expand
correct-by-construction design:
- [Startup and dependency injection](kotlin_startup.pdf) (1 page):
  Application startup often requires initialization of external
  services and components possibly configurable via command-line arguments.
  We propose a number of minor language extensions to achieve this with zero boilerplate. 
- [On type providers for Kotlin](kotlin_meta.pdf) (2 pages):
  We propose introducing a safe form of type providers – compile-time functions
  that synthesize interfaces and type aliases – to greatly improve type-safety of libraries and APIs, enable very 
  sophisticated type-safe domain-specific languages (DSLs) such as embedded SQL.
- [First-class query functions for Kotlin](kotlin_verse.pdf) (1 page):
  We propose introducing query functions inspired by the recently developed Verse calculus, a
  novel approach to deterministic functional logic programming combining the powers of Haskell
  and Prolog. In a limited form which is much easier to implement, query functions can extend
  SQL-like reactive query languages (see Exposed: Kotlin SQL Framework) by recursive queries
  that leverage the power of Datalog while remaining easy to read, understand, and maintain.

Type-driven programming facilitates correct-by-construction design in some of the most complex areas:
- [Typeclasses for Kotlin](kotlin_typeclasses.pdf) (2 pages): Ideas on introducing typeclasses in Kotlin way.
- [Indexed types](kotlin_families.pdf):
  Indexed types enable correct-by-construction design of parsers and interpreters, as well as type-driven design of 
  complex transformation (e.g. compilation) and analysis
  (e.g. typechecking and control-flow analysis) algorithms in general.
  
Lastly, we propose semantic and syntactic extensions to reach into areas where Python and Lean currently dominate:
- [Literate Kotlin](kotlin_literate.pdf) (4 pages):
  Literate programming is the ultimate approach for building reliable and maintainable applications and libraries.
  Kotlin in its current form is not optimized for literate programming and lags
  behind Python when it comes to illustrating ideas in tutorials and research papers.
  We develop an alternative syntactic front-end for these usages.
- [Academic Kotlin](kotlin_academic.pdf) (3 pages):
  Literate Kotlin extensions dedicated to applications in computer science and in pure mathematics.
