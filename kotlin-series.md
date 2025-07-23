Structured programming pioneered by ALGOL and
structured concurrency used in Kotlin
illustrate one of the pillars of great programming language design:
endorse correct-by-construction software design, foster clarity and predictability, aid reasoning.

The first two proposals can be seen as an introduction of far-reaching contracts 
that both foster correctness by construction and set the stage for statically
verifiable contracts (see also [Usability Barriers for Liquid Types](https://dl.acm.org/doi/10.1145/3729327)):
- [Purity and explicit effects](kotlin_purity.pdf) (1 page):
  In many cases, high-order functions such as `sortWith(comparator)`
  only have meaningful behaviour if their arguments are pure functions.
  Type-level control over the purity of functions
  and data is essential to prevent nonsensical behaviour and dangerous vulnerabilities.
- [Resources, lifecycles, and structured concurrency](kotlin_objects.pdf) (7 pages):
  Kotlin relies on scope-based resource management 
  but lacks mechanisms to enforce scope confinement, guarantee lifecycle safety, and rule out conflicting actions
  statically.
  We devise a mechanism addressing these issues in a manner compatible with and inspired by structured concurrency.
  Our model can be seen as a generalization of Rust approach.
  It is also closely related to both Capture Checking in Scala and OxCaml,
  but lays more focus on shifting the complexity burden from library users to library developers as far as possible.

Advanced declarative features and type-safe domain-specific languages further expand the applicability of
correct-by-construction software design.
- [Safe type providers](kotlin_meta.pdf) (2 pages):
  We propose introducing a safe form of type providers – compile-time functions
  that synthesize interfaces and type aliases – to greatly improve type-safety of libraries and APIs, enable very 
  sophisticated type-safe domain-specific languages (DSLs) such as embedded SQL.
- [Startup and dependency injection](kotlin_startup.pdf) (1 page):
  Application startup often requires initialization of external
  services and components possibly configurable via command-line arguments.
  We propose a number of minor language extensions to achieve this with zero boilerplate.
- [Declarative Kotlin](kotlin_declarative.pdf) (2 pages):
  We outline a roadmap for seamless integration of declarative programming
  capabilities embracing the full power of Verse Calculus (roughly “Haskell + Prolog”) and beyond.
- [Distributed Kotlin](kotlin_actors.pdf): An typesafe actor model with declarative complex event processing.
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