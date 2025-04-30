In course of the last two years, I've been exploring evolution avenues for Kotlin.

These ones enhance the type system, improving static safety and making the language throughout amenable to formal reasoning using both theorem provers and model checking based automated and semi-automated verification:
- [Resources, lifecycles, and structured concurrency](kotlin_objects.pdf) (8 pages): Kotlin relies on scope-based resource management, but lacks mechanisms to enforce scope confinement, guarantee lifecycle safety, and rule out conflicting actions statically. We devise a mechanism addressing these issues in a manner compatible with structured concurrency and localized capturing in general. Our model can be seen as a generalization of Rust approach.
- [Purity and effects](kotlin_purity.pdf) (1 page): In many cases, high-order functions such as `sortWith(comparator)` only have meaningful behaviour if their arguments are pure functions. Type-level control over the purity of functions and data is essential to prevent nonsensical behaviour and dangerous vulnerabilities.
- When liquid types become mature, we'll propose introducing them on top of the above extnesions for semi-automated verification.

These ones help reducing boilerplate and increasing expressivity:
- [Startup and dependency injection]() (?? pages): ...
- [Safe type providers](kotlin_meta.pdf) (2 pages): We propose introducing a safe form of type providers – compile-time functions that synthesize interfaces and type aliases – to greatly improve type-safety of libraries and APIs, enable very sophisticated type-safe domain-specific languages (DSLs) such as embedded SQL.
- [Declarative Kotlin](kotlin_declarative.pdf) (2 pages): We outline a roadmap for seamless integration of declarative programming capabilities embracing the full power of Verse Calculus (roughly “Haskell + Prolog”) and beyond.
- [Distributed Kotlin]() (?? pages): An implementation of typesafe actor model with join-calculus-based complex event processing.


Lastly, we propose semantic and syntactic extensions to reach into areas where Python and Lean currently dominate:
- [Literate Kotlin](kotlin_literate.pdf) (4 pages): Kotlin in its current form is not optimized for literate programming and lags behind Python when it comes to illustrating ideas in tutorials and research papers. We develop an alternative syntactic front-end for these usages.
- [Academic Kotlin](kotlin_academic.pdf) (4 pages): Literate Kotlin extensions dedicated to applications in computer science and in pure mathematics.
