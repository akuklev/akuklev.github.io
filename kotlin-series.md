In course of the last two years, I've been developing ambitious ideas on Kotlin evolution.

Practical enhancements for Kotlin:
- [Staged Objects and Actors](kotlin_objects.pdf) (8 pages): Kotlin uses scope-based resource management, but lacks mechanisms to ensure that disposable resources are properly finalized and never accessed thereafter. We propose introducing staged objects to control lifecycle and accessibility at the type level, revealing the common structure behind Rust borrow checking and Kotlin structured concurrency, and featuring a generalization of lifetimes to handle staged resources and a generalization of coroutine scopes to handle staged actors. We also propose dedicated notations for dependency injection and resource acquisition.
- [Safe type providers](kotlin_meta.pdf) (2 pages): We propose introducing a safe form of type providers – compile-time functions that synthesize interfaces and type aliases – to greatly improve type-safety of libraries and APIs, enable very sophisticated type-safe domain-specific languages (DSLs) such as embedded SQL.
- [Controlling effects](kotlin_purity.pdf) (1 page): In many cases, high-order functions such as `sortWith(comparator)` only have meaningful behaviour if their arguments are pure functions. Type-level control over the purity of functions and data is essential to prevent nonsensical behaviour and dangerous vulnerabilities.

Semantic and syntactic extensions to reach into areas where Python and Lean currently dominate:
- [Literate Kotlin](kotlin_literate.pdf) (4 pages): Kotlin in its current form is not optimized for literate programming and lags behind Python when it comes to illustrating ideas in tutorials and research papers. We develop an alternative syntactic front-end for these usages.
- [Declarative Kotlin](kotlin_declarative.pdf) (2 pages): We outline a roadmap for seamless integration of declarative programming capabilities embracing the full power of Verse Calculus (roughly “Haskell + Prolog”) and beyond.
- [Academic Kotlin](kotlin_academic.pdf) (4 pages): Literate Kotlin extensions dedicated to applications in computer science and in pure mathematics.
