In course of the last two years, I've been developing ideas on possible evolution of Kotlin.

Practical enhancements for Kotlin:
- [Structured lifecycle management](kotlin_objects.pdf) (8 pages): Like many languages, Kotlin uses scope-based resource management. We outline how to manage objects' lifecycle on the type level, ultimately revealing the common structure underlying structured concurrency in Kotlin and lifetime-based borrow checking in Rust. We generalize Kotlin's structured concurrency to type-safe structured actor model.
- [Safe type providers](kotlin_meta.pdf) (2 pages): We propose introducing a safe form of type providers – compile-time functions that synthesize interfaces and type aliases – to greatly improve type-safety of libraries and APIs, enable very sophisticated type-safe domain-specific languages (DSLs) such as embedded SQL.
- [Controlling effects](kotlin_purity.pdf) (1 page): In many cases, high-order functions such as `sortWith(comparator)` only have meaningful behaviour if their arguments are pure functions. Type-level control over the purity of functions and data is essential to prevent nonsensical behaviour and dangerous vulnerabilities.

Semantic and syntactic extensions to reach into areas where Python and Lean currently dominate:
- [Literate Kotlin](kotlin_literate.pdf) (4 pages): Kotlin in its current form is not optimized for literate programming and lags behind Python when it comes to illustrating ideas in tutorials and research papers. We develop an alternative syntactic front-end for these usages.
- [Declarative Kotlin](kotlin_declarative.pdf) (2 pages): We outline a roadmap for seamless integration of declarative programming capabilities embracing the full power of Verse Calculus (roughly “Haskell + Prolog”) and beyond.
- [Academic Kotlin](kotlin_academic.pdf) (4 pages): Literate Kotlin extensions dedicated to applications in computer science and in pure mathematics.
