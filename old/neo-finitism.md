Hilbert's Program Formalized
============================

In 1920s David Hilbert proposed a vision that every formal system to be used im mathematics should be proven consistent within a trusted finitistic core system. However, quite soon Kurt Gödel has proven that impossible: non-finitistic systems require strictly stronger systems to prove their consistency.
Original Hilbert's program failed, but originated a multitude of developments that were crucial to overcome the foundational crisis of mathematics. Yet precisely these results have feet of clay. Those metamathematical proofs of relative consistency, equiconsistency, (bi-)interpretability, and conservativity are very convoluted and tedious. Hardly many of them have been ever checked in detail by anyone but the authors, the syntax arithmetization part being nearly unauditable at all.

Contemporary proof assistents are in many aspects not mature enough to be convinient for many areas of mathematics, but they are uniquely suited for end-to-end formalization of metamathematical results related to Hilbert's program. It's precisely the type theory-based proof assistents where we are not forced to provide an arithmetisation of syntax, but can instead work with a direct representation of syntax, naturaly described in terms of finitary inductive data types<sup>[[K2024]()]</sup>. Recently results<sup>[[BuBr2024](https://arxiv.org/abs/2404.01011)]</sup> show how to restrict type theories to primitive-recursive functions between finitary types. Such functions are straightforward enough not to raise doubts about algorithmic correctness, yet powerful enough to describe the syntax transformations of interest in the vast majority of cases relevant to the Hilbert's program. It seems, we only need to develop a proof assistant based on a type theory with enough finitary inductive data types and primitive recursive functions between them, and launch a collaborative formalization effort.

But even despite all of this, such a project would hardly have any chances of taking up, if there were not more to this topic, than formalizing old stuff. Spectacular recent developments seem to pave a way for a new, vastly more structured and comprehensive approach.

# Trusted finitistic core does indeed exist!

After almost a century, a worthy candidate for the role of a trusted finitistic core system was found after all: the finitistic theory of hereditary sets H<sub><ω</sub> developed by Fedor Pakhomov in 2019. This theory has a remarkable property: it acknowledges its own consistency. At the moment it's the only known example of a natural self-justifying theory. H<sub><ω</sub> evades the curse of Gödel theorem by being “finitistic”, i.e. locally finitely satisfiable theory: its finite subtheories have finite models, so it cannot prove existence of any infinite set or unbounded operation. Furthermore H<sub><ω</sub> can interpret any other locally finitely satisfiable theory, so it's a universal locally finitely satisfiable theory.

Of course, it is still not capable of proving consistency of any stronger systems, but it can be used as a base for a hierarchy of extensions H(ɑ) of increasing strength (= modelling capacity) for building set-theoretic models of stronger systems and thus establishing their relative consistency. Such a hierarchy would also allow to precisely gauge modelling capacity of formal systems. Precise gauging requires considering constructive and even computational models for formal systems that admit constructive and/or computational models, demanding for a slightly refined variant of H<sub><ω</sub>.

H<sub><ω</sub> = base theory H₀ (extensionality, separation, and weak hierarchy) + a countably infinite family of axioms ∃0, ∃1, ∃2,... extablishing existence of each finite ordinal. We conjecture there is a constructive set theory CZF₀, such that theories CZF(ɑ) = {CZF₀ + ∃β for each recursive ordinal β < ɑ} has following properties:
- CZF(ω) proves its own consistency
- CZF(ω) proves the same facts about hereditarily finite sets as H<sub><ω</sub>
- CZF(ɑ) does not prove wellfoundness of ɑ, i.e. the proof-theoretic ordinal |CZF(ɑ)| = ɑ
- CZF(ɑ) have direct computational interpretations up to the second order arithmetic, i.e. if ɑ ≤ |PA₂|  
- CZF(|CZF|) = CZF, the standard constructive set theory
- CZF(ɑ) has models of all CZF(β) with β < ɑ, and thus proves their consistency
- For limit ordinals ɑ, CZF(ɑ) satisfies the reflection principle: any finite number of derivable formulas are already satisfied in some inner model
- Large cardinal extensions of CZF and the standard set theory ZFC with its large cardinal extensions fall into the CZF(ɑ)-hierarchy

We also conjecture that it is possible to establish a quantifier-free logic-free presentation for its conservative extension CZF<sup>ω</sup>(ɑ), very similar to the logic-free presentation of primitive-recursive arithmetic PRA developed by Goodstein.
