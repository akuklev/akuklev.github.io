Modal Approach to Polymorphism and Paramatricity
================================================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com), [JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)

Our starting point will be the a type theory with a countable hierarchy of universes introduced by the following infinite family of rules:
```
––––––––————     ––––––––——————     ––––––––—————————     ···
 Γ ⊢ U : U⁺       Γ ⊢ U⁺ : U⁺⁺       Γ ⊢ U⁺⁺ : U⁺⁺⁺
```

These rules introduce a countably infinite family of well-typed terms `U`, `U⁺`, `U⁺⁺`, etc., and have to be considered together as the type used in each rule is first introduced in the next one.

Let us postulate the first universe U to be Σ- and Π-closed and add some basic types to taste:
```
 Γ ⊢ X : U     Γ, x : X ⊢ Y(x) : U       Γ ⊢ X : U     Γ, x : X ⊢ Y(x) : U
––––––––————–––––––––––—————————————    ––––––––——––––––––––––—————————————— 
      Γ ⊢ (x : Y) × Y(x) : U                  Γ ⊢ ∀(x : Y) Y(x) : U

––––––––————    ––––––––————    ––––––––————    ––––––––————
 Γ ⊢ 𝟘 : U       Γ ⊢ 𝟙 : U       Γ ⊢ 𝔹 : U       Γ ⊢ ℕ : U
```

Our goal is to state variadic cummulativity. That is, we want to state that every type belonging to some universe `U` also belongs to `U⁺`, and every type former `F(K : U⁺) : U` can be also lifted one universe above. The second rule leads to inconsistency unless we only state it for closed-form type formers, i.e. the ones definable in empty context. Naïvely, we can try to introduce the S4 neccesity □-modality mapping types `T` to their sets of closed-form inhabitants `t : □T` by the following two rules:
```
 • ⊢ x : X                Г ⊢ x : □X      
————————————(□Intro)     ————————————(□Elim)
 Г ⊢ x : □X               Г ⊢ x : X
```

Here we say that an inhabitant definable in an empty context is a closed-form inhabitant (□Intro), and that a closed-form inhabitant of `X` is an inhabitant of `X` (□Elim).

In the first rule we can allow a context containing only closed-form inhabitants:
```
 □Г ⊢ x : X
—————–––––———————(□Intro)
 □Г, Δ ⊢ x : □X
```     

Now we can clearly see that it is indeed the S4 neccesity modality. But in this form it does not work well with dependent types. To proceed we need to make our type theory {0, ω}-graded, that is we'll allow to mark some variales in contexts as computationally irrelevant using zero subscript above the colon. It will allow introducing parametric quantifiers `∀<x : X> T(x)` (note angle brackets instead of parens):
```
 Γ ⊢ X : U     Γ, x : X ⊢ Y(x) : U
––––––––————–––––––––––—————————————
   Γ ⊢ ∀<x : Y> Y(x) : U

 Γ ⊢ X : U   Г, x :° X ⊢ y : Y(X)
–––––––––––––––––––––––––—————————————
 Г ⊢ { x :° X ↦ Y(X) }: ∀<x : Y> Y(x) 
```

But more importantly, it allows to adjust the rules for the □-modality to work well with dependent types. In the introduction rule we allow irrelevant variables, while in the elimination rule we state that a closed-form element can only depend on non-closed elements of the context irrelevantly:
```
   □Г, Δ° ⊢ x : X                  Г ⊢ x : □X(t)
–––––––––––––––———–——(□Intro)     ——————————————–—(□Elim)
 □Г, Δ°, Σ ⊢ x : □X                Г° ⊢ x : X(t)

(We use the notation □Γ and Γ° to apply □/° to each element of Γ.)
```

Now let us define the universe-shifting operator ( ⁺) for all types. Its action on the types will be defined on case-by-case basis for all type formers (i.e. coinductively). It shifts the universe levels in types built using universes, e.g. `(U → U)⁺` should be `(U⁺ → U⁺)`, while doing nothing for types inside the base universe as they cannot involve universes in their definitions:
```
 Γ ⊢ T : U
––––––––—–——
  T⁺ ↦ T

 ((x : Y) × Y(x))⁺ ↦ (x : Y⁺) × (Y(x))⁺
 (∀(x : Y) Y(x))⁺  ↦ ∀(x : Y⁺) × (Y(x))⁺    
```

Now we can finally write down the cummulativity rules: all closed-form typeformers defined for some universe are also applicable to all higher universes:
```
 Γ, K : U⁺ ⊢ F : □(K → U)      Γ, K : U⁺⁺ ⊢ F : □(K → U⁺)     Γ, K : U⁺⁺⁺ ⊢ F : □(K → U⁺⁺)      
——————————————————————————    ————————————————————————————    ——————————————————————————————   ···
     Γ ⊢ F : K⁺ → U⁺               Γ ⊢ F : K⁺ → U⁺⁺               Γ ⊢ F : K⁺ → U⁺⁺⁺
```

This rule guarantees that closed-form type definitions such as `𝟙 : U`, `(ℕ → 𝔹) : U`, `List<T : U> : U`, `GroupStructureOn(T : U)`, `CatStructureOn(Ob : U, Hom : Ob → Ob → U)`, and `GroupHomomorphism((X : U) × GroupStructureOn(X) × (Y : U) × GroupStructureOn(Y))` become applicable to types from all universes above `U`. 

We can also write down polymorphic lifting rule: polymorphic proofs/definitions are automatically applicable in all higher universes. 
```
 Γ, K : U⁺ ⊢ F : □(K → U)     Γ ⊢ c : □∀<T : K> F(T)
—————————————————————————————–––––––––———————————————
            Γ ⊢ c : ∀<T : K⁺> F(T)
```

For example, assume we have proven the Cayley's embedding theorem for U-small groups:
```
cayleyEmbedding : ∀<G : U> ∀(g : GroupStructureOn<G>) GroupHomomorphism((G, g), sym(G))
```

With the rule above, it automatically applies also to groups in any universe U.

We have just achieved that closed-form typeformer definitions and closed-form proofs that depend on types irrelevantly automatically become fully polymorphic without mentioning universe levels explicitly in any way.

Note that the coinductively defined operator ( ⁺) is reminds of another coinductively defined operator on types, namely the ( ᵈ) operator in [Displayed Type Theory](https://arxiv.org/abs/2311.18781), which allows to derive the displayed category of all groups `CatStructureOnᵈ GroupStructureOn GroupHomomorphism` from the type classes mentioned above. Given a proof of, say, Yoneda's lemma, for U-small categories we actually want it to be applicable not only for categories of arbitrary size, but also for arbitrary displayed categories, which now can be achieved using a simple generalization of the lifting rule above. Ultimately we want to exhibit a type theory (cf. https://akuklev.github.io/reedy-types) where the Yoneda's lemma can be stated (and proven) for ω-categories and will automatically apply to the ω-category of all ω-categories.

# Unary parametricity

It is worth mentioning that □-modality together with ( ᵈ) operator from Displayed Type Theory allows □-internal parametric reasoning. 

Indeed, every inductive type `I` comes with a typeclass `I-Mod<T : U>` of I-structures. For example, for natural numbers we have
```
structure ℕ-Mod<T : U>
  base : T
  next : T → T
```

Every inductive type also has a Church encoding Iᶜ, for example
```
ℕᶜ := ∀<T : U> ℕ-Mod<T> → T
0ᶜ := { T :° U, m : ℕ-Mod<T> ↦ m.base }
1ᶜ := { T :° U, m : ℕ-Mod<T> ↦ m.step m.base }
2ᶜ := { T :° U, m : ℕ-Mod<T> ↦ m.step (m.step m.base) }
...
```

Church encoded form of the inductive type forms an instance of the type class I-Mod:
```
instance ℕᶜ : ℕ-Mod<ℕᶜ>
  base: 0ᶜ
  next: ( ⁺)ᶜ
```

Unary parametricity is given by the following rule for each inductive type:
```
I-par : (n : □Iᶜ) → (R : I-Modᵈ Iᶜ) → (R n)
```

These operators can be used for instance to derive the classical “theorem for free” for the unit type:
```
def m : 𝟙-Modᵈ 𝟙ᶜ {id : 𝟙ᶜ ↦ (id ≃ { x ↦ x } }
  point: refl

Theorem ∀(id : □∀<T : U> T → T) id ≃ { x ↦ x }
  𝟙-par id m
```

We have just shown that the only closed-form inhabitant of the type `∀<T : U> T → T` is `{ x ↦ x }`.

# Further work: Classical reasoning and functional logic programming

In a [related draft](https://akuklev.github.io/modalities) we argue that it is also possible to introduce a modality dual to □, namely the S4-possibility modality mapping each type `T` to a spectrum `◇T` of its formal inhabitants, i.e. inhabitants that can “non-constructively shown to exist” using choice operator (as in Lean4) and double negation elimination as its special case. This modality allows classical (non-constructive) reasoning within ◇-fragment without compromizing computational properties of the underlying type theory such as canonicity, normalization and decidability of type checking, as well as its compatibility with univalence. It remains this way even if we allow non-constructive proofs to escape the ◇-fragment vie computational Markov principle:
```
 c : Computation<T>   nonDivergence : □◇(c ≠ ⊥)
————————————————————————————————————————————————————
          eval(c, nonDivergence) : T
```
It allows to evaluate Turing-complete computations given a closed-form classical proof of their non-divergence, vastly increasing computational power of the underlying type theory.
