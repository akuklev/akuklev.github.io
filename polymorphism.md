Polymorphism and modal parametricity via □-modality
===================================================

[author]: mailto:a@kuklev.com "Alexander Kuklev, JetBrains Research"
[Alexander Kuklev](mailto:a@kuklev.com), [JetBrains Research](https://research.jetbrains.org/researchers/alexander.kuklev/)

# Modal approach to polymorphism

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

Now we can clearly see that it is indeed the S4 neccesity modality. But in this form it does not work well with dependent types. To proceed we need to make our type theory {0, ω}-graded, that we'll allow to mark some variales in contexts as computationally irrelevant using zero subscript above the colon. It will allow us to introduce parametric quantifiers `∀<x : X> T(x)` (note angle brackets instead of parens):
```
 Γ ⊢ X : *     Γ, x : X ⊢ Y(x) : *
––––––––————–––––––––––—————————————
   Γ ⊢ ∀<x : Y> Y(x) : *

 Γ ⊢ X : *   Г, x :° X ⊢ y : Y(X)
––––––––––––––––––––––––—————————————
 Г ⊢ (x :° X ↦ Y(X)) : ∀<x : Y> Y(x) 
```

But more importantly, it allows adjust the rules for the □-modality to work well with dependent types. In the introduction rule we allow irrelevant variables, while in the elimination rule we state that a closed-form element can only depend on non-closed elements of the context irrelevantly:
```
   □Г, Δ⁰ ⊢ x : X                  Г ⊢ x : □X(t)
–––––––––––––––———–——(□Intro)     ——————————————–—(□Elim)
 □Г, Δ⁰, Σ ⊢ x : □X                Г° ⊢ x : X(t)

(We use the notation `□Γ` and `Γ⁰` to □ or ⁰ to each element of the context Γ.)
```

Now let us define the universe-shifting operator ( ⁺) for all types. Its action on the other types will be defined on case-by-case basis for all type formers (i.e. coinductively). It shifts the universe levels in types built using universes, e.g. `(U → U)⁺` should be `(U⁺ → U⁺)`, while doing nothing for types inside the base universe as they cannot involve universes in their definitions:
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

This rule guarantees that closed-form type definitions such as `𝟙 : U`, `(ℕ → 𝔹) : U`, `List<T : U> : U`, `GroupStructureOn(T : U)`, CatStructureOn(Ob : U, Hom : Ob → Ob → U), and `GroupHomomorphism((X : U) × GroupStructureOn(X) × (Y : U) × GroupStructureOn(Y))` become applicable to types from all universes above `U`. 

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

Note that the coinductively defined operator ( ⁺) is very similar to the coinductively defined operator ( ᵈ) in Displayed Type Theory, which allows to derive the polymoprhic displayed category of all groups `CatStructureOnᵈ GroupStructureOn GroupHomomorphism` from already defined type polymorphic type classes above. Given a proof of, say, Yoneda's lemma, for U-small categories we actually want it to be applicable not only for categories of arbitrary size, but also for arbitrary displayed categories, which now can be achieved using a simple generalization of the polymorphic lifting rule.
