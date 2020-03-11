{- Some smart constructors for semigroups and monoids -}
module _  where

  -- left biased
  record IsPartialSemigroupˡ {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) : Set (a ⊔ e) where
    open Rel₃ rel
    field
      ≈-equivalence  : IsEquivalence _≈_

      {{∙-respects-≈}}   : ∀ {Φ₁ Φ₂} → Respect _≈_ (Φ₁ ∙ Φ₂)
      {{∙-respects-≈ˡ}}  : ∀ {Φ₂ Φ}  → Respect _≈_ (_∙ Φ₂ ≣ Φ)

      {{comm}}           : IsCommutative rel
      assocᵣ             : ∀ {a b ab c abc} → a ∙ b ≣ ab → ab ∙ c ≣ abc
                         → ∃ λ bc → a ∙ bc ≣ abc × b ∙ c ≣ bc
    
    isPartialSemigroupˡ : IsPartialSemigroup _≈_ rel
    Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ isPartialSemigroupˡ) eq = ∙-comm ∘ coe eq ∘ ∙-comm
    IsPartialSemigroup.∙-assocᵣ isPartialSemigroupˡ = assocᵣ
    IsPartialSemigroup.∙-assocₗ isPartialSemigroupˡ σ₁ σ₂ =
      let _ , σ₃ , σ₄ = assocᵣ (∙-comm σ₂) (∙-comm σ₁)
      in -, ∙-comm σ₄ , ∙-comm σ₃

  record IsPartialMonoidˡ {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) (unit : A) : Set (a ⊔ e) where
    open Rel₃ rel

    field
      {{isSemigroup}}   : IsPartialSemigroup _≈_ rel
      {{isCommutative}} : IsCommutative rel
      {{emptiness}}     : Emptiness unit
      ε-uniq     : ∀[ _≈_ unit ⇒ Exactly unit ]
      identityˡ  : ∀ {Φ} → unit ∙ Φ ≣ Φ
      identity⁻ˡ : ∀ {Φ} → ∀[ unit ∙ Φ ⇒ _≈_ Φ ]

  
    partialMonoidˡ : IsPartialMonoid _≈_ rel unit
    IsPartialMonoid.ε-unique partialMonoidˡ = ε-uniq
    IsPartialMonoid.∙-idˡ partialMonoidˡ = identityˡ
    IsPartialMonoid.∙-idʳ partialMonoidˡ = ∙-comm identityˡ
    IsPartialMonoid.∙-id⁻ˡ partialMonoidˡ = identity⁻ˡ
    IsPartialMonoid.∙-id⁻ʳ partialMonoidˡ = identity⁻ˡ ∘ ∙-comm

  -- partialMonoidˡ : ∀ {e} {rel : Rel₃ A} {unit : A} →
  --       let open Rel₃ rel in
  --       {_≈_ : A → A → Set e}
  --       {{psg : IsPartialSemigroup _≈_ rel}}
  --       {{cm  : IsCommutative rel}}
  --       → (ε-unique : ∀[ _≈_ unit ⇒ Exactly unit ])
  --       → (idˡ  : ∀ {Φ} → unit ∙ Φ ≣ Φ)
  --       → (id⁻ˡ : ∀ {Φ} → ∀[ unit ∙ Φ ⇒ _≈_ Φ ])
  --       → IsPartialMonoid _≈_ rel unit
  -- partialMonoidˡ {rel = rel} {unit} {_≈_} {{pcsg}} ε-unique idˡ id⁻ˡ = isPartialMonoid′
  --   where
  --     open Rel₃ rel

  --     idʳ : ∀ {Φ} → Φ ∙ unit ≣ Φ
  --     idʳ = ∙-comm idˡ

  --     id⁻ʳ   : ∀ {Φ} → ∀[ Φ ∙ unit ⇒ _≈_ Φ ]
  --     id⁻ʳ = id⁻ˡ ∘ ∙-comm

  --     isPartialMonoid′ : IsPartialMonoid _≈_ rel unit
  --     IsPartialMonoid.ε-unique isPartialMonoid′ = ε-unique
  --     IsPartialMonoid.∙-idˡ isPartialMonoid′ = idˡ
  --     IsPartialMonoid.∙-idʳ isPartialMonoid′ = idʳ
  --     IsPartialMonoid.∙-id⁻ˡ isPartialMonoid′ = id⁻ˡ
  --     IsPartialMonoid.∙-id⁻ʳ isPartialMonoid′ = id⁻ʳ
