{-# OPTIONS --safe #-}
module Relation.Ternary.Structures.PartialMonoid {a} {A : Set a} where

open import Level
open import Function using (_∘_)

open import Relation.Unary hiding (Empty)
open import Relation.Binary.Structures
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core using (Rel₃; Exactly; Respect; coe)
open import Relation.Ternary.Structures.PartialSemigroup

open import Data.Product

record IsPartialMonoid {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) (unit : A) : Set (a ⊔ e) where
  field
    overlap {{ isPartialSemigroup }} : IsPartialSemigroup _≈_ rel

  open Rel₃ rel

  -- because we want to export this name from the record
  ε = unit

  Emp : Pred A a
  Emp = Exactly ε

  field
    ε-unique : ∀[ _≈_ ε ⇒ Emp ]

    ∙-idˡ    : ∀ {Φ} → ε ∙ Φ ≣ Φ
    ∙-idʳ    : ∀ {Φ} → Φ ∙ ε ≣ Φ

    ∙-id⁻ˡ   : ∀ {Φ} → ∀[ ε ∙ Φ ⇒ _≈_ Φ ]
    ∙-id⁻ʳ   : ∀ {Φ} → ∀[ Φ ∙ ε ⇒ _≈_ Φ ]

  ε∙ε : ∀[ ε ∙ ε ⇒ Emp ]
  ε∙ε p = ε-unique (∙-id⁻ˡ p)

  infix 10 ε[_]
  ε[_] : ∀ {ℓ} → Pred A ℓ → Set ℓ
  ε[ P ] = P ε

  ∙-id⁺ˡ : ∀ {Φ} → ∀[ _≈_ Φ ⇒ ε ∙ Φ ]
  ∙-id⁺ˡ eq = coe eq ∙-idˡ

  ∙-id⁺ʳ : ∀ {Φ} → ∀[ _≈_ Φ ⇒ Φ ∙ ε ]
  ∙-id⁺ʳ eq = coe eq ∙-idʳ

  {- Emptyness -}
  module _ where

    data Empty {p} (P : Set p) : Pred A (a ⊔ p) where
      emp : P → Empty P ε

  module _ {p} {P : Pred A p} {{_ : Respect _≈_ P}} where
    ⊙-id⁻ʳ : ∀[ P ⊙ Emp ⇒ P ]
    ⊙-id⁻ʳ (px ∙⟨ σ ⟩ refl) = coe (∙-id⁻ʳ σ) px

    ⊙-id⁻ˡ : ∀[ Emp ⊙ P ⇒ P ]
    ⊙-id⁻ˡ (refl ∙⟨ σ ⟩ px) = coe (∙-id⁻ˡ σ) px 

  module _ {p} {P : Pred A p} where
    ⊙-idʳ : ∀[ P ⇒ P ⊙ Emp ]
    ⊙-idʳ px = px ∙⟨ ∙-idʳ ⟩ refl

    ⊙-idˡ : ∀[ P ⇒ Emp ⊙ P ]
    ⊙-idˡ px = refl ∙⟨ ∙-idˡ ⟩ px

  {- A free preorder -}
  module _ where

    ≤-reflexive : Φ₁ ≡ Φ₂ → Φ₁ ≤ Φ₂
    ≤-reflexive refl = ε , ∙-idʳ

    ≤-isPreorder : IsPreorder _≡_ _≤_
    ≤-isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive = ≤-reflexive
      ; trans = ≤-trans }

    ≤-preorder : Preorder _ _ _
    ≤-preorder = record { isPreorder = ≤-isPreorder }

    ε-minimal : ∀ {Φ} → ε ≤ Φ
    ε-minimal {Φ} = Φ , ∙-idˡ

open IsPartialMonoid {{...}} public
