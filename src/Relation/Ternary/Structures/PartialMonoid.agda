{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Structures.PartialMonoid {a} {A : Set a} where

open import Level
open import Function using (_∘_)

open import Relation.Unary hiding (Empty)
open import Relation.Binary.Structures
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.PartialSemigroup

open import Data.Product

-- This is abstracted from the monoid instance to accomodate unambiguous
-- use of ε/Emp in contexts with multiple monoidal relations on a single carrier
record Emptiness (unit : A) : Set where
  ε : A
  ε = unit

  Emp : Pred A a
  Emp = Own ε

  infix 10 ε[_]
  ε[_] : ∀ {ℓ} → Pred A ℓ → Set ℓ
  ε[ P ] = P ε

  data Empty {p} (P : Set p) : Pred A (a ⊔ p) where
    emp : P → Empty P ε

open Emptiness {{...}}

record IsPartialMonoid {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) (unit : A) : Set (a ⊔ e) where
  field
    overlap {{ emptiness }}   : Emptiness unit
    overlap {{ isSemigroup }} : IsPartialSemigroup _≈_ rel

  open Rel₃ rel
  open IsPartialSemigroup isSemigroup
  module Eq = IsEquivalence ≈-equivalence

  field
    ∙-idˡ    : LeftIdentity rel ε
    ∙-idʳ    : RightIdentity rel ε

    ∙-id⁻ˡ   : LeftIdentity⁻ _≈_ rel ε
    ∙-id⁻ʳ   : RightIdentity⁻ _≈_ rel ε
    
  Emp′ = λ x → x ≈ ε

  ε∙ε′ : ∀[ ε ∙ ε ⇒ Emp′ ]
  ε∙ε′ p = Eq.sym (∙-id⁻ˡ p)

  ε∙ε : {{_ : IsUnique _≈_ ε}} → ∀[ ε ∙ ε ⇒ Emp ]
  ε∙ε p = unique (∙-id⁻ˡ p)

  ∙-id⁺ˡ : ∀[ _≈_ Φ ⇒ ε ∙ Φ ]
  ∙-id⁺ˡ eq = coe eq ∙-idˡ

  ∙-id⁺ʳ : ∀[ _≈_ Φ ⇒ Φ ∙ ε ]
  ∙-id⁺ʳ eq = coe eq ∙-idʳ

  module _ {p} {P : Pred A p} {{_ : Respect _≈_ P}} where
    ✴-id⁻ʳ : ∀[ P ✴ Emp ⇒ P ]
    ✴-id⁻ʳ (px ∙⟨ σ ⟩ refl) = coe (∙-id⁻ʳ σ) px

    ✴-id⁻ˡ : ∀[ Emp ✴ P ⇒ P ]
    ✴-id⁻ˡ (refl ∙⟨ σ ⟩ px) = coe (∙-id⁻ˡ σ) px 

  module _ {p} {P : Pred A p} where
    ✴-idʳ : ∀[ P ⇒ P ✴ Emp ]
    ✴-idʳ px = px ∙⟨ ∙-idʳ ⟩ refl

    ✴-idˡ : ∀[ P ⇒ Emp ✴ P ]
    ✴-idˡ px = refl ∙⟨ ∙-idˡ ⟩ px
  module _ {p q} {P : Pred A p} {Q : Pred A q} {{_ : Respect _≈_ Q}} where

    arrow : ∀[ P ⇒ Q ] → ε[ P ─✴ Q ]
    arrow f ⟨ σ ⟩ px = coe (∙-id⁻ˡ σ) (f px)

  {- A free preorder -}
  module _ where

    ≤-reflexive : Φ₁ ≡ Φ₂ → Φ₁ ≤ Φ₂
    ≤-reflexive refl = ε , ∙-idʳ

    ≤-isPreorder : IsPreorder _≡_ _≤_
    ≤-isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive = ≤-reflexive
      ; trans = ≤-trans }

    open IsPreorder ≤-isPreorder using () renaming (refl to ≤-refl) public

    ≤-preorder : Preorder _ _ _
    ≤-preorder = record { isPreorder = ≤-isPreorder }

    ε-minimal : ∀ {Φ} → ε ≤ Φ
    ε-minimal {Φ} = Φ , ∙-idˡ
