{-# OPTIONS --safe #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Data.ReflexiveTransitive
  {c} {C : Set c} {{rc : Rel₃ C}}
  where

open import Level
open import Data.Product
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

module _
  {_≈_ : C → C → Set c} {u} {{_ : IsCommutativeMonoid _≈_ rc u}}
  {A : Set c} (R : A → A → Pred C c) where

  data Star : (a₁ a₂ : A) → Pred C c where
    nil   : ∀ {a}        → ε[ Star a a ]
    cons  : ∀ {a₁ a₂ a₃} → ∀[ R a₁ a₂ ⊙ Star a₂ a₃ ⇒ Star a₁ a₃ ]

  instance star-respects : ∀ {a₁ a₂ : A} → Respect _≈_ (Star a₁ a₂)
  Respect.coe star-respects eq nil with ε-unique eq
  ... | refl = nil
  Respect.coe star-respects eq (cons x) = cons (coe eq x)

  pattern _▹⟨_⟩_ r σ rs = cons (r ∙⟨ σ ⟩ rs)

  append : ∀ {a₁ a₂ a₃} → ∀[ Star a₁ a₂ ⇒ Star a₂ a₃ ─⊙ Star a₁ a₃ ]
  append nil ⟨ σ ⟩ y = coe (∙-id⁻ʳ σ) y
  append (cons (r ∙⟨ σ₁ ⟩ rs)) ⟨ σ₂ ⟩ y = 
    let _ , σ₃ , σ₄ = ∙-assocᵣ σ₁ (∙-comm σ₂) in
    r ▹⟨ σ₃ ⟩ (append rs ⟨ ∙-comm σ₄ ⟩ y)
