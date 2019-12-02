{-# OPTIONS --safe #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Data.Allstar
  -- level restrictions due to use of monadic interface
  {i} (I : Set i)
  {C : Set i} (_≈_ : C → C → Set i) {{rel : Rel₃ C}}
  {u} {{m : IsPartialMonoid _≈_ rel u}} 
  where

open import Level
open import Data.Product
open import Data.List hiding (concat)
open import Data.List.Relation.Ternary.Interleaving.Propositional as I

open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Ternary.Structures
open import Relation.Ternary.Monad
open import Relation.Ternary.Upto {A = C} _≈_

open import Relation.Ternary.Construct.List.Interleave I

module _ {ℓ} (P : I → Pred C ℓ) where

  data Allstar : List I → Pred C (ℓ ⊔ i) where
    nil  :            ε[ Allstar [] ]
    cons : ∀ {x xs} → ∀[ P x ⊙ Allstar xs ⇒ Allstar (x ∷ xs) ]

module _ {ℓ} {P : I → Pred C ℓ} where
  instance allstar-respects-≈ : ∀ {is} → Respect _≈_ (Allstar P is)
  Respect.coe allstar-respects-≈ eq nil with ε-unique eq
  ... | refl = nil
  Respect.coe allstar-respects-≈ eq (cons x) = cons (coe eq x)

module _ {ℓ} {P : I → Pred C ℓ} {u : C} {{m : IsPartialMonoid _≈_ rel u}} where

  infixr 5 _:⟨_⟩:_
  pattern _:⟨_⟩:_ x p xs = cons (x ∙⟨ p ⟩ xs)

  singleton : ∀ {x} → ∀[ P x ⇒ Allstar P [ x ] ]
  singleton v = v :⟨ ∙-idʳ ⟩: nil

  concat : ∀ {Γ₁ Γ₂} → ∀[ Allstar P Γ₁ ⊙ Allstar P Γ₂ ⇒ Allstar P (Γ₁ ++ Γ₂) ] 
  concat (nil ∙⟨ s ⟩ env₂) = coe (∙-id⁻ˡ s) env₂
  concat ((v :⟨ s ⟩: env₁) ∙⟨ s' ⟩ env₂) =
    let
      _ , eq₁ , eq₂ = ∙-assocᵣ s s'
      vs            = concat (env₁ ∙⟨ eq₂ ⟩ env₂)
    in (v :⟨ eq₁ ⟩: vs)

module _ {{_ : IsCommutative rel}} where

  repartition : ∀ {ℓ} {P : I → Pred C ℓ} {Σ₁ Σ₂ Σ} →
                Σ₁ ∙ Σ₂ ≣ Σ → ∀[ Allstar P Σ ⇒ Allstar P Σ₁ ⊙ Allstar P Σ₂ ]
  repartition [] nil   = nil ∙⟨ ∙-idˡ ⟩ nil
  repartition (consˡ σ) (cons (a ∙⟨ σ′ ⟩ qx)) = 
    let
      xs ∙⟨ σ′′ ⟩ ys = repartition σ qx
      _ , τ₁ , τ₂    = ∙-assocₗ σ′ σ′′
    in (a :⟨ τ₁ ⟩: xs) ∙⟨ τ₂ ⟩ ys
  repartition (consʳ σ) (cons (a ∙⟨ σ′ ⟩ qx)) =
    let
      xs ∙⟨ σ′′ ⟩ ys = repartition σ qx
      _ , τ₁ , τ₂    = ∙-assocᵣ σ′′ (∙-comm σ′)
    in xs ∙⟨ τ₁ ⟩ (a :⟨ ∙-comm τ₂ ⟩: ys) 
