{-# OPTIONS --safe --overlapping-instances #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Data.Allstar
  -- level restrictions due to use of monadic interface
  {i} (I : Set i)
  {C : Set i} (_≈_ : C → C → Set i) {{rel : Rel₃ C}}
  {u} {{m : IsPartialMonoid {_≈_ = _≈_} rel u}} 
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

module _ where

  data Allstar {ℓ} (P : I → Pred C ℓ) : List I → Pred C (ℓ ⊔ i) where
    nil  :            ε[ Allstar P [] ]
    cons : ∀ {x xs} → ∀[ P x ⊙ Allstar P xs ⇒ Allstar P (x ∷ xs) ]

module _ {ℓ} {P : I → Pred C ℓ} {u : C} {{m : IsPartialMonoid {_≈_ = _≈_} rel u}} where

  infixr 5 _:⟨_⟩:_
  pattern _:⟨_⟩:_ x p xs = cons (x ∙⟨ p ⟩ xs)

  singleton : ∀ {x} → ∀[ P x ⇒ Allstar P [ x ] ]
  singleton v = v :⟨ ∙-idʳ ⟩: nil

module _ {{_ : IsCommutative {_≈_ = _≈_} rel}} where

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

module _
  {{_ : IsCommutative {_≈_ = _≈_} rel}}
  {{re : Program i}}
  {P : I → Pred C i} where

  concat : ∀ {Γ₁ Γ₂} → ∀[ Allstar P Γ₁ ⊙ Allstar P Γ₂ ∼> Allstar P (Γ₁ ++ Γ₂) ] 
  concat (nil ∙⟨ s ⟩ env₂) = env₂ over (∙-id⁻ˡ s) 
  concat ((v :⟨ s ⟩: env₁) ∙⟨ s' ⟩ env₂) = do
    let _ , eq₁ , eq₂ = ∙-assocᵣ s s'
    vs ∙⟨ σ ⟩ v ← concat (env₁ ∙⟨ eq₂ ⟩ env₂) &⟨ ∙-comm eq₁ ⟩ v
    return (v :⟨ ∙-comm σ ⟩: vs)
