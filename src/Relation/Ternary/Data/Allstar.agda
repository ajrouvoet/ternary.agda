{-# OPTIONS --safe --overlapping-instances #-}
open import Relation.Ternary.Core

module Relation.Ternary.Data.Allstar
  {i} {I : Set i}
  {c} {C : Set c} {{rc : Rel₃ C}}
  where

open import Level
open import Data.Product
open import Data.List hiding (concat)
open import Data.List.Relation.Ternary.Interleaving.Propositional as I

open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Structures {A = C} _≡_
open import Relation.Ternary.Construct.List.Interleave I

module _ {u : C} {{m : IsPartialMonoid rc u}} where

  data Allstar {ℓ} (P : I → Pred C ℓ) : List I → Pred C (ℓ ⊔ c ⊔ i) where
    nil  :            ε[ Allstar P [] ]
    cons : ∀ {x xs} → ∀[ P x ⊙ Allstar P xs ⇒ Allstar P (x ∷ xs) ]

module _ {ℓ} {P : I → Pred C ℓ} {u : C} {{m : IsPartialMonoid rc u}} where

  infixr 5 _:⟨_⟩:_
  pattern _:⟨_⟩:_ x p xs = cons (x ∙⟨ p ⟩ xs)

  singleton : ∀ {x} → ∀[ P x ⇒ Allstar P [ x ] ]
  singleton v = v :⟨ ∙-idʳ ⟩: nil

  concat : ∀ {Γ₁ Γ₂} → ∀[ Allstar P Γ₁ ⊙ Allstar P Γ₂ ⇒ Allstar P (Γ₁ ++ Γ₂) ] 
  concat (nil ∙⟨ s ⟩ env₂) rewrite ∙-id⁻ˡ s = env₂
  concat ((v :⟨ s ⟩: env₁) ∙⟨ s' ⟩ env₂) =
    let _ , eq₁ , eq₂ = ∙-assocᵣ s s' in
    v :⟨ eq₁ ⟩: (concat (env₁ ∙⟨ eq₂ ⟩ env₂))

module _ {u : C} {{m : IsPartialCommutativeMonoid rc u}} where

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

