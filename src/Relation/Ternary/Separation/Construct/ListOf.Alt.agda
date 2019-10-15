open import Relation.Unary.Separation

module Relation.Unary.Separation.Construct.ListOf 
  {a} (A : Set a) 
  {{ r : RawSep A }}
  {{ _ : IsSep r }}
  where

open import Level
open import Data.Product
open import Data.List
open import Data.List.Properties using (++-isMonoid)
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Binary.Permutation.Inductive

open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary hiding (_∈_; _⊢_)

open import Relation.Unary.Separation.Morphisms

private 
  Carrier = List A
  variable
    xˡ xʳ x y z : A
    xsˡ xsʳ xs ys zs : Carrier

data Split : (xs ys zs : Carrier) → Set a where
  divide   : xˡ ⊎ xʳ ≣ x → Split xs ys (xˡ ∷ xʳ ∷ zs) → Split xs ys (x ∷ zs)
  to-left  : Split xs ys zs → Split (z ∷ xs) ys (z ∷ zs)
  to-right : Split xs ys zs → Split xs (z ∷ ys) (z ∷ zs)
  []       : Split [] [] []
-- Split yields a separation algebra
instance
  splits : RawSep Carrier
  RawSep._⊎_≣_ splits = Split

  split-is-sep : IsSep splits

  -- commutes
  IsSep.⊎-comm split-is-sep (divide τ σ) = divide τ (⊎-comm σ)
  IsSep.⊎-comm split-is-sep (to-left σ)  = to-right (⊎-comm σ)
  IsSep.⊎-comm split-is-sep (to-right σ) = to-left (⊎-comm σ)
  IsSep.⊎-comm split-is-sep [] = []
  
  -- reassociates
  IsSep.⊎-assoc split-is-sep σ₁ (divide x σ₂) =
    let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in -, divide x σ₃ , σ₄
  IsSep.⊎-assoc split-is-sep (divide x σ₁) (to-left σ₂) = {!!}
  IsSep.⊎-assoc split-is-sep (to-left σ₁) (to-left σ₂) = {!!}
  IsSep.⊎-assoc split-is-sep (to-right σ₁) (to-left σ₂) = {!!} 
  IsSep.⊎-assoc split-is-sep σ₁ (to-right σ₂) =
    let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in -, to-right σ₃ , to-right σ₄
  IsSep.⊎-assoc split-is-sep [] [] = -, [] , []

  
  -- split-is-unital : IsUnitalSep splits []
  -- IsUnitalSep.⊎-idˡ split-is-unital {[]}                           = []
  -- IsUnitalSep.⊎-idˡ split-is-unital {x ∷ Φ}                        = to-right ⊎-idˡ
  -- IsUnitalSep.⊎-id⁻ˡ split-is-unital (to-right σ) rewrite ⊎-id⁻ˡ σ = refl
  -- IsUnitalSep.⊎-id⁻ˡ split-is-unital []                            = refl
  
  -- split-has-concat : IsConcattative splits
  -- IsConcattative._∙_ split-has-concat = _++_
  -- IsConcattative.⊎-∙ₗ split-has-concat {Φₑ = []} σ = σ
  -- IsConcattative.⊎-∙ₗ split-has-concat {Φₑ = x ∷ Φₑ} σ = to-left (⊎-∙ₗ σ) 
  
  -- split-separation : Separation _
  -- split-separation = record { Carrier = List A }

  -- split-monoidal : MonoidalSep _
  -- split-monoidal = record { monoid = ++-isMonoid }

  -- list-positive : IsPositive splits
  -- list-positive = record
  --   { ⊎-εˡ = λ where [] → refl }

-- unspliceᵣ : ∀ {xs ys zs : Carrier} {y} → xs ⊎ (y ∷ ys) ≣ zs → ∃ λ zs₁ → xs ⊎ [ y ] ≣ zs₁ × zs₁ ⊎ ys ≣ zs
-- unspliceᵣ σ with ⊎-unassoc σ (⊎-∙ {Φₗ = [ _ ]})
-- ... | _ , σ₁ , σ₂ = -, σ₁ , σ₂
