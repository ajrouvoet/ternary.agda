{-# OPTIONS --safe #-}
open import Relation.Ternary.Separation

module Relation.Ternary.Separation.Construct.List.Interdivide
  {a} (A : Set a) 
  (division : RawSep A)
  {{_ : IsSep division}}
  where

open import Level
open import Data.Product
open import Data.List
open import Data.List.Properties using (++-isMonoid)
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Binary.Permutation.Inductive
open import Algebra.Structures using (IsMonoid)
open import Relation.Ternary.Separation.Decoration

open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary hiding (_∈_; _⊢_)

private 
  instance sep-instance = division
  Carrier = List A
  variable
    xˡ xʳ x y z : A
    xsˡ xsʳ xs ys zs : Carrier

data Split : (xs ys zs : Carrier) → Set a where
  divide   : xˡ ⊎ xʳ ≣ x → Split xs ys zs → Split (xˡ ∷ xs) (xʳ ∷ ys) (x ∷ zs)
  consˡ    : Split xs ys zs → Split (z ∷ xs) ys (z ∷ zs)
  consʳ    : Split xs ys zs → Split xs (z ∷ ys) (z ∷ zs)
  []       : Split [] [] []


-- Split yields a separation algebra
instance
  splits : RawSep Carrier
  RawSep._⊎_≣_ splits = Split

  split-is-sep : IsSep splits

  -- commutes
  IsSep.⊎-comm split-is-sep (divide τ σ) = divide (⊎-comm τ) (⊎-comm σ)
  IsSep.⊎-comm split-is-sep (consˡ σ)  = consʳ (⊎-comm σ)
  IsSep.⊎-comm split-is-sep (consʳ σ) = consˡ (⊎-comm σ)
  IsSep.⊎-comm split-is-sep [] = []
  
  -- reassociates
  IsSep.⊎-assoc split-is-sep σ₁ (consʳ σ₂) with ⊎-assoc σ₁ σ₂
  ... | _ , σ₄ , σ₅ = -, consʳ σ₄ , consʳ σ₅
  IsSep.⊎-assoc split-is-sep (consˡ σ₁) (divide τ σ₂) with ⊎-assoc σ₁ σ₂
  ... | _ , σ₄ , σ₅ = -, divide τ σ₄ , consʳ σ₅
  IsSep.⊎-assoc split-is-sep (consʳ σ₁) (divide τ σ₂)  with ⊎-assoc σ₁ σ₂
  ... | _ , σ₄ , σ₅ = -, consʳ σ₄ , divide τ σ₅
  IsSep.⊎-assoc split-is-sep (divide τ σ₁) (consˡ σ) with ⊎-assoc σ₁ σ
  ... | _ , σ₄ , σ₅ = -, divide τ σ₄ , consˡ σ₅
  IsSep.⊎-assoc split-is-sep (consˡ σ₁) (consˡ σ)  with ⊎-assoc σ₁ σ
  ... | _ , σ₄ , σ₅ = -, consˡ σ₄ , σ₅
  IsSep.⊎-assoc split-is-sep (consʳ σ₁) (consˡ σ) with ⊎-assoc σ₁ σ
  ... | _ , σ₄ , σ₅ = -, consʳ σ₄ , consˡ σ₅
  IsSep.⊎-assoc split-is-sep [] [] = -, [] , []
  IsSep.⊎-assoc split-is-sep (divide lr σ₁) (divide rl σ₂) with ⊎-assoc σ₁ σ₂ | ⊎-assoc lr rl
  ... | _ , σ₃ , σ₄ | _ , τ₃ , τ₄ = -, divide τ₃ σ₃ , divide τ₄ σ₄

  
  split-has-unit⁺ : HasUnit⁺ splits []
  HasUnit⁺.⊎-idˡ split-has-unit⁺ {[]} = []
  HasUnit⁺.⊎-idˡ split-has-unit⁺ {x ∷ Φ} = consʳ ⊎-idˡ

  split-has-unit⁻ : HasUnit⁻ splits []
  HasUnit⁻.⊎-id⁻ˡ split-has-unit⁻ (consʳ σ) rewrite ⊎-id⁻ˡ σ = refl
  HasUnit⁻.⊎-id⁻ˡ split-has-unit⁻ [] = refl

  split-is-unital : IsUnitalSep splits []
  split-is-unital = record {}
  
  split-has-concat : HasConcat splits
  HasConcat._∙_ split-has-concat = _++_
  HasConcat.⊎-∙ₗ split-has-concat {Φₑ = []} σ = σ
  HasConcat.⊎-∙ₗ split-has-concat {Φₑ = x ∷ Φₑ} σ = consˡ (⊎-∙ₗ σ) 
  
  list-positive : IsPositive splits []
  list-positive = record
    { ⊎-εˡ = λ where [] → refl }

  list-monoid : ∀ {a} {A : Set a} → IsMonoid {A = List A} _≡_ _++_ []
  list-monoid = ++-isMonoid

{- Lemmas about List splittings -}
module _ where

  unspliceᵣ : ∀ {xs ys zs : Carrier} {y} →
              xs ⊎ (y ∷ ys) ≣ zs →
              ∃ λ zs₁ → xs ⊎ [ y ] ≣ zs₁ × zs₁ ⊎ ys ≣ zs
  unspliceᵣ σ with ⊎-unassoc σ (⊎-∙ {Φₗ = [ _ ]})
  ... | _ , σ₁ , σ₂ = -, σ₁ , σ₂

{- Decorations -}
module Decor {p} {P : A → Set p} (PD : Decoration P) where

  open import Data.List.Relation.Unary.All
  open Decoration

  instance all-decorates : Decoration (All P)
  decorˡ all-decorates (divide τ σ) (px ∷ pxs) =
    decorˡ PD τ px ∷ decorˡ all-decorates σ pxs
  decorˡ all-decorates (consˡ σ)    (px ∷ pxs) =
    px ∷ decorˡ all-decorates σ pxs
  decorˡ all-decorates (consʳ σ)    (px ∷ pxs) =
    decorˡ all-decorates σ pxs
  decorˡ all-decorates []           []         =
    []

  instance all-unit-decoration : UnitDecoration (All P)
  UnitDecoration.decor-ε all-unit-decoration = []
