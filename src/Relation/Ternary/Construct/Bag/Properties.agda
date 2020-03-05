module Relation.Ternary.Construct.Bag.Properties {ℓ} {A : Set ℓ} where

open import Level
open import Data.Unit using (⊤)
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Extra
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties

open import Relation.Nullary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module BagXSplit
  {{div₁ : Rel₃ A}} {{div₂ : Rel₃ A}}
  {e} {_≈_ : A → A → Set e}
  {{_ : IsCommutative div₁}} {{_ : IsPartialSemigroup _≈_ div₁}}
  {{_ : IsCommutative div₂}} {{_ : IsPartialSemigroup _≈_ div₂}}
  (xsplitₐ : CrossSplit div₁ div₂)
  where

  open import Relation.Ternary.Construct.List.Interdivide div₁ as I₁
  open import Relation.Ternary.Construct.List.Interdivide div₂ as I₂

  open Rel₃ div₁ using () renaming (_∙_≣_ to _∙ₐ₁_≣_)
  open Rel₃ div₂ using () renaming (_∙_≣_ to _∙ₐ₂_≣_)

  open import Relation.Ternary.Construct.Bag div₁ as L
  open import Relation.Ternary.Construct.Bag div₂ as R

  open Rel₃ L.bags using () renaming (_∙_≣_ to _∙₁_≣_)
  open Rel₃ R.bags using () renaming (_∙_≣_ to _∙₂_≣_)

  open import Relation.Ternary.Construct.List.Interdivide.Properties
  private module X = ListXSplit div₁ div₂ xsplitₐ
  
  xsplit : CrossSplit L.bags R.bags
  xsplit (hustle ρx ρy ρz σ₁) (hustle ρx₁ ρy₁ ρz₁ σ₂) with I₁.∙-↭ σ₁ (↭-trans ρz (↭-sym ρz₁))
  ... | _ , ρₗ , ρᵣ , σ₁′ with X.xsplit σ₁′ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ =
    -, R.hustle ↭-refl ↭-refl (↭-trans ρₗ ρx) σ₃
     , R.hustle ↭-refl ↭-refl (↭-trans ρᵣ ρy) σ₄
     , L.hustle ↭-refl ↭-refl ρx₁ σ₅
     , L.hustle ↭-refl ↭-refl ρy₁ σ₆

  module _ (no-div₂ : ∀ {x y xy} → ¬ (x ∙ₐ₂ y ≣ xy)) where

    unxross : Uncross L.bags R.bags
    unxross (hustle ρx₁ ρy₁ ρz₁ σ₁) (hustle ρx₂ ρy₂ ρz₂ σ₂)
            (hustle ρx₃ ρy₃ ρz₃ σ₃) (hustle ρx₄ ρy₄ ρz₄ σ₄)
              with ↭-∙ no-div₂ σ₃ (↭-trans ρx₃ (↭-sym ρx₁)) (↭-trans ρy₃ (↭-sym ρx₂))
                 | ↭-∙ no-div₂ σ₄ (↭-trans ρx₄ (↭-sym ρy₁)) (↭-trans ρy₄ (↭-sym ρy₂))
    ... | _ , ρc , σ₃′ | _ , ρd , σ₄′ with X.unxross no-div₂ σ₁ σ₂ σ₃′ σ₄′
    ... | _ , ρa , ρb , ρc' , ρd' , τ₁ , τ₂ =
      -, R.hustle (↭-trans (↭-sym ρa) ρz₁) (↭-trans (↭-sym ρb) ρz₂) ↭-refl τ₁
       , L.hustle (↭-trans (↭-trans (↭-sym ρc') ρc) ρz₃) (↭-trans (↭-trans (↭-sym ρd') ρd) ρz₄) ↭-refl τ₂
