{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Construct.Bag.Properties {ℓ} {A : Set ℓ} where

open import Level
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Extra
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties

open import Relation.Nullary
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module CrossSplittable
  {{div₁ : Rel₃ A}} {{div₂ : Rel₃ A}}
  {e} {_≈₁_ : A → A → Set e} {_≈₂_ : A → A → Set e}
  {{_ : IsCommutative div₁}} {{_ : IsPartialSemigroup _≈₁_ div₁}}
  {{_ : IsCommutative div₂}} {{_ : IsPartialSemigroup _≈₂_ div₂}}
  (xsplitₐ : CrossSplit div₁ div₂)
  where

  open import Relation.Ternary.Construct.List div₁ as I₁
  open import Relation.Ternary.Construct.List div₂ as I₂

  open Rel₃ div₁ using () renaming (_∙_≣_ to _∙ₐ₁_≣_)
  open Rel₃ div₂ using () renaming (_∙_≣_ to _∙ₐ₂_≣_)

  open import Relation.Ternary.Construct.Bag div₁ tt as L
  open import Relation.Ternary.Construct.Bag div₂ tt as R

  open Rel₃ L.bags using () renaming (_∙_≣_ to _∙₁_≣_)
  open Rel₃ R.bags using () renaming (_∙_≣_ to _∙₂_≣_)

  open import Relation.Ternary.Construct.List.Properties
  private module X = ListXSplit div₁ div₂ xsplitₐ
  
  xsplit : CrossSplit L.bags R.bags
  xsplit (hustle ρx ρy ρz σ₁) (hustle ρx₁ ρy₁ ρz₁ σ₂) with I₁.∙-↭ σ₁ (smart-trans ρz (↭-sym ρz₁))
  ... | _ , ρₗ , ρᵣ , σ₁′ with X.xsplit σ₁′ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ =
    -, R.hustle ↭-refl ↭-refl (smart-trans ρₗ ρx) σ₃
     , R.hustle ↭-refl ↭-refl (smart-trans ρᵣ ρy) σ₄
     , L.hustle ↭-refl ↭-refl ρx₁ σ₅
     , L.hustle ↭-refl ↭-refl ρy₁ σ₆

  module _ (no-div₂ : ∀ {x y xy} → ¬ (x ∙ₐ₂ y ≣ xy)) where

    unxcross : Uncross L.bags R.bags
    unxcross (hustle ρx₁ ρy₁ ρz₁ σ₁) (hustle ρx₂ ρy₂ ρz₂ σ₂)
            (hustle ρx₃ ρy₃ ρz₃ σ₃) (hustle ρx₄ ρy₄ ρz₄ σ₄)
              with ↭-∙ no-div₂ σ₃ (smart-trans ρx₃ (↭-sym ρx₁)) (smart-trans ρy₃ (↭-sym ρx₂))
                 | ↭-∙ no-div₂ σ₄ (smart-trans ρx₄ (↭-sym ρy₁)) (smart-trans ρy₄ (↭-sym ρy₂))
    ... | _ , ρc , σ₃′ | _ , ρd , σ₄′ with X.unxross no-div₂ σ₁ σ₂ σ₃′ σ₄′
    ... | _ , ρa , ρb , ρc' , ρd' , τ₁ , τ₂ =
      -, R.hustle (smart-trans (↭-sym ρa) ρz₁) (smart-trans (↭-sym ρb) ρz₂) ↭-refl τ₁
       , L.hustle (smart-trans (smart-trans (↭-sym ρc') ρc) ρz₃) (smart-trans (smart-trans (↭-sym ρd') ρd) ρz₄) ↭-refl τ₂

open import Relation.Ternary.Structures.Syntax
module _
  {{div : Rel₃ A}}
  {e} {_≈_ : A → A → Set e}
  {{_ : IsCommutative div}} {{_ : IsPartialSemigroup _≈_ div}} where

  open import Relation.Ternary.Construct.List div hiding (splits)
  open import Relation.Ternary.Construct.Bag div tt
  open import Data.List.Relation.Unary.All
  import Relation.Ternary.Construct.List.Properties as List

  module _ {p} {P : Pred A p} (divP : ∀ {a b c} → a ∙ b ≣ c → P c → P a × P b) where

    splitAll : ∀ {xs ys zs} → xs ∙ ys ≣ zs → All P zs → All P xs × All P ys
    splitAll (hustle ρx ρy ρz sep) pzs = 
      let
        pzs' = All-resp-↭ (↭-sym ρz) pzs
        pxs' , pys' = List.splitAll divP sep pzs'
      in All-resp-↭ ρx pxs' , All-resp-↭ ρy pys' 

  module _ {p} {P : Pred A p} (joinP : ∀ {a b c} → a ∙ b ≣ c → P a → P b → P c) where

    joinAll : ∀ {xs ys zs} → xs ∙ ys ≣ zs → All P xs → All P ys → All P zs
    joinAll (hustle ρx ρy ρz sep) pxs pys =
      let
        pxs' = All-resp-↭ (↭-sym ρx) pxs
        pys' = All-resp-↭ (↭-sym ρy) pys
      in All-resp-↭ ρz (List.joinAll joinP sep pxs' pys')
