{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Separation.Construct.List.Interweave {a} (A : Set a) where

open import Level
open import Data.Product
open import Data.List
open import Data.List.Properties using (++-isMonoid)
open import Data.List.Relation.Ternary.Interleaving.Propositional as I public
open import Data.List.Relation.Ternary.Interleaving.Properties
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Binary.Permutation.Inductive

open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary hiding (_∈_; _⊢_)
open import Relation.Ternary.Separation

private 
  Carrier = List A
  variable
    xˡ xʳ x y z : A
    xsˡ xsʳ xs ys zs xxs yys : Carrier

{- Separate a single element from a list -}
data _⊛_≣_ : A → Carrier → Carrier → Set a where
  here  : x ⊛ xs ≣ (x ∷ xs)
  there : x ⊛ xs ≣ xxs → x ⊛ (y ∷ xs) ≣ (y ∷ xxs)

{- Separate a list into two, module permutations, by repeatedly selection one element -}
data Weave : (xs ys zs : Carrier) → Set a where
  fromˡ : x ⊛ xs ≣ xxs → Weave xs ys zs → Weave xxs ys (x ∷ zs)
  fromʳ : y ⊛ ys ≣ yys → Weave xs ys zs → Weave xs yys (y ∷ zs)
  []    : Weave [] [] []

instance 
  weave-sep : RawSep Carrier
  weave-sep = record { _⊎_≣_ = Weave }

  weave-is-sep : IsSep weave-sep

  IsSep.⊎-comm weave-is-sep [] = []
  IsSep.⊎-comm weave-is-sep (fromˡ x σ) = fromʳ x (⊎-comm σ)
  IsSep.⊎-comm weave-is-sep (fromʳ x σ) = fromˡ x (⊎-comm σ)

  IsSep.⊎-assoc weave-is-sep σ₁ σ₂ = {!!}

  
