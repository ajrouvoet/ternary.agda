{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core

module Relation.Ternary.Construct.List {a} {A : Set a} (elementDivision : Rel₃ A) where

open import Level
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Properties using (++-isMonoid; ++-identityʳ)
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional
open import Algebra.Structures using (IsMonoid)

open import Relation.Unary hiding (_∈_; _⊢_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; isEquivalence; cong)

open import Relation.Ternary.Structures
open import Relation.Ternary.Respect.Propositional
open import Relation.Ternary.Bundles

open Rel₃ elementDivision

variable
  xˡ xʳ x y z : A
  xsˡ xsʳ xs ys zs : List A

data Split : (xs ys zs : List A) → Set a where
  divide   : xˡ ∙ xʳ ≣ x → Split xs ys zs → Split (xˡ ∷ xs) (xʳ ∷ ys) (x ∷ zs)
  consˡ    : Split xs ys zs → Split (z ∷ xs) ys (z ∷ zs)
  consʳ    : Split xs ys zs → Split xs (z ∷ ys) (z ∷ zs)
  []       : Split [] [] []

-- Split yields a separation algebra
splits : Rel₃ (List A)
Rel₃._∙_≣_ splits = Split

list-emptiness : Emptiness {A = List A} []
list-emptiness = record {}
