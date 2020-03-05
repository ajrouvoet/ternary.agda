{-# OPTIONS --safe #-}
module Relation.Ternary.Structures.Crosssplit {a} {A : Set a} where

open import Level
open import Relation.Unary
open import Relation.Binary.Structures

open import Function using (_∘_)
open import Data.Product

open import Relation.Ternary.Core using (Rel₃; Respect; coe; Exactly; Commutative)
open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid

module _ (r₁ r₂ : Rel₃ A) where
  open Rel₃ r₁ using () renaming (_∙_≣_ to _∙₁_≣_)
  open Rel₃ r₂ using () renaming (_∙_≣_ to _∙₂_≣_)

  CrossSplit : Set a
  CrossSplit = ∀ {a b c d z} →
    a ∙₁ b ≣ z → c ∙₂ d ≣ z →
    Σ[ frags ∈ (A × A × A × A) ] 
    let ac , ad , bc , bd = frags
    in ac ∙₂ ad ≣ a × bc ∙₂ bd ≣ b × ac ∙₁ bc ≣ c × ad ∙₁ bd ≣ d

  Uncross : Set a
  Uncross = ∀ {a b c d ac ad bc bd}
    → ac ∙₁ ad ≣ a
    → bc ∙₁ bd ≣ b
    → ac ∙₂ bc ≣ c
    → ad ∙₂ bd ≣ d
    → Σ[ z ∈ A ]
      a ∙₂ b ≣ z
      × c ∙₁ d ≣ z

record IsCrosssplittable {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) : Set (a ⊔ e) where
  open Rel₃ rel

  field
    cross   : CrossSplit rel rel
    uncross : Uncross rel rel

open IsCrosssplittable {{...}} public
