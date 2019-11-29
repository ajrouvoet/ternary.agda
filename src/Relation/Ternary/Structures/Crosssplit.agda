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

record IsCrosssplittable {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) : Set (a ⊔ e) where
  open Rel₃ rel

  field
    cross : ∀ {a b c d z}
      → a ∙ b ≣ z
      → c ∙ d ≣ z
      → Σ[ frags ∈ (A × A × A × A) ]
        let ac , ad , bc , bd = frags
        in ac ∙ ad ≣ a
         × bc ∙ bd ≣ b
         × ac ∙ bc ≣ c
         × ad ∙ bd ≣ d

    uncross : ∀ {a b c d ac ad bc bd}
      → ac ∙ ad ≣ a
      → bc ∙ bd ≣ b
      → ac ∙ bc ≣ c
      → ad ∙ bd ≣ d
      → Σ[ z ∈ A ]
          a ∙ b ≣ z
        × c ∙ d ≣ z

open IsCrosssplittable {{...}} public
