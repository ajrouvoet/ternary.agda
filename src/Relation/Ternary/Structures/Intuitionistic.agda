{-# OPTIONS --safe #-}
module Relation.Ternary.Structures.Intuitionistic {a} {A : Set a} where

open import Level
open import Relation.Unary
open import Relation.Ternary.Core

record Intuitionistic {c} (rel : Rel₃ A) : Set (a ⊔ suc c) where
  instance _ = rel
  field
    Condition : A → Set c 
    ∙-copy    : ∀ {xs : A} {{c : Condition xs}} → xs ∙ xs ≣ xs

  copy : ∀ {p} {P : Pred A p} {xs} → {{_ : Condition xs}} → P xs → (P ⊙ P) xs
  copy px = px ∙⟨ ∙-copy ⟩ px

open Intuitionistic {{...}} public
