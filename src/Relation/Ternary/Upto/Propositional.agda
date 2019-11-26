open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.PartialMonoid

module Relation.Ternary.Upto.Propositional
  {a} {A : Set a} {{rel : Rel₃ A}}
  {unit} {{_ : IsPartialMonoid {A = A} _≡_ rel unit}} where

open import Function using (id)
open import Relation.Ternary.Upto {A = A} _≡_
open import Relation.Ternary.Monad.Identity
open import Relation.Ternary.Respect.Propositional

instance ≡-upto : ∀ {p} → Upto p
Upto.⌈ ≡-upto ⌉ = id
Upto.monad ≡-upto = id-monad
