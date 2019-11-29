{-# OPTIONS --safe #-}
open import Relation.Ternary.Core

module Relation.Ternary.Structures.PartialJoinoid
  {a} {A : Set a}
  where

open import Level

open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid
open import Relation.Ternary.Structures.Commutative

record IsJoinoid {e} (_≈_ : A → A → Set e)
  (▹-rel : Rel₃ A)
  (∥-rel  : Rel₃ A)
  (∣-rel  : Rel₃ A)
  (u : A)
  : Set (a ⊔ e) where

  open Rel₃ ▹-rel using ()
    renaming (_∙_≣_ to _▹_≣_; _⊙_ to _▹_)
  open Rel₃ ∥-rel  using ()
    renaming (_∙_≣_ to _∥_≣_; _⊙_ to _∥_)
  open Rel₃ ∣-rel  using ()
    renaming (_∙_≣_ to _∣_≣_; _⊙_ to _∣_)

  field
    overlap {{▹-isMonoid}} : IsPartialMonoid _≈_ ▹-rel u
    overlap {{∥-isCommutativeMonoid}} : IsCommutativeMonoid _≈_ ∥-rel u
    overlap {{∣-isSemigroup}} : IsPartialSemigroup _≈_ ∣-rel

    -- sequential composition distributes over choice
    ▹-distrib-∣ : Distribᵣ ∣-rel ▹-rel

    -- parallel composition distributes over choice
    ∥-distrib-∣ : Distribᵣ ∣-rel ∥-rel
