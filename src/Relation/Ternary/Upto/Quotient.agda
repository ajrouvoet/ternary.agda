{-# OPTIONS --safe #-}
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Upto.Quotient
  {a} {A : Set a} {{rel : Rel₃ A}}
  {e} {_≈_ : A → A → Set e}
  {unit} {{_ : IsPartialMonoid {_≈_ = _≈_} rel unit}} where

open import Level
open import Function using (id)
open import Relation.Ternary.Upto {A = A} _≈_
open import Relation.Ternary.Monad.Quotient _≈_ public

instance quotiented-program : Program (a ⊔ e)
Program.⌈ quotiented-program ⌉   = 𝑸
Program.monad quotiented-program = /-monad
