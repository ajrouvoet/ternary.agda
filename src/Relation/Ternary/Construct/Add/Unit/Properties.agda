module Relation.Ternary.Construct.Add.Unit.Properties where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Construct.Add.Unit

module _
  {a} {A : Set a}
  {{div₁ : Rel₃ A}} {{div₂ : Rel₃ A}}
  (xsplit : CrossSplit div₁ div₂) where

  maybe-cross : CrossSplit  (maybes div₁) (maybes div₂)
  maybe-cross nothing nothing      = -, nothing , nothing , nothing , nothing
  maybe-cross right right          = -, nothing , right , nothing , right
  maybe-cross right left           = -, nothing , left , right , nothing
  maybe-cross right (split x)      = -, nothing , split x , right , right
  maybe-cross left right           = -, right , nothing , nothing , left
  maybe-cross left left            = -, left , nothing , left , nothing
  maybe-cross left (split x)       = -, split x , nothing , left , left
  maybe-cross (split x) right      = -, right , right , nothing , split x
  maybe-cross (split x) left       = -, left , left , split x , nothing
  maybe-cross (split x) (split y) with _ , τ₁ , τ₂ , τ₃ , τ₄ ← xsplit x y =
    -, split τ₁ , split τ₂ , split τ₃ , split τ₄

  -- maybe-unross does not hold!
