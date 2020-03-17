{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Construct.Exchange.Param where

open import Level
open import Relation.Unary
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

record Param {ℓ e} (A : Set ℓ) (εₐ : A) (r₁ : Rel₃ A) (r₂ : Rel₃ A) (_≈ₐ_ : A → A → Set e) s : Set (suc (ℓ ⊔ e ⊔ s)) where
  constructor params
  field
    instance  r₁-monoid  : IsPartialMonoid _≈ₐ_ r₁ εₐ
    instance  r₂-monoid  : IsPartialMonoid _≈ₐ_ r₂ εₐ
    instance  r₁-positive  : IsPositive s _≈ₐ_ r₁ εₐ
    instance  r₂-positive  : IsPositive s _≈ₐ_ r₂ εₐ
    instance  r₁-comm : IsCommutative r₁ 
    instance  r₂-comm : IsCommutative r₂ 
    instance r₂-intuitive : IsIntuitionistic U r₂  
    xsplitₐ  : CrossSplit r₂ r₁
    uncrossₐ : Uncross r₁ r₂
