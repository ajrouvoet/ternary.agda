{-# OPTIONS --postfix-projections #-}
module Relation.Ternary.Bundles where

open import Level
open import Relation.Binary
open import Relation.Binary.Bundles
open import Relation.Ternary.Core hiding (_✴_)
open import Relation.Ternary.Structures using
  ( IsPartialSemigroup
  ; IsPartialMonoid
  ; IsJoinoid )

record PartialSemigroup a e : Set (suc (a ⊔ e)) where
  infix 4 _≈_
  field
    {Carrier}   : Set a
    {_≈_}       : Carrier → Carrier → Set e
    {rel}       : Rel₃ Carrier

    isSemigroup : IsPartialSemigroup _≈_ rel

  open Rel₃ rel public
  open IsPartialSemigroup isSemigroup public

  -- TODO, this one should come from setoid
  instance equivalence : IsEquivalence _≈_
  equivalence = ≈-equivalence

  instance setoid : Setoid a e
  setoid = record { isEquivalence = ≈-equivalence }

  open Setoid setoid public using (partialSetoid; _≉_)

record PartialMonoid a e : Set (suc (a ⊔ e)) where
  field
    {Carrier}   : Set a
    {_≈_}       : Carrier → Carrier → Set e
    {rel}       : Rel₃ Carrier
    {unit}      : Carrier

    isMonoid    : IsPartialMonoid  _≈_ rel unit

  open IsPartialMonoid isMonoid public

  instance partialSemigroup : PartialSemigroup a e
  partialSemigroup = record { isSemigroup = isPartialSemigroup }

open PartialSemigroup {{...}} public
open PartialMonoid    {{...}} public

-- record PartialJoinoid a e : Set (suc (a ⊔ e)) where
--   field
--     setoid : Setoid a e

--   open Setoid setoid public using (_≈_; Carrier)

--   field
--     {▹-rel ∥-rel ∣-rel} : Rel₃ Carrier
--     unit               : Carrier
--     isJoinoid          : IsJoinoid _≈_ ▹-rel ∥-rel ∣-rel unit

--   open IsJoinoid isJoinoid public

-- open PartialJoinoid   {{...}} public

-- open import Relation.Unary
-- open import Relation.Binary.PropositionalEquality
-- open import Data.Nat

-- -- module _ {a e} {{ s₁ : PartialSemigroup 0ℓ e}} {{s₂ : PartialSemigroup a e}} where

-- --   another-assoc : ∀ {P Q R : ℕ → Set} → ∀[ P ✴ (Q ✴ R) ⇒ (P ✴ Q) ✴ R ]
-- --   another-assoc = {!!}
