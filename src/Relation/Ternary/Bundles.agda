module Relation.Ternary.Bundles where

open import Level
open import Relation.Binary.Bundles
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.PartialJoinoid

record Joinoid a e : Set (suc (a ⊔ e)) where
  field
    setoid : Setoid a e

  open Setoid setoid public using (_≈_; Carrier)

  field
    {▹-rel ∥-rel ∣-rel} : Rel₃ Carrier
    {unit}             : Carrier
    isJoinoid          : IsJoinoid _≈_ ▹-rel ∥-rel ∣-rel unit

  open IsJoinoid isJoinoid public
