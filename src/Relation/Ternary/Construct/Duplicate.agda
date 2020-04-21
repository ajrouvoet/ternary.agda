{-# OPTIONS --safe #-}
module Relation.Ternary.Construct.Duplicate {a} (A : Set a) where

open import Function
open import Data.Product
open import Relation.Unary
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

data Dup : A → A → A → Set a where
  dup : ∀ {a} → Dup a a a

instance duplicate : Rel₃ A
duplicate = record { _∙_≣_ = Dup }

instance dup-isComm : IsCommutative duplicate
IsCommutative.∙-comm dup-isComm dup = dup

dup-isSemigroupˡ : IsPartialSemigroupˡ _≡_ duplicate
IsPartialSemigroupˡ.≈-equivalence dup-isSemigroupˡ = isEquivalence
Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ dup-isSemigroupˡ) refl = id
Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ˡ dup-isSemigroupˡ) refl = id
IsPartialSemigroupˡ.assocᵣ dup-isSemigroupˡ dup dup = -, dup , dup

instance dup-isSemigroup : IsPartialSemigroup _≡_ duplicate
dup-isSemigroup = IsPartialSemigroupˡ.semigroupˡ dup-isSemigroupˡ

instance dup-isIdempotent : IsIdempotent duplicate
IsIdempotent.∙-idem dup-isIdempotent = dup

instance dup-isIntuitive : IsIntuitionistic U duplicate
IsIntuitionistic.∙-copy dup-isIntuitive tt = dup

module _ {e} {_≈_ : A → A → Set e} {{equiv : IsEquivalence _≈_}} where
  instance dup-isFunctional : IsFunctional _≈_ duplicate
  IsFunctional.functional dup-isFunctional dup dup = IsEquivalence.reflexive equiv refl
