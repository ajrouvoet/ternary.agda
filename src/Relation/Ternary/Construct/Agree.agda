{-# OPTIONS --safe #-}
module Relation.Ternary.Construct.Agree {a} (A : Set a) where

open import Function
open import Data.Unit
open import Data.Product
open import Relation.Unary
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

data Agree : A → A → A → Set a where
  agreed : ∀ {a} → Agree a a a

instance agrees : Rel₃ A
agrees = record { _∙_≣_ = Agree }

instance agreed-isComm : IsCommutative agrees
IsCommutative.∙-comm agreed-isComm agreed = agreed

agreed-isSemigroupˡ : IsPartialSemigroupˡ _≡_ agrees
IsPartialSemigroupˡ.≈-equivalence agreed-isSemigroupˡ = isEquivalence
Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ agreed-isSemigroupˡ) refl = id
Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ˡ agreed-isSemigroupˡ) refl = id
IsPartialSemigroupˡ.assocᵣ agreed-isSemigroupˡ agreed agreed = -, agreed , agreed

instance agreed-isSemigroup : IsPartialSemigroup _≡_ agrees
agreed-isSemigroup = IsPartialSemigroupˡ.semigroupˡ agreed-isSemigroupˡ

instance agreed-isIdempotent : IsIdempotent U agrees
IsIdempotent.∙-idem agreed-isIdempotent _ = agreed

instance agreed-isIntuitive : IsIdempotent U agrees
IsIdempotent.∙-idem agreed-isIntuitive tt = agreed

module _ {e} {_≈_ : A → A → Set e} {{equiv : IsEquivalence _≈_}} where
  instance agreed-isFunctional : IsFunctional _≈_ agrees
  IsFunctional.functional agreed-isFunctional agreed agreed = IsEquivalence.reflexive equiv refl
