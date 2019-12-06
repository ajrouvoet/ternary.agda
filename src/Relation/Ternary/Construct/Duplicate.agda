module Relation.Ternary.Construct.Duplicate {a} (A : Set a) where

open import Function
open import Data.Product
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

data Dup : A → A → A → Set a where
  dup : ∀ {a} → Dup a a a

instance duplicate : Rel₃ A
duplicate = record { _∙_≣_ = Dup }

instance dup-is-comm : IsCommutative duplicate
IsCommutative.∙-comm dup-is-comm dup = dup

dup-is-semigroupˡ : IsPartialSemigroupˡ _≡_ duplicate
IsPartialSemigroupˡ.≈-equivalence dup-is-semigroupˡ = isEquivalence
Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ dup-is-semigroupˡ) refl = id
Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ˡ dup-is-semigroupˡ) refl = id
IsPartialSemigroupˡ.assocᵣ dup-is-semigroupˡ dup dup = -, dup , dup

instance dup-is-semigroup : IsPartialSemigroup _≡_ duplicate
dup-is-semigroup = IsPartialSemigroupˡ.semigroupˡ dup-is-semigroupˡ
