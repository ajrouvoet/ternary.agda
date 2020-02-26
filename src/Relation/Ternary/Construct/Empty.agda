{- The trivially empty resource -}
module Relation.Ternary.Construct.Empty {a} (A : Set a )where

open import Data.Empty.Polymorphic
open import Data.Product

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P

open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Respect.Propositional

instance empty-rel : Rel₃ A
Rel₃._∙_≣_ empty-rel = λ _ _ _ → ⊥

instance empty-semigroup : IsPartialSemigroup _≡_ empty-rel
IsPartialSemigroup.≈-equivalence empty-semigroup = isEquivalence
IsPartialSemigroup.∙-assocᵣ empty-semigroup ()
IsPartialSemigroup.∙-assocₗ empty-semigroup ()

instance empty-commutative : IsCommutative empty-rel
IsCommutative.∙-comm empty-commutative ()

