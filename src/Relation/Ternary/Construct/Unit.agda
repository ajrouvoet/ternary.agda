{- The trivial resource -}
module Relation.Ternary.Construct.Unit where

open import Data.Unit
open import Data.Product

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P

open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Respect.Propositional

instance unit-rel : Rel₃ ⊤
Rel₃._∙_≣_ unit-rel = λ _ _ _ → ⊤

instance unit-semigroup : IsPartialSemigroup _≡_ unit-rel
IsPartialSemigroup.≈-equivalence unit-semigroup = isEquivalence
IsPartialSemigroup.∙-assocᵣ unit-semigroup _ _ = -, tt , tt
IsPartialSemigroup.∙-assocₗ unit-semigroup _ _ = -, tt , tt

instance unit-commutative : IsCommutative unit-rel
IsCommutative.∙-comm unit-commutative _ = tt

