module Relation.Ternary.Separation.Construct.Duplicate {a} (A : Set a) where

open import Function
open import Data.Product
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Separation

data Dup : A → A → A → Set a where
  dup : ∀ {a} → Dup a a a

instance
  dup-sep : RawSep A
  dup-sep = record { _⊎_≣_ = Dup }

  dup-is-sep : IsSep _≡_ dup-sep
  IsSep.≈-equivalence dup-is-sep = isEquivalence
  IsSep.⊎-respects-≈ dup-is-sep refl = id
  IsSep.⊎-respects-≈ˡ dup-is-sep refl = id
  IsSep.⊎-comm dup-is-sep dup = dup
  IsSep.⊎-assoc dup-is-sep dup dup = -, dup , dup

-- decorations are trivial
-- module _ {p} (P : Pred A p) where
--   open import Relation.Ternary.Separation.Decoration
--   open Decoration 

--   dup-decor : Decoration P
--   decorˡ dup-decor dup = id
