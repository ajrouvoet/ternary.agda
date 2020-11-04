{-# OPTIONS --safe #-}
module Relation.Ternary.Construct.Bag.Overlapping {t} (T : Set t) where

open import Level
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (swap; map)
open import Data.List
open import Data.List.Relation.Binary.Permutation.Propositional
import Data.List.Relation.Binary.Permutation.Propositional.Properties as ↭

open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

private
  Ctx = List T
  variable
    xsˡ xsʳ xs ysˡ ysʳ ys zs : Ctx

module Model {t} (T : Set t) where
  open import Relation.Ternary.Construct.Duplicate T public
  open import Relation.Ternary.Construct.Bag duplicate tt as Overlapping
  open Overlapping public using (hustle) renaming
    (bags               to overlap-split
    ;bag-emptiness      to overlap-empty
    ;bags-isPositive    to overlap-positive
    ;bags-isCommutative to overlap-commutative
    ;bags-isSemigroup   to overlap-semigroup
    ;bags-isMonoid      to overlap-monoid
    ;bags-isTotal       to overlap-total)

  open Rel₃ Overlapping.bags using ()
    renaming (_∙_≣_ to _⊗_≣_; _✴_ to _⊗_; _─✴_ to _─⊗_) public

-- module _ {a} {A : Set a} (f : T → A) where

--   module L = Model T
--   module R = Model A

--   import Relation.Ternary.Construct.List.Overlapping as LO

--   map-inv : ∀ {xs ys : List A} {zs : List T} → xs R.⊗ ys ≣ map f zs →
--             Σ[ frags ∈ List T × List T ]
--               let xs' , ys' = frags in xs' L.⊗ ys' ≣ zs × xs ≡ map f xs' × ys ≡ map f ys'
--   map-inv (R.hustle ρx ρy ρz sep) with ↭.↭-map-inv f (↭-sym ρz)
--   ... | _ , refl , ρ' with LO.map-inv _ f sep
--   ... | _ , sep' , refl , refl with ↭.↭-map-inv f ρx | ↭.↭-map-inv f ρy
--   ... | _ , refl , ρx′ | _ , refl , ρy′ = -, L.hustle ρx′ ρy′ (↭-sym ρ') sep' , refl , refl

open Model T public
