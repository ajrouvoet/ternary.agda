{-# OPTIONS --safe #-}
module Relation.Ternary.Construct.Bag.Disjoint {t} (T : Set t) where

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
  open import Relation.Ternary.Construct.Empty T public
  open import Relation.Ternary.Construct.Bag empty-rel tt as Disjoint
  open Disjoint public using (hustle) renaming
    (bags               to disjoint-split
    ;list-emptiness     to disjoint-empty
    ;bags-isPositive    to disjoint-positive
    ;bags-isCommutative to disjoint-commutative
    ;bags-isSemigroup   to disjoint-semigroup
    ;bags-isMonoid      to disjoint-monoid
    ;bags-isTotal       to disjoint-total)

  open Rel₃ Disjoint.bags using ()
    renaming (_∙_≣_ to _⊕_≣_; _✴_ to _⊕_; _─✴_ to _─⊕_) public

module _ {a} {A : Set a} (f : T → A) where

  module L = Model T
  module R = Model A

  import Relation.Ternary.Construct.List.Disjoint as LD

  map-inv : ∀ {xs ys : List A} {zs : List T} → xs R.⊕ ys ≣ map f zs →
            Σ[ frags ∈ List T × List T ]
              let xs' , ys' = frags in xs' L.⊕ ys' ≣ zs × xs ≡ map f xs' × ys ≡ map f ys'
  map-inv (R.hustle ρx ρy ρz sep) with ↭.map-inv f (↭-sym ρz)
  ... | _ , refl , ρ' with LD.map-inv _ f sep
  ... | _ , sep' , refl , refl with ↭.map-inv f ρx | ↭.map-inv f ρy
  ... | _ , refl , ρx′ | _ , refl , ρy′ = -, L.hustle ρx′ ρy′ (↭-sym ρ') sep' , refl , refl

open Model T public
