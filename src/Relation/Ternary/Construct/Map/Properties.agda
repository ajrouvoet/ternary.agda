module Relation.Ternary.Construct.Map.Properties where

open import Level
open import Function
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (swap)
open import Data.Maybe

open import Relation.Nullary
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Morphisms
open import Relation.Ternary.Construct.Add.Unit.Properties

module CrossSplittable {k v} {K : Set k} {V : K → Set v}
  {{div₁ : ∀ {k} → Rel₃ (V k)}} {{div₂ : ∀ {k} → Rel₃ (V k)}}
  {e} {_≈₁_ : ∀ {k} → V k → V k → Set e} {_≈₂_ : ∀ {k} → V k → V k → Set e}
  {{_ : ∀ {k} → IsCommutative (div₁ {k})}} {{_ : ∀ {k} → IsPartialSemigroup _≈₁_ (div₁ {k})}}
  {{_ : ∀ {k} → IsCommutative (div₂ {k})}} {{_ : ∀ {k} → IsPartialSemigroup _≈₂_ (div₂ {k})}}
  where

  module _ {k} where
    open Rel₃ (div₁ {k}) using () renaming (_∙_≣_ to _∙ₐ₁_≣_)
    open Rel₃ (div₂ {k}) using () renaming (_∙_≣_ to _∙ₐ₂_≣_)

    open import Relation.Ternary.Construct.Map K V as L
    open import Relation.Ternary.Construct.Map K V as R

    xsplit : (∀ {k} → CrossSplit (div₁ {k}) div₂) → CrossSplit (L.maps div₁) (R.maps div₂)
    xsplit xsplitₐ {a} {b} {c} {d} (union σs₁) (union σs₂) = 
      let xsp = λ {k} → maybe-cross (xsplitₐ {k}) in
      -, R.union (λ k → let _ , τ , _ = xsp (σs₁ k) (σs₂ k) in τ)
       , R.union (λ k → let _ , _ , τ , _ = xsp (σs₁ k) (σs₂ k) in τ)
       , R.union (λ k → let _ , _ , _ , τ , _ = xsp (σs₁ k) (σs₂ k) in τ)
       , R.union (λ k → let _ , _ , _ , _ , τ = xsp (σs₁ k) (σs₂ k) in τ)

    -- Maps don't have uncross

