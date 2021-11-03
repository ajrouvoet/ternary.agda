open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as ≡ using (refl; _≢_; _≡_; subst)

module Relation.Ternary.Construct.Map.Properties 
  {k v}
  (K : Set k)
  (V : K → Set v)
  (_≡ₖ?_ : Decidable (_≡_ {A = K}))
  where

open import Level
open import Function
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (swap)
open import Data.Maybe

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Morphisms
open import Relation.Ternary.Construct.Add.Unit.Properties

module CrossSplittable {{div₁ : ∀ {k} → Rel₃ (V k)}} {{div₂ : ∀ {k} → Rel₃ (V k)}} where

  open import Relation.Ternary.Construct.Map K V _≡ₖ?_ as M

  xsplit : (∀ {k} → CrossSplit (div₁ {k}) div₂) → CrossSplit (maps div₁) (maps div₂)
  xsplit xsplitₐ {a} {b} {c} {d} (union σs₁) (union σs₂) =
    let xsp = λ {k} → maybe-cross (xsplitₐ {k}) in
    -, union (λ k → let _ , τ , _ = xsp (σs₁ k) (σs₂ k) in τ)
     , union (λ k → let _ , _ , τ , _ = xsp (σs₁ k) (σs₂ k) in τ)
     , union (λ k → let _ , _ , _ , τ , _ = xsp (σs₁ k) (σs₂ k) in τ)
     , union (λ k → let _ , _ , _ , _ , τ = xsp (σs₁ k) (σs₂ k) in τ)

  -- Maps don't have uncross

