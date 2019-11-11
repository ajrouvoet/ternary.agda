{-# OPTIONS --safe #-}
open import Relation.Ternary.Separation

module Relation.Ternary.Separation.Decoration
  {ℓₐ} {A : Set ℓₐ}
  {{raw : RawSep A}}
  {u : A} {{_ : HasUnit⁺ raw u}}
  where

open import Level
open import Function
open import Algebra.Core

open import Data.Product

open import Relation.Unary
open import Relation.Binary.PropositionalEquality

private
  variable
    a₁ a₂ a : A

-- Splittable decorations
record Decoration {d} (D : Pred A d) : Set (ℓₐ ⊔ d) where
  field
    decorˡ  : a₁ ⊎ a₂ ≣ a → D a → D a₁
    decor-ε : D ε

  DT : A → Set _
  DT a = D a → D a

  decorʳ  : a₁ ⊎ a₂ ≣ a → D a → D a₂
  decorʳ σ = decorˡ (⊎-comm σ)

  {- decorated carriers give rise to a separation algebra -}
  module _ where
    Decorated = ∃ D

    ann-⊎ : Decorated → Decorated → Decorated → Set (ℓₐ ⊔ d)
    ann-⊎ (a₁ , _) (a₂ , _) (a , _) = Lift d (a₁ ⊎ a₂ ≣ a)

    instance
      ann-raw : RawSep Decorated
      RawSep._⊎_≣_ ann-raw = ann-⊎

      ann-is-sep : IsSep ann-raw
      IsSep.⊎-comm ann-is-sep (lift σ) = lift (⊎-comm σ)
      IsSep.⊎-assoc ann-is-sep {abc = abc} (lift σ₁) (lift σ₂) =
        let a , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂
        in (a , decorˡ (⊎-comm σ₃) (proj₂ abc)) , lift σ₃ , lift σ₄

      ann-has-unit⁺ : HasUnit⁺ ann-raw (ε , decor-ε)
      HasUnit⁺.⊎-idˡ ann-has-unit⁺ = lift ⊎-idˡ

open Decoration {{...}} public hiding (Decorated; DT)
open Decoration public using (Decorated; DT)
