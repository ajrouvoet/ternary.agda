module Relation.Ternary.Separation.Monad.Update where

open import Level hiding (Lift)
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Unary
open import Relation.Unary.PredicateTransformer hiding (_⊔_; [_])
open import Relation.Ternary.Separation
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Morphisms
open Monads

open import Data.Unit
open import Data.Product

module _ {ℓ}
  {C : Set ℓ} {u}
  {{r : RawSep C}}
  {{us : IsUnitalSep r u}}
  where

  instance
    ⤇-monad : Monad ⊤ _ (λ _ _ → ⤇ {p = ℓ})
    Monad.return ⤇-monad px         = local λ σ → -, -, σ , px
    app (Monad.bind ⤇-monad f) p σₚ = local λ fr →
      let
        _ , σ₁ , σ₂     = ⊎-assoc (⊎-comm σₚ) fr
        Δ , Σ , σ₃ , px = update p σ₁
        _ , σ₄ , σ₅     = ⊎-unassoc σ₃ σ₂
      in update (app f px (⊎-comm σ₄)) σ₅
