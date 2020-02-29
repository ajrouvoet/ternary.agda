module Relation.Ternary.Data.Bigstar where

open import Level
open import Data.Bool
open import Data.Product
open import Relation.Unary
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module _
  {a p} {A : Set a} 
  {{ r : Rel₃ A }}
  {e u} {_≈_ : A → A → Set e} {{ _ : IsPartialMonoid _≈_ r u }} where

  data Bigstar (P : Pred A p) : Pred A (a ⊔ p) where
    emp  : ε[ Bigstar P ]
    cons : ∀[ P ⊙ Bigstar P ⇒ Bigstar P ]

  postulate instance bigstar-respects : ∀ {P} → Respect _≈_ (Bigstar P)

  [_] : ∀ {P} → ∀[ P ⇒ Bigstar P ]
  [ px ] = cons (px ∙⟨ ∙-idʳ ⟩ emp)

  module _ {{ _ : IsCommutative r }} where
    append : ∀ {P} → ∀[ P ⇒ Bigstar P ─⊙ Bigstar P ]
    append px ⟨ σ ⟩ emp = coe (∙-id⁻ʳ σ) [ px ]
    append px ⟨ σ ⟩ cons (qx ∙⟨ σ₁ ⟩ pxs) =
      let _ , σ₂ , σ₃ = ∙-rotateₗ σ σ₁
          qxs = append px ⟨ ∙-comm σ₃ ⟩ pxs
      in cons (qx ∙⟨ σ₂ ⟩ qxs)

  -- open import Relation.Ternary.Separation.Monad.Error
  -- open import Relation.Ternary.Separation.Morphisms
  -- open Monads

  -- head : ∀ {P} → ∀[ Bigstar P ⇒ Error (P ✴ Bigstar P) ]
  -- head emp = error err
  -- head pool@(cons (px ×⟨ σ ⟩ pxs)) = do
  --   th₂ ×⟨ σ ⟩ pool' ×⟨ σ₂ ⟩ th₁ ← mapM (head pxs &⟨ ⊎-comm σ ⟩ px) ✴-assocᵣ
  --   return (th₂ ×⟨ σ ⟩ cons (th₁ ×⟨ ⊎-comm σ₂ ⟩ pool'))

  -- find : (∀ {Φ} → P Φ → Bool) → ∀[ Bigstar P ⇒ Error (P ✴ Bigstar P) ]
  -- find f emp = error err
  -- find f (cons (px ×⟨ σ ⟩ pxs)) =
  --   if f px
  --     then return (px ×⟨ σ ⟩ pxs)
  --     else do
  --       px' ×⟨ σ₁ ⟩ pxs' ×⟨ σ₂ ⟩ px ← mapM (find f pxs &⟨ P ∥ ⊎-comm σ ⟩ px) ✴-assocᵣ
  --       return (px' ×⟨ σ₁ ⟩ cons (px ×⟨ ⊎-comm σ₂ ⟩ pxs')) 
