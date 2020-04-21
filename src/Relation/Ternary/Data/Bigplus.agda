{-# OPTIONS --safe #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Terary.Data.Bigplus
  {a} {A : Set a} 
  {{ r : Rel₃ A }}
  {e u} {_≈_ : A → A → Set e} {{ _ : IsPartialMonoid _≈_ r u }} where

open import Level
open import Data.Bool
open import Data.Product
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Structures.Syntax
import Relation.Ternary.Data.Bigstar as Star
  
Bigplus : ∀ {p} → PT A A p _
Bigplus P = P ✴ Star.Bigstar P

module Plus {p} {P : Pred A p} where
  
  [_] : ∀[ P ⇒ Bigplus P ]
  [ px ] = px ∙⟨ ∙-idʳ ⟩ Star.emp

  module _ {q} {Q : Pred A q} where

    ⊕-map : ∀[ P ⇒ Q ] → ∀[ Bigplus P ⇒ Bigplus Q ]
    ⊕-map f (px ∙⟨ σ ⟩ pxs) = f px ∙⟨ σ ⟩ Star.⊛-map f pxs

  module _ {{ _ : IsCommutative r }} where
    append : ∀[ P ⇒ Bigplus P ─✴ Bigplus P ]
    append qx ⟨ σ₁ ⟩ (px ∙⟨ σ₂ ⟩ pxs) with _ , σ₃ , σ₄ ← ∙-assocₗ σ₁ (∙-comm σ₂) =
      px ∙⟨ ∙-comm σ₄ ⟩ (Star.append qx ⟨ σ₃ ⟩ pxs)

    concat : ∀[ Bigplus P ⇒ Bigplus P ─✴ Bigplus P ]
    concat (px ∙⟨ σ₁ ⟩ pxs) ⟨ σ₂ ⟩ qxs with _ , σ₃ , σ₄ ← ∙-assocᵣ σ₁ σ₂ =
      px ∙⟨ σ₃ ⟩ (Star.concat pxs ⟨ σ₄ ⟩ (Star.cons qxs))
