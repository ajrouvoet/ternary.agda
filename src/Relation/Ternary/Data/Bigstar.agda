{-# OPTIONS --safe #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Data.Bigstar 
  {a} {A : Set a} 
  {{ r : Rel₃ A }}
  {e u} {_≈_ : A → A → Set e} {{ _ : IsPartialMonoid _≈_ r u }} where

open import Level
open import Data.Bool
open import Data.Product
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Structures.Syntax

infixr 10 cons
data Bigstar {p} (P : Pred A p) : Pred A (a ⊔ p) where
  emp  : ε[ Bigstar P ]
  cons : ∀[ P ⊙ Bigstar P ⇒ Bigstar P ]

instance bigstar-respects : ∀ {p} {P : Pred A p} → Respect _≈_ (Bigstar P)
Respect.coe bigstar-respects eq emp with ε-unique eq
... | refl = emp
Respect.coe bigstar-respects eq (cons x) = cons (coe eq x)

pattern _✴⟨_⟩_ px σ qx = cons (px ∙⟨ σ ⟩ qx)

[_] : ∀ {p} {P : Pred A p} → ∀[ P ⇒ Bigstar P ]
[ px ] = cons (px ∙⟨ ∙-idʳ ⟩ emp)

module _ {{ _ : IsCommutative r }} where
  append : ∀ {p} {P : Pred A p} → ∀[ P ⇒ Bigstar P ─⊙ Bigstar P ]
  append px ⟨ σ ⟩ emp = coe (∙-id⁻ʳ σ) [ px ]
  append px ⟨ σ ⟩ cons (qx ∙⟨ σ₁ ⟩ pxs) =
    let _ , σ₂ , σ₃ = ∙-rotateₗ σ σ₁
        qxs = append px ⟨ ∙-comm σ₃ ⟩ pxs
    in cons (qx ∙⟨ σ₂ ⟩ qxs)

  concat : ∀ {p} {P : Pred A p} → ∀[ Bigstar P ⇒ Bigstar P ─⊙ Bigstar P ]
  concat emp ⟨ σ ⟩ ys = coe (∙-id⁻ˡ σ ) ys
  concat (cons (x ∙⟨ σ₁ ⟩ xs)) ⟨ σ ⟩ ys with ∙-assocᵣ σ₁ σ
  ... | _ , σ₂ , σ₃ = cons (x ∙⟨ σ₂ ⟩ (concat xs ⟨ σ₃ ⟩ ys)) 

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
