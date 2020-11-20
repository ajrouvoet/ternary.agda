{-# OPTIONS --safe #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Data.Bigstar
  {a} {A : Set a}
  {{ r : Rel₃ A }}
  {e u} {_≈_ : A → A → Set e} {{ _ : IsPartialMonoid _≈_ r u }} {{_ : IsUnique _≈_ u}} where

open import Level
open import Data.Bool
open import Data.Product
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Structures.Syntax

infixr 10 cons
data Bigstar {p} (P : Pred A p) : Pred A (a ⊔ p) where
  emp  : ε[ Bigstar P ]
  cons : ∀[ P ✴ Bigstar P ⇒ Bigstar P ]

instance bigstar-respects : ∀ {p} {P : Pred A p} → Respect _≈_ (Bigstar P)
Respect.coe bigstar-respects eq emp with unique eq
... | refl = emp
Respect.coe bigstar-respects eq (cons x) = cons (coe eq x)

pattern _✴⟨_⟩_ px σ qx = cons (px ∙⟨ σ ⟩ qx)

module _ where
  [_] : ∀ {p} {P : Pred A p} → ∀[ P ⇒ Bigstar P ]
  [ px ] = cons (px ∙⟨ ∙-idʳ ⟩ emp)

module _ {p q} {P : Pred A p} {Q : Pred A q} where

  ⊛-map : ∀[ P ⇒ Q ] → ∀[ Bigstar P ⇒ Bigstar Q ]
  ⊛-map f emp = emp
  ⊛-map f (px ✴⟨ σ ⟩ pxs) = f px ✴⟨ σ ⟩ ⊛-map f pxs

module _ {{ _ : IsCommutative r }} where
  append : ∀ {p} {P : Pred A p} → ∀[ P ⇒ Bigstar P ─✴ Bigstar P ]
  append px ⟨ σ ⟩ emp = coe (∙-id⁻ʳ σ) [ px ]
  append px ⟨ σ ⟩ cons (qx ∙⟨ σ₁ ⟩ pxs) =
    let _ , σ₂ , σ₃ = ∙-rotateₗ σ σ₁
        qxs = append px ⟨ ∙-comm σ₃ ⟩ pxs
    in cons (qx ∙⟨ σ₂ ⟩ qxs)

  concat : ∀ {p} {P : Pred A p} → ∀[ Bigstar P ⇒ Bigstar P ─✴ Bigstar P ]
  concat emp ⟨ σ ⟩ ys = coe (∙-id⁻ˡ σ ) ys
  concat (cons (x ∙⟨ σ₁ ⟩ xs)) ⟨ σ ⟩ ys with ∙-assocᵣ σ₁ σ
  ... | _ , σ₂ , σ₃ = cons (x ∙⟨ σ₂ ⟩ (concat xs ⟨ σ₃ ⟩ ys))

module _ where
  open import Data.Unit
  open import Relation.Ternary.Monad
  open import Relation.Ternary.Monad.Error

  head : ∀ {P : Pred A a} → ∀[ Bigstar P ⇒ Error (P ✴ Bigstar P) ]
  head emp                = error
  head (px ✴⟨ σ ⟩ pxs) = return (px ∙⟨ σ ⟩ pxs)
  
  module _ {{_ : IsCommutative r}} where

    last⁺ : ∀ {P : Pred A a} → ∀[ P ⇒ Bigstar P ─✴ (P ✴ Bigstar P) ]
    last⁺ last? ⟨ σ ⟩ emp                = last? ∙⟨ σ ⟩ emp 
    last⁺ last? ⟨ σ₁ ⟩ (px ✴⟨ σ₂ ⟩ tail) = 
      let (last! ∙⟨ σ₃ ⟩ rest) = ✴-rotateᵣ (last? ∙⟨ σ₁ ⟩ (✴-swap (last⁺ px ⟨ σ₂ ⟩ tail)))
      in last! ∙⟨ σ₃ ⟩ cons rest

    last : ∀ {P : Pred A a} → ∀[ Bigstar P ⇒ Error (P ✴ Bigstar P) ]
    last emp = error
    last (px ✴⟨ σ ⟩ pxs) = return (last⁺ px ⟨ σ ⟩ pxs) 
    
    find : ∀ {P : Pred A a} (f : ∀ {Φ} → P Φ → Bool) → ∀[ Bigstar P ⇒ Error (P ✴ Bigstar P) ]
    find f emp = raise _
    find {P} f (px ✴⟨ σ ⟩ pxs) =
      if f px
        then return (px ∙⟨ σ ⟩ pxs)
        else do
          result ∙⟨ σ₁ ⟩ tail✴head ← ✴-rotateₗ ⟨$⟩ (str {Q = P} px ⟨ σ ⟩ find f pxs)
          return (result ∙⟨ σ₁ ⟩ cons (✴-swap tail✴head) )
