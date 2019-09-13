module Relation.Unary.Separation.Morphisms where

open import Level
open import Relation.Unary
open import Relation.Unary.Separation
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Function using (_∘_)

record Morphism {a b} {A : Set a} {{r : RawSep A}} {u} (s₁ : IsUnitalSep r u) (s₂ : Separation b) : Set (a ⊔ suc b) where
  open Separation s₂ using () renaming (Carrier to B)

  field
    j      : A → B
    j-map  : ∀ {Φ₁ Φ₂ Φ} → Φ₁ ⊎ Φ₂ ≣ Φ → j Φ₁ ⊎ j Φ₂ ≣ j Φ
    j-⊎    : ∀ {Φ₁ Φ₂ Φ} → j Φ₁ ⊎ j Φ₂ ≣ Φ → ∃ λ Φ' → Φ ≡ j Φ'
    j-map⁻ : ∀ {Φ₁ Φ₂ Φ} → j Φ₁ ⊎ j Φ₂ ≣ j Φ → Φ₁ ⊎ Φ₂ ≣ Φ

    overlap {{j-unital}} : IsUnitalSep (Separation.raw s₂) (j u) 

  {- Such a morphism on SAs induces a functor on SA-predicates -}
  module _ where

    data J {p} (P : Pred A p) : Pred B (a ⊔ p) where
      inj : ∀ {Φ} → P Φ → J P (j Φ)

    jstar : ∀ {p q} {P : Pred A p} {Q : Pred A q} → ∀[ J (P ✴ Q) ⇒ J P ✴ J Q ]
    jstar (inj (p ×⟨ σ ⟩ q)) = inj p ×⟨ j-map σ ⟩ inj q

    jstar⁻ : ∀ {p q} {P : Pred A p} {Q : Pred A q} → ∀[ J P ✴ J Q ⇒ J (P ✴ Q) ]
    jstar⁻ (inj px ×⟨ σ ⟩ inj qx) with j-⊎ σ
    ... | _ , refl = inj (px ×⟨ j-map⁻ σ ⟩ qx)

  {- relative morphisms -}
  _⇒ⱼ_ : ∀ {p q} → Pred A p → Pred B q → Pred A _ 
  P ⇒ⱼ Q = P ⇒ (Q ∘ j)

  {- relative exponents -}
  _─✴ⱼ_ : ∀ {p q} → Pred A p → Pred B q → Pred A _ 
  P ─✴ⱼ Q = P ─✴ (Q ∘ j)