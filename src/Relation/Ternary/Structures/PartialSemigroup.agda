{-# OPTIONS --safe #-}
module Relation.Ternary.Structures.PartialSemigroup {a e} {A : Set a} (_≈_ : A → A → Set e) where

open import Level
open import Relation.Unary
open import Relation.Binary.Structures
open import Relation.Ternary.Core using (Rel₃; Respect)

open import Function using (_∘_)
open import Data.Product

record IsPartialSemigroup (rel : Rel₃ A) : Set (a ⊔ e) where
  open Rel₃ rel

  field
    overlap {{ ≈-equivalence }} : IsEquivalence _≈_

    -- the relation respects the equivalence in all positions
    {{∙-respects-≈}}  : ∀ {Φ₁ Φ₂} → Respect _≈_ (Φ₁ ∙ Φ₂)
    {{∙-respects-≈ˡ}} : ∀ {Φ₂ Φ}  → Respect _≈_ (_∙ Φ₂ ≣ Φ)
    {{∙-respects-≈ʳ}} : ∀ {Φ₁ Φ}  → Respect _≈_ (Φ₁ ∙_≣ Φ)

    ∙-assocᵣ : ∀ {a b ab c abc}
               → a ∙ b ≣ ab → ab ∙ c ≣ abc
               → ∃ λ bc → a ∙ bc ≣ abc × b ∙ c ≣ bc
    ∙-assocₗ : ∀ {a bc b c abc}
               → a ∙ bc ≣ abc → b ∙ c ≣ bc
               → ∃ λ ab → a ∙ b ≣ ab × ab ∙ c ≣ abc

  -- pairs rotate and reassociate
  module _ {p q r} {P : Pred A p} {Q : Pred A q} {R : Pred A r} where
    ⊙-assocₗ : ∀[ P ⊙ (Q ⊙ R) ⇒ (P ⊙ Q) ⊙ R ]
    ⊙-assocₗ (p ∙⟨ σ₁ ⟩ (q ∙⟨ σ₂ ⟩ r)) =
      let _ , σ₃ , σ₄ = ∙-assocₗ σ₁ σ₂ in
      (p ∙⟨ σ₃ ⟩ q) ∙⟨ σ₄ ⟩ r

    ⊙-assocᵣ : ∀[ (P ⊙ Q) ⊙ R ⇒ P ⊙ (Q ⊙ R) ]
    ⊙-assocᵣ ((p ∙⟨ σ₁ ⟩ q) ∙⟨ σ₂ ⟩ r) =
      let _ , σ₃ , σ₄ = ∙-assocᵣ σ₁ σ₂ in
      p ∙⟨ σ₃ ⟩ q ∙⟨ σ₄ ⟩ r

  module _ {p q} {P : Pred A p} {Q : Pred A q} where
    apply : ∀[ P ⊙ (P ─⊙ Q) ⇒ Q ]
    apply (px ∙⟨ sep ⟩ qx) = qx ⟨ sep ⟩ px

  -- mapping
  module _ {p q p' q'}
    {P : Pred A p} {Q : Pred A q} {P' : Pred A p'} {Q' : Pred A q'} where

    ⟨_⟨⊙⟩_⟩ : ∀[ P ⇒ P' ] → ∀[ Q ⇒ Q' ] → ∀[ P ⊙ Q ⇒ P' ⊙ Q' ]
    ⟨_⟨⊙⟩_⟩ f g (px ∙⟨ sep ⟩ qx) = f px ∙⟨ sep ⟩ g qx

  module _ {p q r} {P : Pred A p} {Q : Pred A q} {R : Pred A r} where

    com : ∀[ (P ─⊙ Q) ⊙ (Q ─⊙ R) ⇒ (P ─⊙ R) ]
    com (f ∙⟨ σ₁ ⟩ g) ⟨ σ₂ ⟩ px = let _ , σ₃ , σ₄ = ∙-assocₗ σ₂ σ₁ in g ⟨ σ₄ ⟩ (f ⟨ σ₃ ⟩ px)

  module _ where

    ≤-trans : Φ₁ ≤ Φ₂ → Φ₂ ≤ Φ₃ → Φ₁ ≤ Φ₃
    ≤-trans (τ₁ , Φ₁∙τ₁=Φ₂) (τ₂ , Φ₂∙τ₂=Φ₃) =
      let τ₃ , p , q = ∙-assocᵣ Φ₁∙τ₁=Φ₂ Φ₂∙τ₂=Φ₃ in τ₃ , p

open IsPartialSemigroup {{...}} public
