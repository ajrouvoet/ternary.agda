{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Structures.Commutative {a} {A : Set a} where

open import Level
open import Relation.Unary
open import Relation.Binary.Structures

open import Function using (_∘_)
open import Data.Product

open import Relation.Ternary.Core using (Rel₃; Respect; coe; Exactly; Commutative)
open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid

record IsCommutative (rel : Rel₃ A) : Set (a) where
  field
    ∙-comm : Commutative rel

  module WithSemigroup {e} {_≈_ : A → A → Set e} (semigroup   : IsPartialSemigroup _≈_ rel) where

    open Rel₃ rel
    open IsPartialSemigroup semigroup

    module _ where

      resplit : ∀ {a b c d ab cd abcd} →
                a ∙ b ≣ ab → c ∙ d ≣ cd → ab ∙ cd ≣ abcd →
                ∃₂ λ ac bd → a ∙ c ≣ ac × b ∙ d ≣ bd × ac ∙ bd ≣ abcd
      resplit σ₁ σ₂ σ     with ∙-assocᵣ σ₁ σ
      ... | bcd , σ₃ , σ₄ with ∙-assocₗ σ₄ (∙-comm σ₂)
      ... | bd  , σ₅ , σ₆ with ∙-assocₗ σ₃ σ₆
      ... | abd , σ₇ , σ₈ with ∙-assocₗ (∙-comm σ₈) σ₇
      ... | ac  , τ  , τ' = -, -, ∙-comm τ , σ₅ , τ'

    -- pairs commute
    module _ {p q} {P : Pred A p} {Q : Pred A q} where
      ⊙-swap : ∀[ (P ⊙ Q) ⇒ (Q ⊙ P) ]
      ⊙-swap (px ∙⟨ σ ⟩ qx) = qx ∙⟨ ∙-comm σ ⟩ px

    module _ {p q p' q'}
      {P : Pred A p} {Q : Pred A q} {P' : Pred A p'} {Q' : Pred A q'} where

      both : ∀[ (P ─⊙ P') ⊙ (Q ─⊙ Q') ⇒ P ⊙ Q ─⊙ P' ⊙ Q' ]
      both (f ∙⟨ σ₁ ⟩ g) ⟨ σ₃ ⟩ (px ∙⟨ σ₂ ⟩ qx) with resplit σ₁ σ₂ σ₃
      ... | _ , _ , σ₄ , σ₅ , σ₆ = (f ⟨ σ₄ ⟩ px) ∙⟨ σ₆ ⟩ (g ⟨ σ₅ ⟩ qx)

    module _ {a b c bc abc} where
      ∙-rotateₗ : a ∙ bc ≣ abc → b ∙ c ≣ bc → ∃ λ ca → b ∙ ca ≣ abc × c ∙ a ≣ ca
      ∙-rotateₗ σ₁ σ₂ with ∙-assocᵣ σ₂ (∙-comm σ₁)
      ... | _ , σ₃ , σ₄ = -, σ₃ , σ₄

      ∙-rotateᵣ : a ∙ bc ≣ abc → b ∙ c ≣ bc → ∃ λ ab → c ∙ ab ≣ abc × a ∙ b ≣ ab
      ∙-rotateᵣ σ₁ σ₂ with ∙-assocₗ σ₁ σ₂
      ... | _ , σ₃ , σ₄ = -, ∙-comm σ₄ , σ₃

    -- pairs rotate and reassociate
    module _ {p q r} {P : Pred A p} {Q : Pred A q} {R : Pred A r} where
      ⊙-rotateᵣ : ∀[ P ⊙ Q ⊙ R ⇒ R ⊙ P ⊙ Q ]
      ⊙-rotateᵣ (p ∙⟨ σ₁ ⟩ (q ∙⟨ σ₂ ⟩ r)) =
        let _ , σ₃ , σ₄ = ∙-rotateᵣ σ₁ σ₂ in
        r ∙⟨ σ₃ ⟩ p ∙⟨ σ₄ ⟩ q

      ⊙-rotateₗ : ∀[ P ⊙ (Q ⊙ R) ⇒ Q ⊙ R ⊙ P ]
      ⊙-rotateₗ (p ∙⟨ σ₁ ⟩ (q ∙⟨ σ₂ ⟩ r)) =
        let _ , σ₃ , σ₄ = ∙-rotateₗ σ₁ σ₂ in
        q ∙⟨ σ₃ ⟩ r ∙⟨ σ₄ ⟩ p
