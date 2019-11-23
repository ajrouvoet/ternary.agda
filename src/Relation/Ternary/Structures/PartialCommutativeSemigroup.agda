{-# OPTIONS --safe #-}
module Relation.Ternary.Structures.PartialCommutativeSemigroup
  {a e} {A : Set a} (_≈_ : A → A → Set e) where

open import Level
open import Relation.Unary
open import Relation.Binary.Structures

open import Function using (_∘_)
open import Data.Product

open import Relation.Ternary.Core using (Rel₃; Respect; coe)
open import Relation.Ternary.Structures.PartialSemigroup _≈_

Commutative : Rel₃ A → Set a
Commutative rel = let open Rel₃ rel in ∀ {a b ab} → a ∙ b ≣ ab → b ∙ a ≣ ab

record IsPartialCommutativeSemigroup (rel : Rel₃ A) : Set (a ⊔ e) where
  open Rel₃ rel

  field
    overlap {{isPSG}} : IsPartialSemigroup rel
    ∙-comm            : Commutative rel
     
  module _ where
    resplit : ∀ {a b c d ab cd abcd} →
              a ∙ b ≣ ab → c ∙ d ≣ cd → ab ∙ cd ≣ abcd →
              ∃₂ λ ac bd → a ∙ c ≣ ac × b ∙ d ≣ bd × ac ∙ bd ≣ abcd
    resplit σ₁ σ₂ σ     with ∙-assocᵣ σ₁ σ
    ... | bcd , σ₃ , σ₄ with ∙-assocₗ σ₄ (∙-comm σ₂)
    ... | bd  , σ₅ , σ₆ with ∙-assocₗ σ₃ σ₆
    ... | abd , σ₇ , σ₈ with ∙-assocₗ (∙-comm σ₈) σ₇
    ... | ac  , τ  , τ' = -, -, ∙-comm τ , σ₅ , τ'

    recombine : ∀ {a b ab c abc} →
      a ∙ b ≣ ab → ab ∙ c ≣ abc →
      ∃ λ ac → a ∙ c ≣ ac × ac ∙ b ≣ abc
    recombine σ₁ σ₂ with ∙-assocᵣ σ₁ σ₂
    ... | _ , σ₃ , σ₄ = ∙-assocₗ σ₃ (∙-comm σ₄) 

  -- pairs commute
  module _ {p q} {P : Pred A p} {Q : Pred A q} where
    ⊙-swap : ∀[ (P ⊙ Q) ⇒ (Q ⊙ P) ]
    ⊙-swap (px ∙⟨ σ ⟩ qx) = qx ∙⟨ ∙-comm σ ⟩ px

  module _ {p q p' q'}
    {P : Pred A p} {Q : Pred A q} {P' : Pred A p'} {Q' : Pred A q'} where

    both : ∀[ (P ─⊙ P') ⊙ (Q ─⊙ Q') ⇒ P ⊙ Q ─⊙ P' ⊙ Q' ]
    both (f ∙⟨ σ₁ ⟩ g) ⟨ σ₃ ⟩ (px ∙⟨ σ₂ ⟩ qx) with resplit σ₁ σ₂ (∙-comm σ₃)
    ... | _ , _ , σ₄ , σ₅ , σ₆ = (f ⟨ ∙-comm σ₄ ⟩ px) ∙⟨ σ₆ ⟩ (g ⟨ ∙-comm σ₅ ⟩ qx)

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

  module _ {p q r} {P : Pred A p} {Q : Pred A q} {R : Pred A r} where

    ⊙-curry : ∀[ (P ─⊙ (Q ─⊙ R)) ⇒ (P ⊙ Q) ─⊙ R ]
    ⊙-curry f ⟨ σ₂ ⟩ (p ∙⟨ σ₁ ⟩ q) =
      let _ , σ₃ , σ₄ = ∙-rotateₗ (∙-comm σ₂) (∙-comm σ₁) in (f ⟨ σ₄ ⟩ p) ⟨ σ₃ ⟩ q

    intro : ∀[ (P ⊙ Q) ⇒ R ] → ∀[ P ⇒ (Q ─⊙ R) ]
    intro f px ⟨ s ⟩ qx = f (px ∙⟨ ∙-comm s ⟩ qx)

    ⊙-uncurry : ∀[ (P ⊙ Q ─⊙ R) ⇒ P ─⊙ (Q ─⊙ R) ]
    ⊙-uncurry f ⟨ σ₁ ⟩ p ⟨ σ₂ ⟩ q =
      let _ , σ₃ , σ₄ = ∙-rotateₗ σ₂ (∙-comm σ₁) in f ⟨ ∙-comm σ₃ ⟩ (p ∙⟨ σ₄ ⟩ q)

{- Smart constructor; exploiting comm to default some fields -}
pcsg : ∀ {rel : Rel₃ A} →
       let open Rel₃ rel in
       {{≈-equivalence  : IsEquivalence _≈_}}
       {{∙-respects-≈   : ∀ {Φ₁ Φ₂} → Respect _≈_ (Φ₁ ∙ Φ₂)}}
       {{∙-respects-≈ˡ  : ∀ {Φ₂ Φ} → Respect _≈_ (_∙ Φ₂ ≣ Φ)}}
       (∙-assocᵣ′      : ∀ {a b ab c abc} → a ∙ b ≣ ab → ab ∙ c ≣ abc
                       → ∃ λ bc → a ∙ bc ≣ abc × b ∙ c ≣ bc)
       (∙-comm         : ∀ {a b ab} → a ∙ b ≣ ab → b ∙ a ≣ ab)
  → IsPartialCommutativeSemigroup rel
IsPartialCommutativeSemigroup.isPSG (pcsg ∙-assocᵣ ∙-comm)
  = record
      { ∙-respects-≈ʳ = record { coe = λ eq → ∙-comm ∘ coe eq ∘ ∙-comm }
      ; ∙-assocᵣ = ∙-assocᵣ
      ; ∙-assocₗ = λ σ₁ σ₂ →
        let _ , σ₃ , σ₄ = ∙-assocᵣ (∙-comm σ₂) (∙-comm σ₁)
        in -, ∙-comm σ₄ , ∙-comm σ₃
      }
IsPartialCommutativeSemigroup.∙-comm (pcsg ∙-assocᵣ′ ∙-comm) = ∙-comm

open IsPartialCommutativeSemigroup {{...}} public
