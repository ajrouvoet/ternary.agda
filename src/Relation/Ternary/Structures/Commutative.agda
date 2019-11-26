{-# OPTIONS --safe #-}
module Relation.Ternary.Structures.Commutative
  {a e} {A : Set a} (_≈_ : A → A → Set e) where

open import Level
open import Relation.Unary
open import Relation.Binary.Structures

open import Function using (_∘_)
open import Data.Product

open import Relation.Ternary.Core using (Rel₃; Respect; coe; Exactly)
open import Relation.Ternary.Structures.PartialSemigroup _≈_
open import Relation.Ternary.Structures.PartialMonoid _≈_

Commutative : Rel₃ A → Set a
Commutative rel = let open Rel₃ rel in ∀ {a b ab} → a ∙ b ≣ ab → b ∙ a ≣ ab

record IsCommutative (rel : Rel₃ A) : Set (a ⊔ e) where
  open Rel₃ rel

  field
    ∙-comm            : Commutative rel

open IsCommutative {{...}} public
     
module _
  {rel : Rel₃ A}
  {{_ : IsPartialSemigroup rel}}
  {{_ : IsCommutative rel}}
  where

  open Rel₃ rel

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

{- Combined structures for abstract usage -}
module _ where
  record IsCommutativeSemigroup (rel : Rel₃ A) : Set (a ⊔ e) where
    field
      {{isSemigroup}}   : IsPartialSemigroup rel
      {{isCommutative}} : IsCommutative rel

  record IsCommutativeMonoid (rel : Rel₃ A) u : Set (a ⊔ e) where
    field
      {{isMonoid}}      : IsPartialMonoid rel u
      {{isCommutative}} : IsCommutative rel

{- Some smart constructors for semigroups and monoids -}
module _ where

  psg : ∀ {rel : Rel₃ A} →
         let open Rel₃ rel in
         {{≈-equivalence  : IsEquivalence _≈_}}
         {{∙-respects-≈   : ∀ {Φ₁ Φ₂} → Respect _≈_ (Φ₁ ∙ Φ₂)}}
         {{∙-respects-≈ˡ  : ∀ {Φ₂ Φ} → Respect _≈_ (_∙ Φ₂ ≣ Φ)}}
         {{comm           : IsCommutative rel}}
         (∙-assocᵣ′      : ∀ {a b ab c abc} → a ∙ b ≣ ab → ab ∙ c ≣ abc
                         → ∃ λ bc → a ∙ bc ≣ abc × b ∙ c ≣ bc)
    → IsPartialSemigroup rel
  psg ∙-assocᵣ
    = record
        { ∙-respects-≈ʳ = record { coe = λ eq → ∙-comm ∘ coe eq ∘ ∙-comm }
        ; ∙-assocᵣ = ∙-assocᵣ
        ; ∙-assocₗ = λ σ₁ σ₂ →
          let _ , σ₃ , σ₄ = ∙-assocᵣ (∙-comm σ₂) (∙-comm σ₁)
          in -, ∙-comm σ₄ , ∙-comm σ₃
        }

  pcm : ∀ {rel : Rel₃ A} {unit : A} →
        let open Rel₃ rel in
        {{psg : IsPartialSemigroup rel}}
        {{cm  : IsCommutative rel}}
        → (ε-unique : ∀[ _≈_ unit ⇒ Exactly unit ])
        → (idˡ  : ∀ {Φ} → unit ∙ Φ ≣ Φ)
        → (id⁻ˡ : ∀ {Φ} → ∀[ unit ∙ Φ ⇒ _≈_ Φ ])
        → IsPartialMonoid rel unit
  pcm {rel} {unit} {{pcsg}} ε-unique idˡ id⁻ˡ = isPartialMonoid′
    where
      open Rel₃ rel

      idʳ : ∀ {Φ} → Φ ∙ unit ≣ Φ
      idʳ = ∙-comm idˡ

      id⁻ʳ   : ∀ {Φ} → ∀[ Φ ∙ unit ⇒ _≈_ Φ ]
      id⁻ʳ = id⁻ˡ ∘ ∙-comm

      isPartialMonoid′ : IsPartialMonoid rel unit
      IsPartialMonoid.ε-unique isPartialMonoid′ = ε-unique
      IsPartialMonoid.∙-idˡ isPartialMonoid′ = idˡ
      IsPartialMonoid.∙-idʳ isPartialMonoid′ = idʳ
      IsPartialMonoid.∙-id⁻ˡ isPartialMonoid′ = id⁻ˡ
      IsPartialMonoid.∙-id⁻ʳ isPartialMonoid′ = id⁻ʳ
