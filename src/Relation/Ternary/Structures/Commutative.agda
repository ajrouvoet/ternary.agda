{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Structures.Commutative {a} {A : Set a} where

open import Level
open import Relation.Unary
open import Relation.Binary.Structures

open import Function using (_∘_)
open import Data.Product

open import Relation.Ternary.Core using (Rel₃; Respect; coe; Own; Commutative)
open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid
open import Relation.Ternary.Structures.Idempotent

record IsCommutative (rel : Rel₃ A) : Set (a) where
  open Rel₃ rel

  field
    ∙-comm            : Commutative rel

  -- pairs commute
  module _ {p q} {P : Pred A p} {Q : Pred A q} where
    ✴-swap : ∀[ (P ✴ Q) ⇒ (Q ✴ P) ]
    ✴-swap (px ∙⟨ σ ⟩ qx) = qx ∙⟨ ∙-comm σ ⟩ px

open IsPartialSemigroup {{...}}
open IsCommutative      {{...}}
open IsIdempotent       {{...}}

module CommutativeSemigroupOps
  {e} {_≈_ : A → A → Set e} {rel : Rel₃ A}
  {{pcsg : IsPartialSemigroup _≈_ rel}}
  {{comm : IsCommutative rel}}
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
    
  module _ {{_ : IsIdempotent U rel}} where

    -- Co-products of the extension order for any idempotent commutative semigroup,
    -- along the lines set out by McBride in EGTBS
    ≤-cop : ∀ {a b c} → a ≤ c → b ≤ c → Σ[ ab ∈ _ ] a ∙ b ≣ ab × ab ≤ c
    ≤-cop (_ , σ₁) (_ , σ₂) with (m₁₂ , _ , σ₃ , σ₄ , σ₅) ← resplit σ₁ σ₂ (∙-idem _) = m₁₂ , σ₃ , (-, σ₅)

  module _ {p q p' q'}
    {P : Pred A p} {Q : Pred A q} {P' : Pred A p'} {Q' : Pred A q'} where

    both : ∀[ (P ─✴ P') ✴ (Q ─✴ Q') ⇒ P ✴ Q ─✴ P' ✴ Q' ]
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
    ✴-rotateᵣ : ∀[ P ✴ Q ✴ R ⇒ R ✴ P ✴ Q ]
    ✴-rotateᵣ (p ∙⟨ σ₁ ⟩ (q ∙⟨ σ₂ ⟩ r)) =
      let _ , σ₃ , σ₄ = ∙-rotateᵣ σ₁ σ₂ in
      r ∙⟨ σ₃ ⟩ p ∙⟨ σ₄ ⟩ q

    ✴-rotateₗ : ∀[ P ✴ (Q ✴ R) ⇒ Q ✴ R ✴ P ]
    ✴-rotateₗ (p ∙⟨ σ₁ ⟩ (q ∙⟨ σ₂ ⟩ r)) =
      let _ , σ₃ , σ₄ = ∙-rotateₗ σ₁ σ₂ in
      q ∙⟨ σ₃ ⟩ r ∙⟨ σ₄ ⟩ p

{- Combined structures for abstract usage -}
module _ where

  record IsCommutativeSemigroup {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) : Set (a ⊔ e) where
    instance constructor isCommSemigroup
    field
      {{isSemigroup}}   : IsPartialSemigroup _≈_ rel
      {{isCommutative}} : IsCommutative rel

  record IsCommutativeMonoid {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) u : Set (a ⊔ e) where
    instance constructor isCommMonoid
    field
      {{isMonoid}}      : IsPartialMonoid _≈_ rel u
      {{isCommutative}} : IsCommutative rel

{- Some smart constructors for semigroups and monoids -}
module _  where

  -- left biased
  record IsPartialSemigroupˡ {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) : Set (a ⊔ e) where
    open Rel₃ rel
    field
      {{≈-equivalence}}  : IsEquivalence _≈_
      {{∙-respects-≈}}   : ∀ {Φ₁ Φ₂} → Respect _≈_ (Φ₁ ∙ Φ₂)
      {{∙-respects-≈ˡ}}  : ∀ {Φ₂ Φ}  → Respect _≈_ (_∙ Φ₂ ≣ Φ)

      {{comm}}           : IsCommutative rel
      assocᵣ             : ∀ {a b ab c abc} → a ∙ b ≣ ab → ab ∙ c ≣ abc
                         → ∃ λ bc → a ∙ bc ≣ abc × b ∙ c ≣ bc

    instance semigroupˡ : IsPartialSemigroup _≈_ rel
    Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ semigroupˡ) eq = ∙-comm ∘ coe eq ∘ ∙-comm
    IsPartialSemigroup.∙-assocᵣ semigroupˡ = assocᵣ
    IsPartialSemigroup.∙-assocₗ semigroupˡ σ₁ σ₂ =
      let _ , σ₃ , σ₄ = assocᵣ (∙-comm σ₂) (∙-comm σ₁)
      in -, ∙-comm σ₄ , ∙-comm σ₃

  record IsPartialMonoidˡ {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) (unit : A) : Set (a ⊔ e) where
    open Rel₃ rel

    field
      {{isSemigroup}}   : IsPartialSemigroup _≈_ rel
      {{isCommutative}} : IsCommutative rel
      {{emptiness}}     : Emptiness unit
      identityˡ  : ∀ {Φ} → unit ∙ Φ ≣ Φ
      identity⁻ˡ : ∀ {Φ} → ∀[ unit ∙ Φ ⇒ _≈_ Φ ]

    partialMonoidˡ : IsPartialMonoid _≈_ rel unit
    IsPartialMonoid.∙-idˡ partialMonoidˡ = identityˡ
    IsPartialMonoid.∙-idʳ partialMonoidˡ = ∙-comm identityˡ
    IsPartialMonoid.∙-id⁻ˡ partialMonoidˡ = identity⁻ˡ
    IsPartialMonoid.∙-id⁻ʳ partialMonoidˡ = identity⁻ˡ ∘ ∙-comm
