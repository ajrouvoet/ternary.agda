{-# OPTIONS --safe #-}
open import Relation.Ternary.Core

module Relation.Ternary.Structures.PartialJoinoid {a} {A : Set a} where

open import Level

open import Data.Product
open import Relation.Binary.Structures
open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid
open import Relation.Ternary.Structures.PartialBand
open import Relation.Ternary.Structures.Commutative
open import Relation.Ternary.Structures.Functional
open IsEquivalence {{...}} using () renaming (sym to ≈-sym)

record IsJoinoid {e₂}
  -- (_≤_ : A → A → Set e₁)
  (_≈_ : A → A → Set e₂)
  (▹-rel : Rel₃ A)
  (∥-rel  : Rel₃ A)
  (∣-rel  : Rel₃ A)
  (u : A)
  : Set (a ⊔ e₂) where

  open Rel₃ ▹-rel using ()
    renaming (_∙_≣_ to _▹_≣_; _⊙_ to _▹_) public
  open Rel₃ ∥-rel  using ()
    renaming (_∙_≣_ to _∥_≣_; _⊙_ to _∥_) public
  open Rel₃ ∣-rel  using ()
    renaming (_∙_≣_ to _∣_≣_; _⊙_ to _∣_) public

  field
    -- overlap {{≤-isPreorder}}          : IsPreorder _≈_ _≤_
    overlap {{▹-isMonoid}}            : IsPartialMonoid _≈_ ▹-rel u
    overlap {{∥-isCommutativeMonoid}} : IsCommutativeMonoid _≈_ ∥-rel u
    overlap {{∣-isSemigroup}}         : IsPartialSemigroup _≈_ ∣-rel

    -- Sequential composition distributes over choice.
    -- The distributivity laws make formal that choice is different than both sequential and parallel composition,
    -- in the sense that an execution of the former only sees /either/ effect, and an execution of the latter sees /both/ the LHS and RHS effects.
    ▹-distrib-∣ʳ : ▹-rel DistribOverᵣ ∣-rel
    ▹-distrib-∣ˡ : ▹-rel DistribOverₗ ∣-rel

    -- parallel composition distributes over choice
    ∥-distrib-∣ʳ : ∥-rel DistribOverᵣ ∣-rel
    ∥-distrib-∣ˡ : ∥-rel DistribOverₗ ∣-rel

  module _ {{∣-monoid : IsPartialMonoid _≈_ ∣-rel u}} where

    -- The distributivity laws imply idempotence of choice, iff choice also has a unit.
    ∣-idem : Φ ∣ Φ ≣ Φ
    ∣-idem {Φ} with ▹-distrib-∣ʳ (∙-idˡ {Φ = ε {{∣-monoid}}}) (∙-idˡ {Φ = Φ})
    ... | _ , _ , τ₁ , τ₂ , τ₃ =
      coe (≈-sym (∙-id⁻ˡ τ₂)) (
      coe {{ ∙-respects-≈ˡ }} (≈-sym (∙-id⁻ˡ τ₁)) τ₃)

  module _
    {{∣-monoid : IsPartialMonoid _≈_ ∣-rel u}}
    {{▹-funct : IsFunctional _≈_ ▹-rel}}
    where

    ▹-absorps-∣ʳ : ∀ {a b c} → a ▹ b ≣ c → c ∣ b ≣ c
    ▹-absorps-∣ʳ {a} {b} {c} σ with ▹-distrib-∣ʳ (∙-idʳ {{∣-monoid}} {a}) σ
    ... | _ , _ , τ₁ , τ₂ , τ₃ =
      coe {{∙-respects-≈ˡ}} (functional τ₁ σ) (
      coe {{∙-respects-≈ʳ}} (≈-sym (∙-id⁻ˡ τ₂)) τ₃)

  module _
    {{∣-monoid : IsPartialMonoid _≈_ ∣-rel u}}
    {{∥-funct : IsFunctional _≈_ ∥-rel}}
    where
    ∥-absorps-∣ʳ : ∀ {a b c} → a ∥ b ≣ c → c ∣ b ≣ c
    ∥-absorps-∣ʳ {a} {b} {c} σ with ∥-distrib-∣ʳ (∙-idʳ {{∣-monoid}} {a}) σ
    ... | _ , _ , τ₁ , τ₂ , τ₃ =
      coe {{∙-respects-≈ˡ}} (functional τ₁ σ) (
      coe {{∙-respects-≈ʳ}} (≈-sym (∙-id⁻ˡ τ₂)) τ₃)

open IsJoinoid {{...}} public hiding (_▹_≣_; _∥_≣_; _∣_≣_)

-- every functional, idempotent, commutative monoid yields a joinoid.
module FromMonoid (rel : Rel₃ A)
  {e} {_≈_ : A → A → Set e} 
  {u : A} {{ m : IsCommutativeMonoid _≈_ rel u }}
  {{ f : IsFunctional _≈_ rel }}
  {{ f : IsIdempotent rel }}
  where

  instance free-joinoid : IsJoinoid _≈_ rel rel rel u
  IsJoinoid.∥-isCommutativeMonoid free-joinoid = m
  IsJoinoid.▹-distrib-∣ʳ free-joinoid σ₁ σ₂ =
    let _ , _ , σ₃ , σ₄ , σ₅ = resplit σ₁ ∙-idem σ₂
    in -, -, σ₃ , σ₄ , σ₅
  IsJoinoid.▹-distrib-∣ˡ free-joinoid σ₁ σ₂ σ₃ =
    let _ , _ , σ₃ , σ₄ , σ₅ = resplit σ₁ σ₂ σ₃
    in -, σ₃ , coe (functional σ₄ ∙-idem) σ₅
  IsJoinoid.∥-distrib-∣ʳ free-joinoid = ▹-distrib-∣ʳ
  IsJoinoid.∥-distrib-∣ˡ free-joinoid = ▹-distrib-∣ˡ
