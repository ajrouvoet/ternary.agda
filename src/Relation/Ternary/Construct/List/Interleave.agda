{-# OPTIONS --safe #-}
module Relation.Ternary.Construct.List.Interleave {a} (A : Set a) where

open import Level
open import Function using (id)
open import Data.Product

open import Data.List
open import Data.List.Properties using (++-isMonoid)
open import Data.List.Relation.Ternary.Interleaving.Propositional as I public
open import Data.List.Relation.Ternary.Interleaving.Properties
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Binary.Permutation.Inductive

open import Algebra.Structures using (IsMonoid)
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary hiding (_∈_; _⊢_)

open import Relation.Ternary.Core
open import Relation.Ternary.Structures {A = List A} _≡_

private C = List A

-- TODO add to stdlib
interleaving-assoc : ∀ {a b ab c abc : List A} →
                     Interleaving a b ab → Interleaving ab c abc →
                     ∃ λ bc → Interleaving a bc abc × Interleaving b c bc
interleaving-assoc l (consʳ r)         = let _ , p , q = interleaving-assoc l r in -, consʳ p , consʳ q
interleaving-assoc (consˡ l) (consˡ r) = let _ , p , q = interleaving-assoc l r in -, consˡ p , q
interleaving-assoc (consʳ l) (consˡ r) = let _ , p , q = interleaving-assoc l r in -, consʳ p , consˡ q
interleaving-assoc [] []               = [] , [] , []

instance
  interleave : Rel₃ C
  interleave = record { _∙_≣_ = Interleaving }

{- Cross splits on interleavings -}
∙-cross : ∀ {a b c d z}
    → a ∙ b ≣ z
    → c ∙ d ≣ z
    → Σ[ frags ∈ (C × C × C × C) ]
      let ac , ad , bc , bd = frags
      in ac ∙ ad ≣ a
       × bc ∙ bd ≣ b
       × ac ∙ bc ≣ c
       × ad ∙ bd ≣ d
∙-cross [] [] =
  -, [] , [] , [] , []
∙-cross (consˡ σ₁) (consˡ σ₂) with ∙-cross σ₁ σ₂
... | _ , τ₁ , τ₂ , τ₃ , τ₄ = -, consˡ τ₁ , τ₂ , consˡ τ₃ , τ₄
∙-cross (consˡ σ₁) (consʳ σ₂) with ∙-cross σ₁ σ₂
... | _ , τ₁ , τ₂ , τ₃ , τ₄ = -, consʳ τ₁ , τ₂ , τ₃ , consˡ τ₄
∙-cross (consʳ σ₁) (consˡ σ₂) with ∙-cross σ₁ σ₂
... | _ , τ₁ , τ₂ , τ₃ , τ₄ = -, τ₁ , consˡ τ₂ , consʳ τ₃ , τ₄
∙-cross (consʳ σ₁) (consʳ σ₂) with ∙-cross σ₁ σ₂
... | _ , τ₁ , τ₂ , τ₃ , τ₄ = -, τ₁ , consʳ τ₂ , τ₃ , consʳ τ₄

instance
  comm-semigroup : IsPartialCommutativeSemigroup interleave
  IsPartialCommutativeSemigroup.≈-equivalence comm-semigroup = isEquivalence
  IsPartialCommutativeSemigroup.∙-respects-≈′ comm-semigroup  refl = id
  IsPartialCommutativeSemigroup.∙-respects-≈ˡ′ comm-semigroup refl = id
  IsPartialCommutativeSemigroup.∙-assocᵣ′ comm-semigroup = interleaving-assoc
  IsPartialCommutativeSemigroup.∙-comm comm-semigroup = I.swap

  comm-monoid : IsPartialCommutativeMonoid interleave []
  IsPartialCommutativeMonoid.ε-unique′ comm-monoid = id
  IsPartialCommutativeMonoid.∙-idˡ′ comm-monoid = right (≡⇒≋ P.refl)
  IsPartialCommutativeMonoid.∙-id⁻ˡ′ comm-monoid [] = refl
  IsPartialCommutativeMonoid.∙-id⁻ˡ′ comm-monoid (consʳ σ) = cong (_ ∷_) (∙-id⁻ˡ′ σ)

  monoid : ∀ {a} {A : Set a} → IsMonoid {A = List A} _≡_ _++_ []
  monoid = ++-isMonoid

  total : IsTotal interleave _++_ []

  IsTotal.∙-∙ₗ total {Φₑ = []} σ = σ
  IsTotal.∙-∙ₗ total {Φₑ = x ∷ _} σ = consˡ (∙-∙ₗ σ)

  IsTotal.∙-∙ᵣ total {Φₑ = []} σ = σ
  IsTotal.∙-∙ᵣ total {Φₑ = x ∷ _} σ = consʳ (∙-∙ᵣ σ)

  -- list-positive : IsPositive interleave ε
  -- list-positive = record
  --   { ∙-εˡ = λ where [] → refl }

  -- list-has-cross⁺ : HasCrossSplit⁺ interleave
  -- list-has-cross⁺ = record { cross = ∙-cross }
