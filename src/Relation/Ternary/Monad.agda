{-# OPTIONS --safe #-}
open import Relation.Ternary.Core

module Relation.Ternary.Monad {a e}
  {A : Set a}
  {_≈_ : A → A → Set e}
  {{ra : Rel₃ A}}
  where

open import Level
open import Data.Product
open import Function using (_∘_)

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT)
open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

{- strong indexed monads on predicates over PRSAs -}
module _ where

  RawMonad : ∀ {i} (I : Set i) → (ℓ₁ ℓ₂ : Level) → Set _
  RawMonad I ℓ₁ ℓ₂ = (i j : I) → PT A A ℓ₁ ℓ₂

  record Monad {i ℓ₁ ℓ₂} (I : Set i) (M : RawMonad I ℓ₁ ℓ₂) : Set (a ⊔ suc ℓ₁ ⊔ ℓ₂ ⊔ i) where
    field
      return : ∀ {P i₁}         → ∀[ P ⇒ M i₁ i₁ P ]
      bind   : ∀ {P i₁ i₂ i₃ Q} → ∀[ (P ─⊙ M i₂ i₃ Q) ⇒ (M i₁ i₂ P ─⊙ M i₁ i₃ Q) ]

    mapM′ : ∀ {P Q i₁ i₂} → ∀[ (P ─⊙ Q) ⇒ (M i₁ i₂ P ─⊙ M i₁ i₂ Q) ]
    mapM′ f = bind (arr λ where
      σ px → return (f ⟨ σ ⟩ px))

  open Monad {{...}} public

  {- Monadic strength -}
  module _
    {i ℓ₂} {I : Set i} {M : RawMonad I a ℓ₂} {{ monad : Monad I M }}
    {i₁ i₂} {P : Pred A a} where
    infixl 5 str
    str  : ∀ {Q : Pred A a} → M i₁ i₂ P Φ₁ → Φ₁ ∙ Φ₂ ≣ Φ → Q Φ₂ → M i₁ i₂ (P ⊙ Q) Φ
    str mp σ qx = bind (arr λ where
      σ' px → return (px ∙⟨ σ' ⟩ qx)) ⟨ σ ⟩ mp 

    infixl 5 typed-str
    typed-str : ∀ {Φ₁ Φ₂ Φ} (Q) → M i₁ i₂ P Φ₁ → Φ₁ ∙ Φ₂ ≣ Φ → Q Φ₂ → M i₁ i₂ (P ⊙ Q) Φ
    typed-str Q mp σ qx = str {Q = Q} mp σ qx

    syntax str mp σ qx = mp &⟨ σ ⟩ qx
    syntax typed-str Q mp σ qx = mp &⟨ Q # σ ⟩ qx

{- Having identities begets you external operations -}
module _
  {u} {{pm : IsPartialMonoid _≈_ ra u}}
  {i ℓ₁ ℓ₂} {I : Set i} {M : RawMonad I ℓ₁ ℓ₂} {{ monad : Monad I M }}
  where

  module _ {P Q} {{ _ : ∀ {i₁ i₂} → Respect _≈_ (M i₁ i₂ Q) }} where
    _=<<_ : ∀ {i₁ i₂ i₃} → ∀[ P ⇒ M i₂ i₃ Q ] → ∀[ M i₁ i₂ P ⇒ M i₁ i₃ Q ]
    f =<< mp =
      bind
        (arr λ where
          σ px → coe (∙-id⁻ʳ σ) (f px)) ⟨ ∙-idʳ ⟩ mp

    _>>=_ : ∀ {Φ} {i₁ i₂ i₃} → M i₁ i₂ P Φ → ∀[ P ⇒ M i₂ i₃ Q ] → M i₁ i₃ Q Φ
    mp >>= f = f =<< mp

    mapM : ∀ {Φ} {i₁ i₂} → M i₁ i₂ P Φ → ∀[ P ⇒ Q ] → M i₁ i₂ Q Φ
    mapM mp f = mp >>= (return ∘ f)

{- Additional level restrictions give you a nice strength shorthand -}
module _
  {u} {{pm : IsPartialMonoid _≈_ ra u}}
  {i ℓ₂} {I : Set i} {M : RawMonad I a ℓ₂} {{ monad : Monad I M }}
  where

    _&_ : ∀ {i₁ i₂ P Q} → M i₁ i₂ P ε → ∀[ Q ⇒ M i₁ i₂ (P ⊙ Q) ]
    mp & q = mp &⟨ ∙-idˡ ⟩ q
