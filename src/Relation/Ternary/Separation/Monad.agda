open import Relation.Binary.Bundles

module Relation.Ternary.Separation.Monad {a e₁} (Aₛ : Setoid a e₁) where

open import Level
open import Data.Product
open import Function using (_∘_; case_of_)
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Separation.Core
open import Relation.Ternary.Separation.Morphisms

open Setoid Aₛ renaming (Carrier to A; _≈_ to _≈₁_)

{- strong indexed monads on predicates over PRSAs -}
module _ {{ra : RawSep A}} {u} {{as : HasUnit _≈₁_ ra u}} where

  RawMonad : ∀ {i} (I : Set i) → (ℓ : Level) → Set _
  RawMonad I ℓ = (i j : I) → Pt A ℓ

  record Monad {i} (I : Set i) ℓ (M : RawMonad I ℓ) : Set (a ⊔ suc ℓ ⊔ i) where
    field
      return : ∀ {P i₁}         → ∀[ P ⇒ M i₁ i₁ P ]
      bind   : ∀ {P i₁ i₂ i₃ Q} → ∀[ (P ─✴ M i₂ i₃ Q) ⇒ (M i₁ i₂ P ─✴ M i₁ i₃ Q) ]

    module _ {P Q} {{ _ : ∀ {i₁ i₂} → Respect _≈₁_ (M i₁ i₂ Q) }} where
      _=<<_ : ∀ {i₁ i₂ i₃} → ∀[ P ⇒ M i₂ i₃ Q ] → ∀[ M i₁ i₂ P ⇒ M i₁ i₃ Q ]
      f =<< mp =
        bind
          (wand λ where
            σ px → coe (⊎-id⁻ˡ σ) (f px)) ⟨ ⊎-idˡ ⟩ mp

      _>>=_ : ∀ {Φ} {i₁ i₂ i₃} → M i₁ i₂ P Φ → ∀[ P ⇒ M i₂ i₃ Q ] → M i₁ i₃ Q Φ
      mp >>= f = f =<< mp

      mapM : ∀ {Φ} {i₁ i₂} → M i₁ i₂ P Φ → ∀[ P ⇒ Q ] → M i₁ i₂ Q Φ
      mapM mp f = mp >>= (return ∘ f)

    mapM′ : ∀ {P Q i₁ i₂} → ∀[ (P ─✴ Q) ⇒ (M i₁ i₂ P ─✴ M i₁ i₂ Q) ]
    mapM′ f = bind (wand λ where
      σ px → return (f ⟨ σ ⟩ px))

  open Monad ⦃...⦄ public

  -- having the internal bind is enough to get strength
  module _ {i} {I : Set i} {i₁ i₂} {P} {M} {{ _ : Monad I a M }} where
    infixl 5 str
    str  : ∀ {Q : Pred A a} → M i₁ i₂ P Φ₁ → Φ₁ ⊎ Φ₂ ≣ Φ → Q Φ₂ → M i₁ i₂ (P ✴ Q) Φ
    str mp σ qx = bind (wand λ where
      σ' px → return (px ×⟨ ⊎-comm σ' ⟩ qx)) ⟨ ⊎-comm σ ⟩ mp 

    infixl 5 typed-str
    typed-str : ∀ {Φ₁ Φ₂ Φ} (Q) → M i₁ i₂ P Φ₁ → Φ₁ ⊎ Φ₂ ≣ Φ → Q Φ₂ → M i₁ i₂ (P ✴ Q) Φ
    typed-str Q mp σ qx = str {Q = Q} mp σ qx

    syntax str mp σ qx = mp &⟨ σ ⟩ qx
    syntax typed-str Q mp σ qx = mp &⟨ Q ∥ σ ⟩ qx

    _&_ : ∀ {Q} → M i₁ i₂ P ε → ∀[ Q ⇒ M i₁ i₂ (P ✴ Q) ]
    mp & q = mp &⟨ ⊎-idˡ ⟩ q

