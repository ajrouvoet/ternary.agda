{-# OPTIONS --safe #-}
open import Relation.Ternary.Core

module Relation.Ternary.Monad {a}
  {A : Set a}
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
RawMonad : ∀ {i} (I : Set i) → (ℓ₁ ℓ₂ : Level) → Set _
RawMonad I ℓ₁ ℓ₂ = (i j : I) → PT A A ℓ₁ ℓ₂

record Monad {i ℓ₁ ℓ₂} (I : Set i) (M : RawMonad I ℓ₁ ℓ₂) : Set (a ⊔ suc ℓ₁ ⊔ ℓ₂ ⊔ i) where
  field
    return : ∀ {P i₁}         → ∀[ P ⇒ M i₁ i₁ P ]
    bind   : ∀ {P i₁ i₂ i₃ Q} → ∀[ (P ─⊙ M i₂ i₃ Q) ⇒ (M i₁ i₂ P ─⊙ M i₁ i₃ Q) ]

  module _ {i₁ i₂ i₃} {P Q : Pred A ℓ₁} where
    bind-syntax : (P ─⊙ M i₂ i₃ Q) Φ₁ → Φ₁ ∙ Φ₂ ≣ Φ → M i₁ i₂ P Φ₂ → M i₁ i₃ Q Φ 
    bind-syntax f σ m = bind f ⟨ σ ⟩ m

    syntax bind-syntax f σ m = m ⟨ σ ⟩= f

  {- `fmap` from monadic interface -}
  module _ where
    mapM′ : ∀ {P Q i₁ i₂} → ∀[ (P ─⊙ Q) ⇒ (M i₁ i₂ P ─⊙ M i₁ i₂ Q) ]
    mapM′ f = bind (arr λ where
      σ px → return (f ⟨ σ ⟩ px))

  {- kleisli composition -}
  module _ {i₁ i₂ i₃} {P Q R : Pred A ℓ₁} {e} {_≈_ : A → A → Set e} {{_ : IsPartialSemigroup _≈_ ra}} where

    kleisli : ∀[ (Q ─⊙ M i₂ i₃ R) ⇒ (P ─⊙ M i₁ i₂ Q) ─⊙ (P ─⊙ M i₁ i₃ R) ]
    kleisli g ⟨ σ ⟩ f = bind g ∘⟨ σ ⟩ f

    kleisli-syntax : (P ─⊙ M i₁ i₂ Q) Φ₁ → Φ₂ ∙ Φ₁ ≣ Φ → (Q ─⊙ M i₂ i₃ R) Φ₂ → (P ─⊙ M i₁ i₃ R) Φ 
    kleisli-syntax g σ f = kleisli f ⟨ σ ⟩ g

    syntax kleisli-syntax f σ g = f ⟨ σ ⟩=> g

open Monad {{...}} public

{- Monadic strength -}
module Strength
  {i ℓ₂} {I : Set i} {M : RawMonad I a ℓ₂} {{ monad : Monad I M }}
  {i₁ i₂} {P : Pred A a} where
  str  : ∀ {Q : Pred A a} → ∀[ Q ⇒ M i₁ i₂ P ─⊙ M i₁ i₂ (Q ⊙ P) ]
  str qx ⟨ σ ⟩ mp = bind (arr (λ τ px → return (qx ∙⟨ τ ⟩ px))) ⟨ σ ⟩ mp

  infixl 5 str-syntax
  str-syntax  : ∀ {Q : Pred A a} → Q Φ₁ → Φ₁ ∙ Φ₂ ≣ Φ → M i₁ i₂ P Φ₂ → M i₁ i₂ (Q ⊙ P) Φ
  str-syntax qx σ mp = str qx ⟨ σ ⟩ mp
  syntax str-syntax qx σ mp = mp &⟨ σ ⟩ qx

  infixl 5 typed-str-syntax
  typed-str-syntax : ∀ {Φ₁ Φ₂ Φ} (Q) → Q Φ₁ → Φ₁ ∙ Φ₂ ≣ Φ → M i₁ i₂ P Φ₂ → M i₁ i₂ (Q ⊙ P) Φ
  typed-str-syntax Q qx σ mp = str {Q = Q} qx ⟨ σ ⟩ mp
  syntax typed-str-syntax Q qx σ mp = mp &⟨ Q # σ ⟩ qx

open Strength public

{- Having identities begets you external operations -}
module Bind
  {e} {_≈_ : A → A → Set e}
  {u} {{pm : IsPartialMonoid _≈_ ra u}}
  {i ℓ₁ ℓ₂} {I : Set i} {M : RawMonad I ℓ₁ ℓ₂} {{ monad : Monad I M }}
  {{ _ : ∀ {i₁ i₂ Q} → Respect _≈_ (M i₁ i₂ Q) }} where

  infixl 1 _=<<_
  _=<<_ : ∀ {i₁ i₂ i₃ P Q} → ∀[ P ⇒ M i₂ i₃ Q ] → ∀[ M i₁ i₂ P ⇒ M i₁ i₃ Q ]
  f =<< mp =
    bind
      (arr λ where
        σ px → coe (∙-id⁻ˡ σ) (f px)) ⟨ ∙-idˡ ⟩ mp

  infixl 1 _>>=_
  _>>=_ : ∀ {Φ} {i₁ i₂ i₃ P Q} → M i₁ i₂ P Φ → ∀[ P ⇒ M i₂ i₃ Q ] → M i₁ i₃ Q Φ
  mp >>= f = f =<< mp

  mapM : ∀ {i₁ i₂ P Q} → ∀[ P ⇒ Q ] → ∀[ M i₁ i₂ P ⇒ M i₁ i₂ Q ]
  mapM f mp = mp >>= (return ∘ f)

  _⟨$⟩_ : ∀ {i₁ i₂ P Q} → ∀[ P ⇒ Q ] → ∀[ M i₁ i₂ P ⇒ M i₁ i₂ Q ]
  f ⟨$⟩ mp = mapM f mp

open Bind public

{- Additional level restrictions give you a nice strength shorthand -}
module _
  {e} {_≈_ : A → A → Set e}
  {u} {{pm : IsPartialMonoid _≈_ ra u}}
  {i ℓ₂} {I : Set i} {M : RawMonad I a ℓ₂} {{ monad : Monad I M }}
  where

    _&_ : ∀ {i₁ i₂ P Q} → M i₁ i₂ P ε → ∀[ Q ⇒ M i₁ i₂ (Q ⊙ P) ]
    mp & q = mp &⟨ ∙-idʳ ⟩ q

{- Monad laws -}
module Laws
  {e} {_≈_ : A → A → Set e}
  {u} {{pm : IsPartialMonoid _≈_ ra u}}
  {i ℓ₁ ℓ₂} {I : Set i} {M : RawMonad I ℓ₁ ℓ₂} {{ monad : Monad I M }}
  {ℓ₃} (_≈ₘ_ : ∀ {i₁ i₂ P x} (l r : M i₁ i₂ P x) → Set ℓ₃)
  {{ _ : ∀ {P i₁ i₂} → Respect _≈_ (M i₁ i₂ P) }}
  where

  -- poinwise lifted
  _≐ₘ_ : ∀ {p i₁ i₂} {P : Pred A p} {Q} {x} (f g : (P ─⊙ M i₁ i₂ Q) x) → Set (ℓ₃ ⊔ a ⊔ p)
  _≐ₘ_ {P = P} {Q} {x} f g = ∀ {y z} {σ : x ∙ y ≣ z} {px : P y} → (f ⟨ σ ⟩ px) ≈ₘ (g ⟨ σ ⟩ px)

  module _ {P i₁ i₂ Q x} {f : (P ─⊙ M i₁ i₂ Q) x} where
    RightId = (f ⟨ ∙-idˡ ⟩=> arrow return) ≐ₘ f 
    LeftId  = (arrow return ⟨ ∙-idʳ ⟩=> f) ≐ₘ f
    Assoc   = ∀ {i₃ i₄ R S} {y z} {g : (Q ─⊙ M i₂ i₃ R) y} {h : (R ─⊙ M i₃ i₄ S) z}
              {xy xyz} {σ : y ∙ x ≣ xy} {τ : z ∙ xy ≣ xyz} →
              let _ , σ₃ , σ₄ = ∙-assocₗ τ σ in
              ((f ⟨ σ ⟩=> g) ⟨ τ ⟩=> h) ≐ₘ (f ⟨ σ₄ ⟩=> (g ⟨ σ₃ ⟩=> h))
