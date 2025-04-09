{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Monad {a}
  {A : Set a} {{ra : Rel₃ A}}
  where

open import Level
open import Data.Product
open import Function using (_∘_; id)

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Functor public
open import Effect.Monad.Predicate

{- strong indexed monads on predicates over PRSAs -}
RawMonad : ∀ {i} (I : Set i) → (ℓ₁ ℓ₂ : Level) → Set _
RawMonad I ℓ₁ ℓ₂ = (i j : I) → PT A A ℓ₁ ℓ₂

-- regular indexed monad on indexed sets
record Monad {i} (I : Set i) (M : RawMonad I a a) : Set (suc a ⊔ i) where
  field
    overlap {{functor}} : ∀ {i₁ i₂} → Functor (M i₁ i₂)
    return              : ∀ {P i₁}         → ∀[ P ⇒ M i₁ i₁ P ]
    _=<<_               : ∀ {i₁ i₂ i₃ P Q} → ∀[ P ⇒ M i₂ i₃ Q ] → ∀[ M i₁ i₂ P ⇒ M i₁ i₃ Q ]

  infixl 1 _>>=_
  _>>=_ : ∀ {Φ} {i₁ i₂ i₃ P Q} → M i₁ i₂ P Φ → ∀[ P ⇒ M i₂ i₃ Q ] → M i₁ i₃ Q Φ
  mp >>= f = f =<< mp

  mapM : ∀ {i₁ i₂ P Q} → ∀[ P ⇒ Q ] → ∀[ M i₁ i₂ P ⇒ M i₁ i₂ Q ]
  mapM f mp = mp >>= (return ∘ f)

  join : ∀ {i₁ i₂ i₃ P} → ∀[ M i₁ i₂ (M i₂ i₃ P) ⇒ M i₁ i₃ P ]
  join mmp = mmp >>= id

open Monad {{...}} public

record Strong {i} (I : Set i) (M : RawMonad I a a) : Set (suc a ⊔ i) where
  field
    overlap {{monad}} : Monad I M
    str       : ∀ {i₁ i₂} → Strength (M i₁ i₂)

  module _ {i₁ i₂ i₃} {P Q} where
    bind : ∀[ (P ─✴ M i₂ i₃ Q) ⇒ (M i₁ i₂ P ─✴ M i₁ i₃ Q) ]
    bind f ⟨ σ ⟩ mp with f✴mp ← str f ⟨ σ ⟩ mp = join (apply ⟨$⟩ f✴mp)

    bind-syntax : ∀ {Φ₁ Φ₂ Φ : A} → (P ─✴ M i₂ i₃ Q) Φ₁ → Φ₁ ∙ Φ₂ ≣ Φ → M i₁ i₂ P Φ₂ → M i₁ i₃ Q Φ
    bind-syntax f σ m = bind f ⟨ σ ⟩ m

    syntax bind-syntax f σ m = m ⟨ σ ⟩= f

  {- strong `fmap` from monadic interface -}
  module _ where
    mapM′ : ∀ {P Q i₁ i₂} → ∀[ (P ─✴ Q) ⇒ (M i₁ i₂ P ─✴ M i₁ i₂ Q) ]
    mapM′ f = bind (arr λ where
      σ px → return (f ⟨ σ ⟩ px))

  {- strong kleisli composition -}
  module _
    {e} {_≈_ : A → A → Set e} {{_ : IsPartialSemigroup _≈_ ra}}
    {i₁ i₂ i₃} {P Q R : Pred A a} where

    kleisli : ∀[ (Q ─✴ M i₂ i₃ R) ⇒ (P ─✴ M i₁ i₂ Q) ─✴ (P ─✴ M i₁ i₃ R) ]
    kleisli g ⟨ σ ⟩ f = bind g ∘⟨ σ ⟩ f

    kleisli-syntax : ∀ {Φ₁ Φ₂ Φ : A} → (P ─✴ M i₁ i₂ Q) Φ₁ → Φ₂ ∙ Φ₁ ≣ Φ → (Q ─✴ M i₂ i₃ R) Φ₂ → (P ─✴ M i₁ i₃ R) Φ
    kleisli-syntax g σ f = kleisli f ⟨ σ ⟩ g

    syntax kleisli-syntax f σ g = f ⟨ σ ⟩=> g

  {- Monadic strength -}
  module _ {i₁ i₂} {P : Pred A a} where

    infixl 5 str-syntax
    str-syntax  : ∀ {Q : Pred A a} {Φ₁ Φ₂ Φ : A} → Q Φ₁ → Φ₁ ∙ Φ₂ ≣ Φ → M i₁ i₂ P Φ₂ → M i₁ i₂ (Q ✴ P) Φ
    str-syntax qx σ mp = str qx ⟨ σ ⟩ mp
    syntax str-syntax qx σ mp = qx &⟨ σ ⟩ mp

    infixl 5 typed-str-syntax
    typed-str-syntax : ∀ {Φ₁ Φ₂ Φ : A} Q → Q Φ₁ → Φ₁ ∙ Φ₂ ≣ Φ → M i₁ i₂ P Φ₂ → M i₁ i₂ (Q ✴ P) Φ
    typed-str-syntax Q qx σ mp = str {Q = Q} qx ⟨ σ ⟩ mp
    syntax typed-str-syntax Q qx σ mp = Q ∋ qx &⟨ σ ⟩ mp

  {- Monoid structure gives a nice shorthands when one side is resourceless -}
  module _ {u} {e} {_≈_ : A → A → Set e} {{pm : IsPartialMonoid _≈_ ra u}} where
    open import Relation.Binary.PropositionalEquality

    _>>_ : ∀ {i₁ i₂ i₃ P Φ₂} {{_ : Respect _≈_ (M i₂ i₃ P)}}
         → M i₁ i₂ Emp ε → M i₂ i₃ P Φ₂ → M i₁ i₃ P Φ₂
    _>>_ {P = P} m mp = do
      mp ∙⟨ σ ⟩ refl ←  (M _ _ P) ∋ mp &⟨ ∙-idʳ ⟩ m
      coe (∙-id⁻ʳ σ) mp

    _&_ : ∀ {i₁ i₂ P Q Φ} → Q Φ → M i₁ i₂ P ε → M i₁ i₂ (Q ✴ P) Φ
    q & mp = q &⟨ ∙-idʳ ⟩ mp

  module _ {{_ : IsCommutative ra }} where

    mzip : ∀ {P Q i₁ i₂ i₃} → ∀[ M i₁ i₂ P ⇒ M i₂ i₃ Q ─✴ M i₁ i₃ (P ✴ Q) ]
    mzip {P} {Q} mp ⟨ σ ⟩ mq = do
      mq ∙⟨ σ ⟩ px ← mq &⟨ ∙-comm σ ⟩ mp
      P ∋ px &⟨ ∙-comm σ ⟩ mq

open Strong {{...}} public

module _ {g} {G : Set g}
  {{gr : Rel₃ G}}
  {e} {_≈_ : G → G → Set e} {ug} {{gm : IsPartialMonoid _≈_ gr ug}}
  where

  private
    variable
      Δ₁ Δ₂ Δ₃ Δ : G

  record GradedMonad (M[_] : G → Pt A a) : Set (suc (a ⊔ g)) where
    field
      {{functor}} : Functor M[ Δ ]
      unit     : ∀ {P} → ∀[ P ⇒ M[ ε ] P ]
      multiply : ∀ {P} → Δ₁ ∙ Δ₂ ≣ Δ → ∀[ M[ Δ₁ ] (M[ Δ₂ ] P) ⇒ M[ Δ ] P ]
      gstr     : ∀ {Δ} → Strength M[ Δ ]

    gbind : ∀ {P Q} → Δ₁ ∙ Δ₂ ≣ Δ → ∀[ P ⇒ M[ Δ₂ ] Q ] → ∀[ M[ Δ₁ ] P ⇒ M[ Δ ] Q ]
    gbind δ f mpx = multiply δ (fmap f mpx)

    gbind-syntax : ∀ {P Q} → Δ₁ ∙ Δ₂ ≣ Δ → M[ Δ₁ ] P Φ → ∀[ P ⇒ M[ Δ₂ ] Q ] → M[ Δ ] Q Φ
    gbind-syntax δ px f = gbind δ f px
    syntax gbind-syntax δ px f = px >>=⟨ δ ⟩ f

  open GradedMonad {{...}} public

-- {- Monad laws -}
-- module Laws
--   {e} {_≈_ : A → A → Set e}
--   {u} {{pm : IsPartialMonoid _≈_ ra u}}
--   {i ℓ₁ ℓ₂} {I : Set i} {M : RawMonad I ℓ₁ ℓ₂} {{ monad : StrongMonad I M }}
--   {ℓ₃} (_≈ₘ_ : ∀ {i₁ i₂ P x} (l r : M i₁ i₂ P x) → Set ℓ₃)
--   where

--   -- poinwise lifted
--   _≐ₘ_ : ∀ {p i₁ i₂} {P : Pred A p} {Q} {x} (f g : (P ─✴ M i₁ i₂ Q) x) → Set (ℓ₃ ⊔ a ⊔ p)
--   _≐ₘ_ {P = P} {Q} {x} f g = ∀ {y z} {σ : x ∙ y ≣ z} {px : P y} → (f ⟨ σ ⟩ px) ≈ₘ (g ⟨ σ ⟩ px)

--   module _ {P i₁ i₂ Q x} {f : (P ─✴ M i₁ i₂ Q) x} where
--     RightId = (f ⟨ ∙-idˡ ⟩=> arrow return) ≐ₘ f
--     LeftId  = (arrow return ⟨ ∙-idʳ ⟩=> f) ≐ₘ f
--     Assoc   = ∀ {i₃ i₄ R S} {y z} {g : (Q ─✴ M i₂ i₃ R) y} {h : (R ─✴ M i₃ i₄ S) z}
--               {xy xyz} {σ : y ∙ x ≣ xy} {τ : z ∙ xy ≣ xyz} →
--               let _ , σ₃ , σ₄ = ∙-assocₗ τ σ in
--               ((f ⟨ σ ⟩=> g) ⟨ τ ⟩=> h) ≐ₘ (f ⟨ σ₄ ⟩=> (g ⟨ σ₃ ⟩=> h))

