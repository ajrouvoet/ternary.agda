{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Arrows {a}
  {A : Set a} {{ra : Rel₃ A}}
  where

open import Level
open import Data.Unit
open import Data.Product
open import Function using (_∘_; id)

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad

private 
  variable
    P Q R S : Pred A a

module _ where

  RawArrow = Pred A a → Pred A a → Pred A a

  record Arrow (_⟹_ : RawArrow) : Set (suc a) where
    field
      pureArr  : ∀[ (P ─✴ Q) ⇒ (P ⟹ Q) ]
      sequence : ∀[ (P ⟹ Q) ⇒ (Q ⟹ R) ─✴ (P ⟹ R) ]
      first    : ∀[ (P ⟹ Q) ⇒ ((P ✴ R) ⟹ (Q ✴ R)) ]
      
    sequence-syntax : ∀ {Φ₁ Φ₂ Φ}
                    → (P ⟹ Q) Φ₁ → Φ₁ ∙ Φ₂ ≣ Φ → (Q ⟹ R) Φ₂ 
                    → (P ⟹ R) Φ
    sequence-syntax f σ g = sequence f ⟨ σ ⟩ g
    syntax sequence-syntax f σ g = f >> σ >> g

    module _ {e} {_≈_ : A → A → Set e} {u} {{_ : IsPartialMonoid _≈_ ra u}} {{_ : IsCommutative ra}} where

      second : ∀[ (P ⟹ Q) ⇒ ((R ✴ P) ⟹ (R ✴ Q)) ]
      second f = pureArr (arrow ✴-swap) >> ∙-idˡ >> (first f >> ∙-idʳ >> pureArr (arrow ✴-swap))

      onBoth : ∀[ (P ⟹ R) ⇒ (Q ⟹ S) ─✴ ((P ✴ Q) ⟹ (R ✴ S)) ]
      onBoth f ⟨ σ ⟩ g = first f >> σ >> second g
      
      mkStar : {{_ : IsIntuitionistic P ra}} 
             → ∀[ (P ⟹ Q) ⇒ (P ⟹ R) ─✴ (P ⟹ (Q ✴ R)) ]
      mkStar f ⟨ σ ⟩ g = pureArr (arrow copy) >> ∙-idˡ >> (onBoth f ⟨ σ ⟩ g)
      
module _ where
      
  Kleisli : (M : RawMonad ⊤ a a) → RawArrow
  Kleisli M P Q = P ─✴ M _ _ Q
      
  module _ {e} {_≈_ : A → A → Set e} {u} {{_ : IsPartialMonoid _≈_ ra u}} where

    record ArrowApp (_⟹_ : RawArrow) : Set (suc a) where
      field
        {{isArrow}} : Arrow _⟹_
        app         : ε[ (((P ⟹ Q) ✴ P) ⟹ Q) ]

    module _ {{_ : IsCommutative ra}} {M : RawMonad ⊤ a a} {{m : Strong ⊤ M}} where

      instance kleisliArrow : Arrow (Kleisli M)
      Arrow.pureArr kleisliArrow f ⟨ σ ⟩ px = return (f ⟨ σ ⟩ px)
      Arrow.sequence kleisliArrow f ⟨ σ ⟩ g    = kleisli g ⟨ ∙-comm σ ⟩ f
      Arrow.first kleisliArrow f ⟨ σ ⟩ (px ∙⟨ τ ⟩ qx) with _ , σ₂ , σ₃ ← ∙-assocₗ σ τ = 
        ✴-swap ⟨$⟩ (f ⟨ σ₂ ⟩ px &⟨ ∙-comm σ₃ ⟩ qx)

      instance kleisliApp : {{_ : ∀ {P} → Respect _≈_ (M _ _ P)}} 
                          → ArrowApp (Kleisli M)
      ArrowApp.app kleisliApp ⟨ σ ⟩ (f ∙⟨ σ₂ ⟩ px) = coe (∙-id⁻ˡ σ) (f ⟨ σ₂ ⟩ px)
