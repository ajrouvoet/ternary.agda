{-# OPTIONS --safe --without-K #-}

module Relation.Ternary.Core where

open import Level
open import Function using (const; id)

open import Data.Product

open import Relation.Unary hiding (Empty)
open import Relation.Binary hiding (_⇒_)

open import Relation.Unary
  using () renaming (｛_｝ to Exactly) public

module _ {a} {A : Set a} where
  record Respect {e p} (_≈_ : A → A → Set e) (P : Pred A p) : Set (a ⊔ e ⊔ p) where
    field
      coe : P Respects _≈_

  open Respect {{...}} public

record Rel₃ {a} (A : Set a) : Set (suc a) where

  field
    _∙_≣_ : (Φ₁ Φ₂ : A) → Pred A a

  variable
    Φ₁ Φ₂ Φ₃ Φ : A

  -- we can see the three point relation as a predicate on the carrier
  _∙_ = _∙_≣_

  -- buy one, get a preorder for free
  _≤_ : Rel A _
  Φ₁ ≤ Φ = ∃ λ Φ₂ → Φ₁ ∙ Φ₂ ≣ Φ

  {- Partial products over the relatiion -}
  module _ where

    infixr 10 _∙⟨_⟩_
    record Conj {p q} (P : Pred A p) (Q : ∀ {Φ} → P Φ → Pred A q) Φ : Set (p ⊔ q ⊔ a) where
      inductive
      constructor _∙⟨_⟩_
      field
        {Φₗ Φᵣ} : A

        px  : P Φₗ
        sep : Φₗ ∙ Φᵣ ≣ Φ
        qx  : Q px Φᵣ

    infixr 9 ∃[_]⊙_
    ∃[_]⊙_ = Conj

    infixr 9 _⊙_
    _⊙_ : ∀ {p q} → Pred A p → Pred A q → Pred A (p ⊔ q ⊔ a)
    P ⊙ Q = ∃[ P ]⊙ const Q

  {- Partial exponents over the relatiion -}
  module _ where

    infixr 8 _─⊙[_]_
    record _─⊙[_]_ {b p q} {B : Set b}
      (P : Pred B p)
      (j : B → A)
      (Q : Pred A q)
      (Φᵢ : A) : Set (p ⊔ q ⊔ a ⊔ b) where

      constructor arr

      infixl 10 _⟨_⟩_
      field
        _⟨_⟩_ : ∀ {Φₚ Φ} → j Φₚ ∙ Φᵢ ≣ Φ → P Φₚ → Q Φ

    open _─⊙[_]_ public

    infixr 8 _─⊙_ 
    _─⊙_ : ∀ {p q} (P : Pred A p) (Q : Pred A q) → Pred A (p ⊔ q ⊔ a)
    _─⊙_ = _─⊙[ id ]_

open Rel₃ {{...}} public

module _ {a} {A : Set a} where

  open import Data.List

  Just : A → Pred (List A) _
  Just t = Exactly [ t ]
