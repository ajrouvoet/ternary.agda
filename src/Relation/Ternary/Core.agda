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

 {- Partial products over the relation -}
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
        _⟨_⟩_ : ∀ {Φₚ Φ} → Φᵢ ∙ j Φₚ ≣ Φ → P Φₚ → Q Φ

    open _─⊙[_]_ public

    infixr 8 _─⊙_ 
    _─⊙_ : ∀ {p q} (P : Pred A p) (Q : Pred A q) → Pred A (p ⊔ q ⊔ a)
    _─⊙_ = _─⊙[ id ]_

{- Rel morphisms -}
module _ {a} {A : Set a} where

  _flipped : Rel₃ A → Rel₃ A
  Rel₃._∙_≣_ (rel flipped) = let open Rel₃ rel in λ Φ₁ Φ₂ Φ → Φ₂ ∙ Φ₁ ≣ Φ

{- Properties of ternary relations -}
module _ {a} {A : Set a} where

  Commutative : Rel₃ A → Set a
  Commutative rel = let open Rel₃ rel
    in ∀ {a b ab : A} → a ∙ b ≣ ab → b ∙ a ≣ ab

  RightAssoc : Rel₃ A → Set a
  RightAssoc rel = let open Rel₃ rel in
    ∀ {a b ab c abc}
      → a ∙ b ≣ ab → ab ∙ c ≣ abc
      → ∃ λ bc → a ∙ bc ≣ abc × b ∙ c ≣ bc

  LeftAssoc : Rel₃ A → Set a
  LeftAssoc rel = let open Rel₃ rel in
    ∀ {a bc b c abc}
      → a ∙ bc ≣ abc → b ∙ c ≣ bc
      → ∃ λ ab → a ∙ b ≣ ab × ab ∙ c ≣ abc

  -- (a - b) - c ≈> a - (b + c)
  RightAssoc′ : (add : Rel₃ A) → (sub : Rel₃ A) → Set a
  RightAssoc′ add sub =
    let open Rel₃ add renaming (_∙_≣_ to _+_≣_)
        open Rel₃ sub renaming (_∙_≣_ to _∸_≣_)
    in ∀ {a₁ a₂ a₃ a₁-₂ a₀ a₂+₃} →
         a₁ ∸ a₂ ≣ a₁-₂ → a₁-₂ ∸ a₃ ≣ a₀ → a₂ + a₃ ≣ a₂+₃ →
         a₁ ∸ a₂+₃ ≣ a₀

  -- a - (b + c) ≈> (a - b) - c
  LeftAssoc′ : (add : Rel₃ A) → (sub : Rel₃ A) → Set a
  LeftAssoc′ add sub =
    let open Rel₃ add renaming (_∙_≣_ to _+_≣_)
        open Rel₃ sub renaming (_∙_≣_ to _∸_≣_)
    in ∀ {a₁ a₂ a₃ a₂+₃ a₀} →
         a₁ ∸ a₂+₃ ≣ a₀ → a₂ + a₃ ≣ a₂+₃ →
         ∃ λ a₁-₂ → 
           a₁ ∸ a₂ ≣ a₁-₂ × a₁-₂ ∸ a₃ ≣ a₀

  -- (a ∪ b) - c => (a - c) ∪ (b - c)
  -- sub distributes over cup
  _DistribOverᵣ_ : (sub : Rel₃ A) (cup : Rel₃ A) → Set a
  _DistribOverᵣ_ sub cup =
    let open Rel₃ cup renaming (_∙_≣_ to _⊎_≣_)
        open Rel₃ sub renaming (_∙_≣_ to _∸_≣_)
    in ∀ {a b c a∪b d}
      → a ⊎ b ≣ a∪b → a∪b ∸ c ≣ d
      → ∃₂ λ a-c b-c → a ∸ c ≣ a-c × b ∸ c ≣ b-c × a-c ⊎ b-c ≣ d

  -- (a ∪ b) - c <= (a - c) ∪ (b - c)
  _DistribOverₗ_ : (sub : Rel₃ A) → (cup : Rel₃ A) → Set a
  _DistribOverₗ_ sub cup =
    let open Rel₃ cup renaming (_∙_≣_ to _⊎_≣_)
        open Rel₃ sub renaming (_∙_≣_ to _∸_≣_)
    in ∀ {a b c d a-c b-c}
      → a ∸ c ≣ a-c → b ∸ c ≣ b-c → a-c ⊎ b-c ≣ d
      → ∃ λ a∪b → a ⊎ b ≣ a∪b × a∪b ∸ c ≣ d

  LeftIdentity : Rel₃ A → A → Set a
  LeftIdentity rel ε = let open Rel₃ rel in ∀ {Φ} → ε ∙ Φ ≣ Φ

  LeftIdentity⁻ : ∀ {e} → (A → A → Set e) → Rel₃ A → A → Set (a ⊔ e)
  LeftIdentity⁻ _≈_ rel ε = let open Rel₃ rel in ∀ {Φ Φ′} → ε ∙ Φ ≣ Φ′ → Φ ≈ Φ′

  RightIdentity : Rel₃ A → A → Set a
  RightIdentity rel ε = let open Rel₃ rel in ∀ {Φ} → Φ ∙ ε ≣ Φ

  RightIdentity⁻ : ∀ {e} → (A → A → Set e) → Rel₃ A → A → Set (a ⊔ e)
  RightIdentity⁻ _≈_ rel ε = let open Rel₃ rel in ∀ {Φ Φ′} → Φ ∙ ε ≣ Φ′ → Φ ≈ Φ′

  LeftZero : Rel₃ A → A → Set a
  LeftZero rel z = let open Rel₃ rel in ∀ {Φ} → z ∙ Φ ≣ z

  LeftZero⁻ : ∀ {e} → (A → A → Set e) → Rel₃ A → A → Set (a ⊔ e)
  LeftZero⁻ _≈_ rel z = let open Rel₃ rel in ∀ {Φ Φ′} → z ∙ Φ ≣ Φ′ → Φ′ ≈ z

  RightZero : Rel₃ A → A → Set a
  RightZero rel z = let open Rel₃ rel in ∀ {Φ} → Φ ∙ z ≣ z

  RightZero⁻ : ∀ {e} → (A → A → Set e) → Rel₃ A → A → Set (a ⊔ e)
  RightZero⁻ _≈_ rel z = let open Rel₃ rel in ∀ {Φ Φ′} → Φ ∙ z ≣ Φ′ → Φ′ ≈ z

  Idempotent : Rel₃ A → Set a
  Idempotent rel = let open Rel₃ rel in ∀ {Φ} → Φ ∙ Φ ≣ Φ

  Idempotent⁻ : ∀ {e} → (A → A → Set e) → Rel₃ A → Set (a ⊔ e)
  Idempotent⁻ _≈_ rel = let open Rel₃ rel in ∀ {Φ Φ′} → Φ ∙ Φ ≣ Φ′ → Φ ≈ Φ′

  LeftMonotone : ∀ {e} → (A → A → Set e) → Rel₃ A → Set (a ⊔ e)
  LeftMonotone _∼_ rel = let open Rel₃ rel in 
    ∀ {Φ₁ Φ₂ Φ Φ₃ Φ′} → Φ₁ ∙ Φ₂ ≣ Φ → Φ₁ ∼ Φ₃ → Φ₃ ∙ Φ₂ ≣ Φ′ → Φ ∼ Φ′

  RightMonotone : ∀ {e} → (A → A → Set e) → Rel₃ A → Set (a ⊔ e)
  RightMonotone _∼_ rel = LeftMonotone _∼_ (rel flipped)

  Functional : ∀ {e} → (A → A → Set e) → Rel₃ A → Set (a ⊔ e) 
  Functional _≈_ rel = let open Rel₃ rel in
    ∀ {a b c c'} → a ∙ b ≣ c → a ∙ b ≣ c' → c ≈ c'

  -- a ∸ (b ∩ c) ≈ (a ∸ b) ∪ (a ∸ c)
  DeMorganʳ : (sub cap cup : Rel₃ A) → Set a
  DeMorganʳ sub cap cup =
    let open Rel₃ cup renaming (_∙_≣_ to _⊎_≣_)
        open Rel₃ sub renaming (_∙_≣_ to _∸_≣_)
        open Rel₃ cap renaming (_∙_≣_ to _∩_≣_)
    in
      ∀ {a b c b∩c a-b∩c} → b ∩ c ≣ b∩c → a ∸ b∩c ≣ a-b∩c →
      ∃₂ λ a-b a-c → (a ∸ b ≣ a-b) × (a ∸ c ≣ a-c) × (a-b ⊎ a-c ≣ a-b∩c)
      

module _ {a} {A : Set a} where

  open import Data.List

  Just : A → Pred (List A) _
  Just t = Exactly [ t ]

open Rel₃ {{...}} public
