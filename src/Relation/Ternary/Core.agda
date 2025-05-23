{-# OPTIONS --safe --without-K #-}

module Relation.Ternary.Core where

open import Agda.Primitive
open import Function using (const; id)

open import Data.Product

open import Relation.Unary hiding (Empty)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Unary
  using () renaming (｛_｝ to Own) public

module _ {a} {A : Set a} where
  record Respect {e p} (_≈_ : A → A → Set e) (P : Pred A p) : Set (a ⊔ e ⊔ p) where
    field
      coe : P Respects _≈_

  record IsUnique {e} (_≈_ : A → A → Set e) (el : A) : Set (a ⊔ e) where
    field
      unique : ∀ {a} → el ≈ a → el ≡ a

    instance unique-respects : Respect _≈_ (Own el)
    Respect.coe unique-respects eq refl rewrite unique eq = refl
    
  instance unique-≡ : ∀ {a} → IsUnique _≡_ a
  IsUnique.unique unique-≡ eq = eq

  open Respect {{...}} public
  open IsUnique {{...}} public

module _ {a} {A : Set a} where

  True : ∀ {ℓ} → Pred A ℓ
  True = λ _ → ⊤
    where open import Data.Unit.Polymorphic

record Rel₃ {a} (A : Set a) : Set (lsuc a) where

  field
    _∙_≣_ : (Φ₁ Φ₂ : A) → Pred A a

  variable
    Φ₁ Φ₂ Φ₃ Φ : A

  module _ where
    -- we can see the three point relation as a predicate on the carrier
    _∙_ = _∙_≣_

  module _ where
    -- concise notation for "being separated"
    _◆_ = λ Φ₁ Φ₂ → ∃ λ Φ → Φ₁ ∙ Φ₂ ≣ Φ

    whole : Φ₁ ◆ Φ₂ → A
    whole = proj₁

  module _ where
    -- buy one, get a preorder for free
    _≤_ : Rel A _
    Φ₁ ≤ Φ = ∃ λ Φ₂ → Φ₁ ∙ Φ₂ ≣ Φ

 {- Partial products over the relation -}
  module _ where

    infixr 10 _∙⟨_⟩_
    record Conj {p q} (P : Pred A p) (Q : ∀ {Φ} → P Φ → Pred A q) Φ : Set (p ⊔ q ⊔ a) where
      pattern
      constructor _∙⟨_⟩_
      field
        {Φₗ Φᵣ} : A

        px  : P Φₗ
        sep : Φₗ ∙ Φᵣ ≣ Φ
        qx  : Q px Φᵣ

    infixr 9 Σ✴-syntax
    Σ✴-syntax : ∀ {p q} → (P : Pred A p) → (Q : ∀ {Φ} → P Φ → Pred A q) → Pred A (p ⊔ q ⊔ a)
    Σ✴-syntax = Conj

    syntax Σ✴-syntax A (λ x → B) = Σ[ x ∈ A ]✴ B

    infixr 9 _✴_
    _✴_ : ∀ {p q} → Pred A p → Pred A q → Pred A (p ⊔ q ⊔ a)
    P ✴ Q = Σ[ x ∈ P ]✴ Q

  {- Partial exponents over the relation -}
  module _ where

    record Wand {b p q} {B : Set b}
      (P : Pred B p)
      (j : B → A)
      (Q : ∀ {Φ} → P Φ → Pred A q)
      (Φᵢ : A) : Set (p ⊔ q ⊔ a ⊔ b) where

      constructor arr

      infixl 10 _⟨_⟩_
      field
        _⟨_⟩_ : ∀ {Φₚ Φ} → Φᵢ ∙ j Φₚ ≣ Φ → (px : P Φₚ) → Q px Φ

    open Wand public

    infixr 8 _─✴[_]_
    _─✴[_]_ : ∀ {p q b} {B : Set b} (P : Pred B p) (j : B → A) (Q : Pred A q) → Pred A (p ⊔ q ⊔ a ⊔ b)
    (P ─✴[ j ] Q) = Wand P j (const Q)

    infixr 8 Π✴-syntax
    Π✴-syntax : ∀ {p q} → (P : Pred A p) → (Q : ∀ {Φ} → P Φ → Pred A q) → Pred A (p ⊔ q ⊔ a)
    Π✴-syntax P Q = Wand P id Q
    syntax Π✴-syntax P (λ x → Q) = Π[ x ∈ P ]✴ Q

    -- TODO this should be in Relation.Unary
    infixr 8 Π⇒-syntax
    Π⇒-syntax : ∀ {p q} → (P : Pred A p) → (Q : ∀ {Φ} → P Φ → Pred A q) → Pred A (p ⊔ q)
    Π⇒-syntax P Q = λ Φ → (px : P Φ) → Q px Φ
    syntax Π⇒-syntax P (λ x → Q) = Π[ x ∈ P ]⇒ Q

    infixr 8 _─✴_
    _─✴_ : ∀ {p q} (P : Pred A p) (Q : Pred A q) → Pred A (p ⊔ q ⊔ a)
    P ─✴ Q = Wand P id (const Q)

  module _ {p q} {P : Pred A p} {Q : Pred A q} where

    apply : ∀[ (P ─✴ Q) ✴ P ⇒ Q ]
    apply (f ∙⟨ σ ⟩ px) = f ⟨ σ ⟩ px

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

  One : A → Pred (List A) _
  One t = Own [ t ]

