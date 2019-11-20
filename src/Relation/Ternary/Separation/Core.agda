{-# OPTIONS --safe --without-K #-}

-- Proof relevant separation algebras
module Relation.Ternary.Separation.Core where

open import Function hiding (_⟨_⟩_)
open import Level

open import Data.Unit using (tt; ⊤)
open import Data.Product hiding (map)
open import Data.List.Relation.Ternary.Interleaving.Propositional hiding (map)
open import Data.List.Relation.Binary.Equality.Propositional

open import Relation.Unary hiding (Empty)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import Algebra
open import Algebra.Structures using (IsMonoid)
open import Algebra.FunctionProperties.Core

{- Auxiliary definitions -}
module _ where

  Exactly : ∀ {a} {A : Set a} → A → Pred A a
  Exactly x y = y ≡ x

module _ {a} {A : Set a} where
  record Respect {e p} (_≈_ : A → A → Set e) (P : Pred A p) : Set (a ⊔ e ⊔ p) where
    field
      coe : P Respects _≈_

  open Respect {{...}} public

  instance respect-≡ : ∀ {p} {P : Pred A p} → Respect _≡_ P
  Respect.coe respect-≡ P.refl = id

record RawSep {a} (A : Set a) : Set (suc a) where

  field
    _⊎_≣_ : (Φ₁ Φ₂ : A) → Pred A a

  variable
    Φ₁ Φ₂ Φ₃ Φ : A

  -- we can see the three point relation as a predicate on the carrier
  _⊎_ = _⊎_≣_

  -- buy one, get a preorder for free
  _≤_ : Rel A _
  Φ₁ ≤ Φ = ∃ λ Φ₂ → Φ₁ ⊎ Φ₂ ≣ Φ

  -- remainder
  rem : ∀ {x y} → x ≤ y → A
  rem (z , _) = z

  -- separating conjunction
  infixr 10 _×⟨_⟩_
  record Conj {p q} (P : Pred A p) (Q : ∀ {Φ} → P Φ → Pred A q) Φ : Set (p ⊔ q ⊔ a) where
    inductive
    constructor _×⟨_⟩_
    field
      {Φₗ Φᵣ} : A

      px  : P Φₗ
      sep : Φₗ ⊎ Φᵣ ≣ Φ
      qx  : Q px Φᵣ

  infixr 9 ∃[_]✴_
  ∃[_]✴_ = Conj

  infixr 9 _✴_
  _✴_ : ∀ {p q} → Pred A p → Pred A q → Pred A (p ⊔ q ⊔ a)
  P ✴ Q = ∃[ P ]✴ const Q

  -- | Separating implication / magic is what you wand

  infixr 8 _─✴[_]_
  record _─✴[_]_ {b p q} {B : Set b}
    (P : Pred B p) (j : B → A) (Q : Pred A q)
    (Φᵢ : A) : Set (p ⊔ q ⊔ a ⊔ b) where
    constructor wand
    infixl 10 _⟨_⟩_
    field
      _⟨_⟩_ : ∀ {Φₚ Φ} → Φᵢ ⊎ j Φₚ ≣ Φ → P Φₚ → Q Φ

  open _─✴[_]_ public

  infixr 8 _─✴_ 
  _─✴_ : ∀ {p q} (P : Pred A p) (Q : Pred A q) → Pred A (p ⊔ q ⊔ a)
  _─✴_ = _─✴[ id ]_

record IsSep {a e} {A : Set a} (Eq : A → A → Set e) (s : RawSep A) : Set (a ⊔ e) where
  open RawSep s

  field
    overlap {{ ≈-equivalence }} : IsEquivalence Eq
    ⊎-respects-≈  : ∀ {Φ₁ Φ₂ Φ Φ′} → Eq Φ Φ′ → Φ₁ ⊎ Φ₂ ≣ Φ → Φ₁ ⊎ Φ₂ ≣ Φ′
    ⊎-respects-≈ˡ : ∀ {Φ₁ Φ₂ Φ₁′}  → Eq Φ₁ Φ₁′ → ∀[ Φ₁ ⊎ Φ₂ ⇒ Φ₁′ ⊎ Φ₂ ]

    ⊎-comm   : ∀ {Φ₁ Φ₂} → ∀[ Φ₁ ⊎ Φ₂ ⇒ Φ₂ ⊎ Φ₁ ]
    ⊎-assoc  : ∀ {a b ab c abc}
               → a ⊎ b ≣ ab → ab ⊎ c ≣ abc
               → ∃ λ bc → a ⊎ bc ≣ abc × b ⊎ c ≣ bc

  module _ where
    ⊎-respects-≈ʳ : ∀ {Φ₁ Φ₂ Φ₂′} → Eq Φ₂ Φ₂′ → ∀[ Φ₁ ⊎ Φ₂ ⇒ Φ₁ ⊎ Φ₂′ ]
    ⊎-respects-≈ʳ eq = ⊎-comm ∘ ⊎-respects-≈ˡ eq ∘ ⊎-comm

  module _ where
    ⊎-unassoc : ∀ {b c bc a abc}
                → a ⊎ bc ≣ abc → b ⊎ c ≣ bc
                → ∃ λ ab → a ⊎ b ≣ ab × ab ⊎ c ≣ abc
    ⊎-unassoc σ₁ σ₂ =
      let _ , σ₃ , σ₄ = ⊎-assoc (⊎-comm σ₂) (⊎-comm σ₁)
      in -, ⊎-comm σ₄ , ⊎-comm σ₃

    resplit : ∀ {a b c d ab cd abcd} →
              a ⊎ b ≣ ab → c ⊎ d ≣ cd → ab ⊎ cd ≣ abcd →
              ∃₂ λ ac bd → a ⊎ c ≣ ac × b ⊎ d ≣ bd × ac  ⊎ bd  ≣ abcd
    resplit σ₁ σ₂ σ     with ⊎-assoc σ₁ σ
    ... | bcd , σ₃ , σ₄ with ⊎-unassoc σ₄ (⊎-comm σ₂)
    ... | bd  , σ₅ , σ₆ with ⊎-unassoc σ₃ σ₆
    ... | abd , σ₇ , σ₈ with ⊎-unassoc (⊎-comm σ₈) σ₇
    ... | ac  , τ  , τ' = -, -, ⊎-comm τ , σ₅ , τ'

    recombine : ∀ {a b ab c abc} →
      a ⊎ b ≣ ab → ab ⊎ c ≣ abc →
      ∃ λ ac → a ⊎ c ≣ ac × ac ⊎ b ≣ abc
    recombine σ₁ σ₂ with ⊎-assoc σ₁ σ₂
    ... | _ , σ₃ , σ₄ = ⊎-unassoc σ₃ (⊎-comm σ₄) 

  -- pairs commute
  module _ {p q} {P : Pred A p} {Q : Pred A q} where
    ✴-swap : ∀[ (P ✴ Q) ⇒ (Q ✴ P) ]
    ✴-swap (px ×⟨ σ ⟩ qx) = qx ×⟨ ⊎-comm σ ⟩ px

  -- pairs rotate and reassociate
  module _ {p q r} {P : Pred A p} {Q : Pred A q} {R : Pred A r} where
    ✴-assocₗ : ∀[ P ✴ (Q ✴ R) ⇒ (P ✴ Q) ✴ R ]
    ✴-assocₗ (p ×⟨ σ₁ ⟩ (q ×⟨ σ₂ ⟩ r)) =
      let _ , σ₃ , σ₄ = ⊎-assoc (⊎-comm σ₂) (⊎-comm σ₁) in
      (p ×⟨ ⊎-comm σ₄ ⟩ q) ×⟨ ⊎-comm σ₃ ⟩ r

    ✴-assocᵣ : ∀[ (P ✴ Q) ✴ R ⇒ P ✴ (Q ✴ R) ]
    ✴-assocᵣ ((p ×⟨ σ₁ ⟩ q) ×⟨ σ₂ ⟩ r) =
      let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in
      p ×⟨ σ₃ ⟩ q ×⟨ σ₄ ⟩ r

    ✴-rotateᵣ : ∀[ P ✴ (Q ✴ R) ⇒ R ✴ P ✴ Q ]
    ✴-rotateᵣ (p ×⟨ σ₁ ⟩ (q ×⟨ σ₂ ⟩ r)) =
      let _ , σ₃ , σ₄ = ⊎-assoc (⊎-comm σ₂) (⊎-comm σ₁) in
      r ×⟨ σ₃ ⟩ p ×⟨ ⊎-comm σ₄ ⟩ q

    ✴-rotateₗ : ∀[ P ✴ (Q ✴ R) ⇒ Q ✴ R ✴ P ]
    ✴-rotateₗ (p ×⟨ σ₁ ⟩ (q ×⟨ σ₂ ⟩ r)) =
      let _ , σ₃ , σ₄ = ⊎-assoc σ₂ (⊎-comm σ₁) in
      q ×⟨ σ₃ ⟩ r ×⟨ σ₄ ⟩ p

  module _ {p q} {P : Pred A p} {Q : Pred A q} where
    apply : ∀[ (P ─✴ Q) ✴ P ⇒ Q ]
    apply (px ×⟨ sep ⟩ qx) = px ⟨ sep ⟩ qx

  -- mapping
  module _ {p q p' q'}
    {P : Pred A p} {Q : Pred A q} {P' : Pred A p'} {Q' : Pred A q'} where

    ⟨_⟨✴⟩_⟩ : ∀[ P ⇒ P' ] → ∀[ Q ⇒ Q' ] → ∀[ P ✴ Q ⇒ P' ✴ Q' ]
    ⟨_⟨✴⟩_⟩ f g (px ×⟨ sep ⟩ qx) = (f px) ×⟨ sep ⟩ (g qx)

    both : ∀[ (P ─✴ P') ✴ (Q ─✴ Q') ⇒ P ✴ Q ─✴ P' ✴ Q' ]
    both (f ×⟨ σ₁ ⟩ g) ⟨ σ₃ ⟩ (px ×⟨ σ₂ ⟩ qx) with resplit σ₁ σ₂ σ₃
    ... | _ , _ , σ₄ , σ₅ , σ₆ = apply (f ×⟨ σ₄ ⟩ px) ×⟨ σ₆ ⟩ apply (g ×⟨ σ₅ ⟩ qx)

  module _ {p q r} {P : Pred A p} {Q : Pred A q} {R : Pred A r} where

    ✴-curry : ∀[ (P ─✴ (Q ─✴ R)) ⇒ (P ✴ Q) ─✴ R ]
    ✴-curry f ⟨ σ₂ ⟩ (p ×⟨ σ₁ ⟩ q) =
      let _ , σ₃ , σ₄ = ⊎-unassoc σ₂ σ₁ in (f ⟨ σ₃ ⟩ p) ⟨ σ₄ ⟩ q

    intro : ∀[ (P ✴ Q) ⇒ R ] → ∀[ P ⇒ (Q ─✴ R) ]
    intro f px ⟨ s ⟩ qx = f (px ×⟨ s ⟩ qx)

    com : ∀[ (P ─✴ Q) ✴ (Q ─✴ R) ⇒ (P ─✴ R) ]
    com (f ×⟨ s ⟩ g) ⟨ s' ⟩ px = let _ , eq₁ , eq₂ = ⊎-assoc (⊎-comm s) s' in g ⟨ eq₁ ⟩ (f ⟨ eq₂ ⟩ px)

    ✴-uncurry : ∀[ (P ✴ Q ─✴ R) ⇒ P ─✴ (Q ─✴ R) ]
    ✴-uncurry f ⟨ σ₁ ⟩ p ⟨ σ₂ ⟩ q = let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in f ⟨ σ₃ ⟩ (p ×⟨ σ₄ ⟩ q)

  module _ where

    ≤-trans : Φ₁ ≤ Φ₂ → Φ₂ ≤ Φ₃ → Φ₁ ≤ Φ₃
    ≤-trans (τ₁ , Φ₁⊎τ₁=Φ₂) (τ₂ , Φ₂⊎τ₂=Φ₃) =
      let τ₃ , p , q = ⊎-assoc Φ₁⊎τ₁=Φ₂ Φ₂⊎τ₂=Φ₃ in τ₃ , p

open IsSep {{...}} public

record HasUnit {a e} {A : Set a} (Eq : A → A → Set e) (sep : RawSep A) (unit : A) : Set (a ⊔ e) where
  field
    overlap {{ isSep }}         : IsSep Eq sep

  open RawSep sep

  ε = unit

  Emp : Pred A a
  Emp = Exactly ε

  field
    ⊎-idˡ    : ∀ {Φ} →  ε ⊎ Φ ≣ Φ
    ε-unique :          ∀[ Eq ε ⇒ Emp ]
    ⊎-id⁻ˡ   : ∀ {Φ₁} → ∀[ ε ⊎ Φ₁ ⇒ Eq Φ₁ ]

  ⊎-idʳ : ∀ {Φ} → Φ ⊎ ε ≣ Φ
  ⊎-idʳ = ⊎-comm ⊎-idˡ

  ⊎-id⁻ʳ : ∀[ Φ ⊎ ε ⇒ Eq Φ ]
  ⊎-id⁻ʳ = ⊎-id⁻ˡ ∘ ⊎-comm

  ε⊎ε : ∀[ ε ⊎ ε ⇒ Emp ]
  ε⊎ε p = ε-unique (⊎-id⁻ˡ p)

  infix 10 ε[_]
  ε[_] : ∀ {ℓ} → Pred A ℓ → Set ℓ
  ε[ P ] = P ε

  {- Emptyness -}
  module _ where

    data Empty {p} (P : Set p) : Pred A (a ⊔ p) where
      emp : P → Empty P ε

    -- backwards compatibility
    pattern empty = P.refl

  module _ {p} {P : Pred A p} {{_ : Respect Eq P}} where
    ✴-id⁻ʳ : ∀[ P ✴ Emp ⇒ P ]
    ✴-id⁻ʳ (px ×⟨ σ ⟩ empty) = coe (⊎-id⁻ʳ σ) px

    ✴-id⁻ˡ : ∀[ Emp ✴ P ⇒ P ]
    ✴-id⁻ˡ = ✴-id⁻ʳ ∘ ✴-swap

  module _ {p} {P : Pred A p} where
    ✴-idʳ : ∀[ P ⇒ P ✴ Emp ]
    ✴-idʳ px = px ×⟨ ⊎-idʳ ⟩ empty

    ✴-idˡ : ∀[ P ⇒ Emp ✴ P ]
    ✴-idˡ = ✴-swap ∘ ✴-idʳ

  {- A free preorder -}
  module _ where

    ≤-reflexive : Φ₁ ≡ Φ₂ → Φ₁ ≤ Φ₂
    ≤-reflexive P.refl = ε , ⊎-idʳ

    ≤-isPreorder : IsPreorder _≡_ _≤_
    ≤-isPreorder = record
      { isEquivalence = P.isEquivalence
      ; reflexive = ≤-reflexive
      ; trans = ≤-trans }

    ≤-preorder : Preorder _ _ _
    ≤-preorder = record { isPreorder = ≤-isPreorder }

    ε-minimal : ∀ {Φ} → ε ≤ Φ
    ε-minimal {Φ} = Φ , ⊎-idˡ

open HasUnit {{...}} public

-- module _ {r : RawSep A} {unit} {{_ : HasUnit r unit}} where
--   open RawSep r

--   -- a resource-polymorphic function is a pure wand
--   -- wandit : ∀ {p q} {P : Pred A p} {Q : Pred A q} → ∀[ P ⇒ Q ] → ε[ P ─✴ Q ]
--   -- wandit f ⟨ σ ⟩ p rewrite ⊎-id⁻ˡ σ = f p

record HasConcat {a e} {A : Set a} (Eq : A → A → Set e) (sep : RawSep A) : Set (suc a ⊔ e) where
  open RawSep sep

  field
    overlap {{ isSep }}  : IsSep Eq sep

    _∙_ : A → A → A 
    ⊎-∙ₗ : ∀ {Φ₁ Φ₂ Φ Φₑ} → Φ₁ ⊎ Φ₂ ≣ Φ → (Φₑ ∙ Φ₁) ⊎ Φ₂ ≣ (Φₑ ∙ Φ)

  ⊎-∙ᵣ : ∀ {Φ₁ Φ₂ Φ Φₑ} → Φ₁ ⊎ Φ₂ ≣ Φ → Φ₁ ⊎ (Φₑ ∙ Φ₂) ≣ (Φₑ ∙ Φ)
  ⊎-∙ᵣ s = ⊎-comm (⊎-∙ₗ (⊎-comm s))

open HasConcat {{...}} public

record IsPositive {a e} {A : Set a} (Eq : A → A → Set e) (sep : RawSep A) ε : Set (suc a ⊔ e) where
  open RawSep sep

  field
    overlap {{ isSep }} : IsSep Eq sep

  field
    ⊎-εˡ : ∀ {Φ₁ Φ₂} → Φ₁ ⊎ Φ₂ ≣ ε → Φ₁ ≡ ε

  ⊎-ε : ∀ {Φ₁ Φ₂} {{_ : HasUnit Eq sep ε}} → Φ₁ ⊎ Φ₂ ≣ ε → Φ₁ ≡ ε × Φ₂ ≡ ε
  ⊎-ε σ with ⊎-εˡ σ
  ... | P.refl = P.refl , ε-unique (sym $ ⊎-id⁻ˡ σ)
    where open IsEquivalence {{...}}

open IsPositive ⦃...⦄ public

record HasCrossSplit⁺ {a e} {A : Set a} (Eq : A → A → Set e) (sep : RawSep A) : Set (suc a ⊔ e) where
  open RawSep sep

  field
    overlap {{ isSep }} : IsSep Eq sep
    cross : ∀ {a b c d z}
      → a ⊎ b ≣ z
      → c ⊎ d ≣ z
      → Σ[ frags ∈ (A × A × A × A) ]
        let ac , ad , bc , bd = frags
        in ac ⊎ ad ≣ a
         × bc ⊎ bd ≣ b
         × ac ⊎ bc ≣ c
         × ad ⊎ bd ≣ d

open HasCrossSplit⁺ ⦃...⦄ public

record HasCrossSplit⁻ {a e} {A : Set a} (Eq : A → A → Set e) (sep : RawSep A) : Set (suc a ⊔ e) where
  open RawSep sep
  field
    overlap {{ isSep }} : IsSep Eq sep
    uncross : ∀ {a b c d ac ad bc bd}
      → ac ⊎ ad ≣ a
      → bc ⊎ bd ≣ b
      → ac ⊎ bc ≣ c
      → ad ⊎ bd ≣ d
      → Σ[ z ∈ A ]
          a ⊎ b ≣ z
        × c ⊎ d ≣ z

open HasCrossSplit⁻ {{...}} public

open RawSep {{...}} public

-- record MonoidalSep : Set (suc a ⊔ e) where
--   instance constructor monoidal
--   field
--     {unit}        : A
--     {{sep}}       : RawSep
--     {{isUnital}}  : HasUnit sep unit
--     {{hasConcat}} : HasConcat sep
--     {{monoid}}    : IsMonoid Eq (HasConcat._∙_  hasConcat) unit

-- module _ {{_ : MonoidalSep}} where
--   open IsMonoid {{...}}

--   ⊎-∙ : ∀ {Φₗ Φᵣ : A} → Φₗ ⊎ Φᵣ ≣ (Φₗ ∙ Φᵣ)
--   ⊎-∙ {Φₗ} {Φᵣ} = ⊎-respects-≈ˡ (identityʳ Φₗ) (⊎-∙ₗ ⊎-idˡ)
