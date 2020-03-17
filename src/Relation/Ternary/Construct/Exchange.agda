{-# OPTIONS --safe #-}
-- The Exchange PRSA
--
-- This proof relevant separation algebra balances multiple "accounts"
-- that can /each/ both supply (/up/) and demand (/down/) some amount of an underlying
-- PRSA A.
-- At every node in the splitting tree, two accounts can "exchange" some amount,
-- meaning that the demand on the left can be fulfilled by some supply on the right and vice versa.

open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Construct.Exchange.Param

module Relation.Ternary.Construct.Exchange {ℓ e s}
  {A : Set ℓ} {εₐ} {r₁ r₂} {_≈ₐ_ : A → A → Set e}
  (param : Param A εₐ r₁ r₂ _≈ₐ_ s) where

open Param param

open import Level hiding (Lift)
open import Data.Product
open import Data.Unit
open import Function using (case_of_; _∘_)

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
open import Relation.Ternary.Structures.Syntax

open IsEquivalence (≈-equivalence {{IsPartialMonoid.isSemigroup r₁-monoid}})

private
  instance
    _ = r₁
    _ = r₂
  variable
    u₁ u₂ u₃ d₁ d₂ d₃ u d : A

open Rel₃ r₁ using () renaming (_∙_≣_ to _∙₁_≣_; _⊙_ to _⊙₁_; _─⊙_ to _─⊙₁_)
open Rel₃ r₂ using () renaming (_∙_≣_ to _∙₂_≣_; _⊙_ to _⊙₂_; _─⊙_ to _─⊙₂_)

module _ where

  -- Accounts are essentially pairs, but we rewrap 'm for instance search.
  record Account : Set ℓ where
    constructor _⇅_
    field
      up   : A
      down : A

    pair : A × A
    pair = up , down

  open Account public

module _ where

  open import Data.Product.Relation.Binary.Pointwise.NonDependent
  _≈_ : Account → Account → Set _
  a ≈ b = Pointwise _≈ₐ_ _≈ₐ_ (pair a) (pair b)

  instance account-equiv : IsEquivalence _≈_
  IsEquivalence.refl account-equiv  = ≈-refl , ≈-refl
  IsEquivalence.sym account-equiv   = map ≈-sym ≈-sym
  IsEquivalence.trans account-equiv (e₁ , e₂) (e₃ , e₄) = ≈-trans e₁ e₃ , ≈-trans e₂ e₄

  {- Exchange with leftovers -}
  data _-_≣_ : A → A → Account → Set ℓ where
    sub : ∀ {e d' u'} →
          d' ∙₁ e ≣ d →
          u' ∙₂ e ≣ u →
          d - u ≣ (u' ⇅ d')

  data Exchange : Account → Account → Account → Set ℓ where
    -- exchange the rings and bind 'm
    ex : ∀ {u₁' d₁' u₂' d₂'} →
      -- exchange lhs to rhs and vice versa
      d₁ - u₂ ≣ (u₂' ⇅ d₂') →
      d₂ - u₁ ≣ (u₁' ⇅ d₁') →

      -- add the remaining supply and demand
      u₁' ∙₁ u₂' ≣ u →
      d₁' ∙₂ d₂' ≣ d →

      Exchange (u₁ ⇅ d₁) (u₂ ⇅ d₂) (u ⇅ d)

private

  instance sub-respectsˡ : ∀ {u r} → Respect _≈ₐ_ (_- u ≣ r)
  Respect.coe sub-respectsˡ x (sub s₁ s₂) = sub (coe x s₁) s₂

  instance sub-respectsʳ : ∀ {u r} → Respect _≈ₐ_ (u -_≣ r)
  Respect.coe sub-respectsʳ x (sub s₁ s₂) = sub s₁ (coe x s₂)

  instance sub-respects : ∀ {u d} → Respect _≈_ (u - d ≣_)
  Respect.coe sub-respects (x , y) (sub s₁ s₂) = sub (coe y s₁) (coe x s₂)

module _ where

  instance exchange-rel : Rel₃ Account
  exchange-rel = record { _∙_≣_ = Exchange }

  instance exchange-isCommutative : IsCommutative exchange-rel
  IsCommutative.∙-comm exchange-isCommutative (ex x₁ x₂ x₃ x₄) = ex x₂ x₁ (∙-comm x₃) (∙-comm x₄)
    
  exchange-isSemigroupˡ : IsPartialSemigroupˡ _≈_ exchange-rel

  Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ˡ exchange-isSemigroupˡ) (eq₁ , eq₂) (ex x₁ x₂ σ₁ σ₂) =
    ex (coe eq₂ x₁) (coe eq₁ x₂) σ₁ σ₂
  Respect.coe (IsPartialSemigroupˡ.∙-respects-≈  exchange-isSemigroupˡ) (eq₁ , eq₂) (ex x₁ x₂ σ₁ σ₂) =
    ex x₁ x₂ (coe eq₁ σ₁) (coe eq₂ σ₂)

  -- Associativity follows from associativity of the underlying relations,
  -- in conjunction with the fact that the two relations are cross- and uncross-splittable.
  -- The documentation of this repository contains drawings of this proof tree.
  IsPartialSemigroupˡ.assocᵣ exchange-isSemigroupˡ
    (ex (sub τ-a↓  τ-b↑) (sub τ-b↓ τ-a↑)  σ-ab↑ σ-ab↓)
    (ex (sub τ-ab↓ τ-c↑) (sub τ-c↓ τ-ab↑) σ-abc↑ σ-abc↓)
      with xsplitₐ (∙-comm τ-ab↑) σ-ab↑ | xsplitₐ σ-ab↓ τ-ab↓
  ... | _ , ν₁ , ν₂ , ν₃ , ν₄ | _ , μ₁ , μ₂ , μ₃ , μ₄
    with ∙-assocᵣ ν₂ σ-abc↑ | ∙-assocᵣ (∙-comm μ₃) (∙-comm σ-abc↓)
  ... | bc↑' , ι₁ , ι₂ | bc↓ , κ₁ , κ₂
    with ∙-assocᵣ (∙-comm ν₃) τ-a↑ | ∙-rotateᵣ (∙-comm τ-b↑) (∙-comm ν₄) | ∙-assocᵣ μ₄ (∙-comm τ-c↑)
       | ∙-assocᵣ μ₂ τ-a↓          | ∙-rotateᵣ (∙-comm τ-b↓) μ₁          | ∙-assocᵣ (∙-comm ν₁) (∙-comm τ-c↓)
  ... | _ , α-a↑ , ≺-ea>bc | _ , α-b↑ , ν₅ | _ , α-c↑ , μ₅
      | _ , α-a↓ , ≺-ebc>a | _ , α-b↓ , ν₆ | _ , α-c↓ , μ₆
    with uncrossₐ (∙-comm ≺-ebc>a) ι₂ ν₅ μ₅ | uncrossover uncrossₐ ≺-ea>bc (∙-comm κ₂) μ₆ ν₆
  ... | _ , τ-bc↑ , σ-bc↑ | _ , bo , bu =
    -, ex (sub α-a↓ (∙-comm τ-bc↑)) (sub (∙-comm bo) α-a↑) ι₁ (∙-comm κ₁) 
     , ex (sub (∙-comm α-b↓) (∙-comm α-c↑)) (sub (∙-comm α-c↓) (∙-comm α-b↑)) σ-bc↑ bu

  instance exchange-isSemigroup : IsPartialSemigroup _≈_ exchange-rel
  exchange-isSemigroup = IsPartialSemigroupˡ.semigroupˡ exchange-isSemigroupˡ

{- "Identity laws" for the auxiliary exchange relation -}
module _ where

  instance exchange-emptiness : Emptiness (εₐ ⇅ εₐ)
  exchange-emptiness = record {}

  ε-sub : ∀ {xs} → εₐ - xs ≣ (xs ⇅ εₐ)
  ε-sub = sub ∙-idˡ ∙-idʳ

  sub-ε : ∀ {xs} → xs - ε ≣ (ε ⇅ xs)
  sub-ε = sub ∙-idʳ ∙-idˡ

  ε-sub⁻ : ∀ {xs ys zs} → ε - xs ≣ (ys ⇅ zs) → ys ≈ₐ xs × zs ≡ ε
  ε-sub⁻ (sub x x₁) with ε-split x
  ... | PEq.refl = ∙-id⁻ʳ x₁ , PEq.refl

  sub-ε⁻ : ∀ {xs ys zs} → xs - ε ≣ (ys ⇅ zs) → zs ≈ₐ xs × ys ≡ ε
  sub-ε⁻ (sub x x₁) with ε-split x₁
  ... | PEq.refl = ∙-id⁻ʳ x , PEq.refl

  xs-xs≡ε : ∀ {xs} → xs - xs ≣ ε
  xs-xs≡ε = sub ∙-idˡ ∙-idˡ

{- Exchange is a partial monoid -}
module _ where

  exchange-isMonoidˡ : IsPartialMonoidˡ _≈_ exchange-rel (εₐ ⇅ εₐ)

  IsPartialMonoidˡ.ε-uniq exchange-isMonoidˡ {u ⇅ d} (eq₁ , eq₂) with ε-unique {{r₁-monoid}} eq₁ | ε-unique {{r₂-monoid}} eq₂
  ... | PEq.refl | PEq.refl = PEq.refl

  IsPartialMonoidˡ.identityˡ exchange-isMonoidˡ = ex ε-sub sub-ε ∙-idˡ ∙-idʳ
  IsPartialMonoidˡ.identity⁻ˡ exchange-isMonoidˡ (ex x₁ x₂ σ₁ σ₂) with ε-sub⁻ x₁ | sub-ε⁻ x₂
  ... | ρ₁ , PEq.refl | ρ₂ , PEq.refl = trans (sym ρ₁) (∙-id⁻ˡ σ₁) , trans (sym ρ₂) (∙-id⁻ʳ σ₂)

  instance exchange-isMonoid : IsPartialMonoid _≈_ exchange-rel (εₐ ⇅ εₐ)
  exchange-isMonoid = IsPartialMonoidˡ.partialMonoidˡ exchange-isMonoidˡ

module _ where

  instance exchange-intuitive-down : IsIntuitionistic (λ where (u ⇅ d) → u ≡ εₐ) exchange-rel
  IsIntuitionistic.∙-copy exchange-intuitive-down {{PEq.refl}} = ex sub-ε sub-ε ∙-idˡ ∙-copy

module _ (P : Pred A ℓ) where

  Liftₓ : Pred (A × A) ℓ → Pred Account ℓ
  Liftₓ P (u ⇅ d) = P (u , d)

  data Down : Pred Account ℓ where
    ↓ : ∀ {x} → P x → Down (εₐ ⇅ x)

  data Up : Pred Account ℓ where
    ↑ : ∀ {x} → P x → Up (x ⇅ εₐ)

module _ where

  Up⁻ : Pred Account ℓ → Pred A ℓ
  Up⁻ P = P ∘ (_⇅ ε)

  Down⁻ : Pred Account ℓ → Pred A ℓ
  Down⁻ P = P ∘ (ε ⇅_)

module _ {P : Pred A ℓ} {{_ : Respect _≈ₐ_ P}} where

  instance ↓-respects : Respect _≈_ (Down P)
  Respect.coe ↓-respects x (↓ x₁) with ε-unique {{r₂-monoid}} (proj₁ x)
  ... | PEq.refl = ↓ (coe (proj₂ x) x₁)

  instance ↑-respects : Respect _≈_ (Up P)
  Respect.coe ↑-respects x (↑ x₁) with ε-unique {{r₁-monoid}} (proj₂ x)
  ... | PEq.refl = ↑ (coe (proj₁ x) x₁)

module _ where
  ups : ∀ {xs ys zs} → Exchange (xs ⇅ ε) (ys ⇅ ε) zs → ∃ λ xys → zs ≈ (xys ⇅ ε) × xs ∙₁ ys ≣ xys
  ups (ex x x₁ x₂ x₃) with ε-sub⁻ x | ε-sub⁻ x₁
  ... | eq₁ , PEq.refl | eq₂ , PEq.refl = -, (refl , reflexive (PEq.sym (ε∙ε x₃))) , coe eq₂ (coe eq₁ x₂)

  downs : ∀ {xs ys zs} → Exchange (ε ⇅ xs) (ε ⇅ ys) zs → ∃ λ xys → zs ≈ (ε ⇅ xys) × xs ∙₂ ys ≣ xys
  downs (ex x x₁ x₂ x₃) with sub-ε⁻ x | sub-ε⁻ x₁
  ... | eq₁ , PEq.refl | eq₂ , PEq.refl = -, (reflexive (PEq.sym (ε∙ε x₂)) , refl) , ∙-comm (coe eq₁ (coe eq₂ x₃))

  up-down=up : ∀ {xs ys zs} → (ε ⇅ xs) ∙ ys ≣ (zs ⇅ ε) → ∃ λ ys' →  ys ≈ (ys' ⇅ ε) × zs ∙₂ xs ≣ ys' 
  up-down=up (ex (sub x y) x₁ x₂ x₃) with sub-ε⁻ x₁
  ... | eq₁ , PEq.refl with ε-split x₃
  ... | PEq.refl = -, (refl , ≈-sym eq₁)  , coe (∙-id⁻ˡ x₂) (coe {{∙-respects-≈ʳ}} (∙-id⁻ˡ x) y)

module _ {P Q : Pred A ℓ} where
  zipUp : ∀[ (Up P) ⊙ (Up Q) ⇒ Up (P ⊙₁ Q) ]
  zipUp ((↑ px) ∙⟨ σ ⟩ (↑ qx)) = let _ , eq , σ↑ = ups σ in coe (≈-sym eq) (↑ (px ∙⟨ σ↑ ⟩ qx)) 

  zipDown : ∀[ (Down P) ⊙ (Down Q) ⇒ Down (P ⊙₂ Q) ]
  zipDown (↓ p ∙⟨ σ ⟩ ↓ q) = let _ , eq , σ↓ = downs σ in coe (≈-sym eq) (↓ (p ∙⟨ σ↓ ⟩ q))

module _ {P} where

  pure : ∀[ P ⇒ Up P ∘ (_⇅ ε) ] 
  pure px = ↑ px

module _ {P Q : Pred A ℓ} {{_ : Respect _≈ₐ_ Q}} where

  upMap : ∀[ Up (P ─⊙₁ Q) ⇒ (Up P ─⊙ Up Q) ]
  upMap (↑ f) ⟨ σ ⟩ ↑ px = let _ , eq , σ↑ = ups σ in coe (≈-sym eq) (↑ (f ⟨ σ↑ ⟩ px))

  _<*>_ : ∀[ Up (P ⇒ Q) ∘ (_⇅ ε) ] → ∀[ Up P ⇒ Up Q ]
  f <*> (↑ upx) = ↑ (case f of λ where (↑ f) → f upx)

  downMap : ∀[ Down (P ─⊙₂ Q) ⇒ (Down P ─⊙ Down Q) ]
  downMap (↓ f) ⟨ σ ⟩ ↓ px = let _ , eq , σ↓ = downs σ in coe (≈-sym eq) (↓ (f ⟨ σ↓ ⟩ px))
