{-# OPTIONS --safe #-}
-- The Exchange PRSA
--
-- This proof relevant separation algebra balances multiple "accounts"
-- that can /each/ both supply (/up/) and demand (/down/) some amount of an underlying
-- PRSA A.
-- At every node in the splitting tree, two accounts can "exchange" some amount,
-- meaning that the demand on the left can be fulfilled by some supply on the right and vice versa.

open import Relation.Unary using (U)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Algebra.Structures

module Relation.Ternary.Construct.Exchange {ℓ e s}
  {A : Set ℓ} {εₐ} {r₁ r₂} {_≈ₐ_ : A → A → Set e}
  {{r₁-monoid  : IsPartialMonoid _≈ₐ_ r₁ εₐ}}
  {{r₂-monoid  : IsPartialMonoid _≈ₐ_ r₂ εₐ}}
  {{r₁-positive  : IsPositiveWithZero s _≈ₐ_ r₁ εₐ}}
  {{r₂-positive  : IsPositiveWithZero s _≈ₐ_ r₂ εₐ}}
  {{εₐ-unique    : IsUnique _≈ₐ_ εₐ}}
  {{r₁-comm : IsCommutative r₁}}
  {{r₂-comm : IsCommutative r₂}}
  {_∙_}
  {{_ : IsTotal r₁ _∙_}}
  {{_ : IsTotal r₂ _∙_}}
  {{m : IsMonoid _≈ₐ_ _∙_ εₐ}}
  (xsplitₐ  : CrossSplit r₂ r₁)
  (uncrossₐ : Uncross r₁ r₂) where

open import Level hiding (Lift)
open import Data.Product hiding (_<*>_)
open import Data.Unit
open import Function using (case_of_; _∘_)

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
open import Relation.Ternary.Structures.Syntax hiding (_∙_)

open IsEquivalence (≈-equivalence {{IsPartialMonoid.isSemigroup r₁-monoid}})

private
  instance
    _ = r₁
    _ = r₂
  variable
    u₁ u₂ u₃ d₁ d₂ d₃ u d : A

open Rel₃ r₁ using () renaming (_∙_≣_ to _∙₁_≣_; _✴_ to _✴₁_; _─✴_ to _─✴₁_)
open Rel₃ r₂ using () renaming (_∙_≣_ to _∙₂_≣_; _✴_ to _✴₂_; _─✴_ to _─✴₂_)

module _ where

  -- Accounts are essentially pairs, but we rewrap 'm for instance search.
  record Account : Set ℓ where
    constructor _⇅_
    field
      up   : A
      down : A

    givePair : A × A
    givePair = up , down

  open Account public

module _ where

  open import Data.Product.Relation.Binary.Pointwise.NonDependent
  _≈_ : Account → Account → Set _
  a ≈ b = Pointwise _≈ₐ_ _≈ₐ_ (givePair a) (givePair b)

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

{- Total -}
module _ where

  _↟_ : Account → Account → Account
  (u₁ ⇅ d₁) ↟ (u₂ ⇅ d₂) = (u₁ ∙ u₂) ⇅ (d₁ ∙ d₂)

  instance exchange-isTotal : IsTotal exchange-rel _↟_
  IsTotal.∙-parallel exchange-isTotal (ex x₁ x₂ σ₁ σ₂) (ex x₃ x₄ σ₃ σ₄) =
    ex (sub-∙ x₁ x₃) (sub-∙ x₂ x₄) (∙-parallel σ₁ σ₃) (∙-parallel σ₂ σ₄)

    where
      sub-∙ : ∀ {d₁ d₂ u₁ u₂ u₁' u₂' d₁' d₂'} →
              (d₁ - u₁ ≣ (u₁' ⇅ d₁')) →
              (d₂ - u₂ ≣ (u₂' ⇅ d₂')) →
              (d₁ ∙ d₂) - (u₁ ∙ u₂) ≣ ((u₁' ∙ u₂') ⇅ (d₁' ∙ d₂'))
      sub-∙ (sub x x₁) (sub x₂ x₃) = sub (∙-parallel x x₂) (∙-parallel x₁ x₃)

  open IsMonoid {{...}}

  private
    acc-magma : IsMagma _≈_ _↟_
    IsMagma.isEquivalence acc-magma = account-equiv
    IsMagma.∙-cong acc-magma e₁ e₂ = ∙-cong (proj₁ e₁) (proj₁ e₂)
                                   , ∙-cong (proj₂ e₁) (proj₂ e₂)

    acc-semigroup : IsSemigroup _≈_ _↟_
    IsSemigroup.isMagma acc-semigroup = acc-magma
    IsSemigroup.assoc acc-semigroup x y z = assoc _ _ _ , assoc _ _ _

  instance acc-monoid : IsMonoid _≈_ _↟_ (εₐ ⇅ εₐ)
  IsMonoid.isSemigroup acc-monoid = acc-semigroup
  IsMonoid.identity acc-monoid = (λ x → (identityˡ _) , identityˡ _ )
                               , (λ x → (identityʳ _) , identityʳ _ )

{- "Identity laws" for the auxiliary exchange relation -}
module _ where

  instance exchange-emptiness : Emptiness (εₐ ⇅ εₐ)
  exchange-emptiness = record {}

  instance empty-unique : IsUnique _≈_ (εₐ ⇅ εₐ)
  IsUnique.unique empty-unique eq
    with PEq.refl ← unique (proj₁ eq) | PEq.refl ← unique (proj₂ eq) = PEq.refl

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

  no-sub : ∀ {xs ys} → xs - ys ≣ (ys ⇅ xs)
  no-sub = sub ∙-idʳ ∙-idʳ

{- Exchange is a partial monoid -}
module _ where

  exchange-isMonoidˡ : IsPartialMonoidˡ _≈_ exchange-rel (εₐ ⇅ εₐ)

  IsPartialMonoidˡ.identityˡ exchange-isMonoidˡ = ex ε-sub sub-ε ∙-idˡ ∙-idʳ
  IsPartialMonoidˡ.identity⁻ˡ exchange-isMonoidˡ (ex x₁ x₂ σ₁ σ₂) with ε-sub⁻ x₁ | sub-ε⁻ x₂
  ... | ρ₁ , PEq.refl | ρ₂ , PEq.refl = trans (sym ρ₁) (∙-id⁻ˡ σ₁) , trans (sym ρ₂) (∙-id⁻ʳ σ₂)

  instance exchange-isMonoid : IsPartialMonoid _≈_ exchange-rel (εₐ ⇅ εₐ)
  exchange-isMonoid = IsPartialMonoidˡ.partialMonoidˡ exchange-isMonoidˡ

module _ (P : Pred A ℓ) where

  Liftₓ : Pred (A × A) ℓ → Pred Account ℓ
  Liftₓ P (u ⇅ d) = P (u , d)

  data Down : Pred Account ℓ where
    ↓ : ∀ {x} → P x → Down (εₐ ⇅ x)

  data Up : Pred Account ℓ where
    ↑ : ∀ {x} → P x → Up (x ⇅ εₐ)

module DownIntuitive {{r₂-intuitive : IsContractive U r₂}} where

  instance exchange-intuitive-down : ∀ {P} → IsContractive (Down P) exchange-rel
  IsContractive.∙-copy exchange-intuitive-down (↓ _) = ex sub-ε sub-ε ∙-idˡ (∙-copy tt)

module _ where

  balance : ∀ {r} → ε[ Up (Own r) ✴ Down (Own r) ]
  balance = ↑ PEq.refl ∙⟨ ex xs-xs≡ε xs-xs≡ε ∙-idˡ ∙-idˡ ⟩ ↓ PEq.refl

module _ where

  Up⁻ : Pred Account ℓ → Pred A ℓ
  Up⁻ P = P ∘ (_⇅ ε)

  Down⁻ : Pred Account ℓ → Pred A ℓ
  Down⁻ P = P ∘ (ε ⇅_)

module _ {P : Pred A ℓ} {{_ : Respect _≈ₐ_ P}} where

  instance ↓-respects : Respect _≈_ (Down P)
  Respect.coe ↓-respects x (↓ x₁) with unique (proj₁ x)
  ... | PEq.refl = ↓ (coe (proj₂ x) x₁)

  instance ↑-respects : Respect _≈_ (Up P)
  Respect.coe ↑-respects x (↑ x₁) with unique (proj₂ x)
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

  liftUp : ∀ {xs ys zs} → xs ∙₁ ys ≣ zs → (xs ⇅ εₐ) ∙ (ys ⇅ εₐ) ≣ (zs ⇅ εₐ)
  liftUp σ = ex ε-sub ε-sub σ ∙-idˡ

module _ {P Q : Pred A ℓ} where
  zipUp : ∀[ (Up P) ✴ (Up Q) ⇒ Up (P ✴₁ Q) ]
  zipUp ((↑ px) ∙⟨ σ ⟩ (↑ qx)) = let _ , eq , σ↑ = ups σ in coe (≈-sym eq) (↑ (px ∙⟨ σ↑ ⟩ qx))

  unzipUp : ∀[ (Up (P ✴₁ Q)) ⇒ Up P ✴ Up Q ]
  unzipUp (↑ (px ∙⟨ σ ⟩ qx)) = (↑ px) Rel₃.∙⟨ (ex ε-sub ε-sub σ ∙-idʳ) ⟩ (↑ qx)

  zipDown : ∀[ (Down P) ✴ (Down Q) ⇒ Down (P ✴₂ Q) ]
  zipDown (↓ p ∙⟨ σ ⟩ ↓ q) = let _ , eq , σ↓ = downs σ in coe (≈-sym eq) (↓ (p ∙⟨ σ↓ ⟩ q))

module _ {P} where

  pure : ∀[ P ⇒ Up P ∘ (_⇅ ε) ]
  pure px = ↑ px

module _ {P Q : Pred A ℓ} {{_ : Respect _≈ₐ_ Q}} where

  upMap : ∀[ Up (P ─✴₁ Q) ⇒ (Up P ─✴ Up Q) ]
  upMap (↑ f) ⟨ σ ⟩ ↑ px = let _ , eq , σ↑ = ups σ in coe (≈-sym eq) (↑ (f ⟨ σ↑ ⟩ px))

  _<*>_ : ∀[ Up (P ⇒ Q) ∘ (_⇅ ε) ] → ∀[ Up P ⇒ Up Q ]
  f <*> (↑ upx) = ↑ (case f of λ where (↑ f) → f upx)

  downMap : ∀[ Down (P ─✴₂ Q) ⇒ (Down P ─✴ Down Q) ]
  downMap (↓ f) ⟨ σ ⟩ ↓ px = let _ , eq , σ↓ = downs σ in coe (≈-sym eq) (↓ (f ⟨ σ↓ ⟩ px))
  
module _ where
  open import Relation.Ternary.Functor

  instance up-functor : Functor Up
  Functor.fmap up-functor f (↑ px) = ↑ (f px)

  instance down-functor : Functor Down
  Functor.fmap down-functor f (↓ px) = ↓ (f px)
