open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Structures as Tern
open import Data.Product.Relation.Binary.Pointwise.NonDependent

module Relation.Ternary.Construct.RequiresEnsures
  {a} {A : Set a}

  (and : Rel₃ A)

  -- the relation between ∪ and -
  {{or  : Rel₃ A}} {{sub : Rel₃ A}}
  (or-sub-assocₗ  : LeftAssoc′ or sub)
  (or-sub-assocᵣ  : RightAssoc′ or sub)
  (or-sub-distribₗ : sub DistribOverₗ or)
  (or-sub-distribᵣ : sub DistribOverᵣ or)

  where

instance _ = and

open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Construct.Product

open Rel₃ or  using () renaming (_∙_≣_ to _∪_≣_)
open Rel₃ and using () renaming (_∙_≣_ to _∩_≣_)
open Rel₃ sub using () renaming (_∙_≣_ to _-_≣_)

{- Pairs of A for requires and ensures, and their equivalences -}
module _ where

  Conditions : Set a
  Conditions = A × A

  module Conditions (c : Conditions) where
    requires = proj₁ c
    ensures  = proj₂ c

{- Parallel composition -}
module _ where
  instance ∥-rel : Rel₃ Conditions
  ∥-rel = or ×-∙ or

{- Choice -}
module _ where
  instance ∣-rel : Rel₃ Conditions
  ∣-rel = or ×-∙ and

{- Sequential composition -}
module _ where

  record _▹_≣_ (cₗ : Conditions) (cᵣ : Conditions) (c : Conditions) : Set a where
    constructor seq
    open Conditions cₗ renaming (requires to r₁; ensures to e₁)
    open Conditions cᵣ renaming (requires to r₂; ensures to e₂)
    open Conditions c  renaming (requires to r ; ensures to e)

    -- (r₁ , e₁) ▹ (r₂ , e₂) = (r₁ ∪ (r₂ - e₁) , e₁ ∪ e₂)
    field
      {r₂′} : A
      subtract   : r₂ - e₁  ≣ r₂′
      seq-req    : r₁ ∪ r₂′ ≣ r
      seq-ens    : e₁ ∪ e₂  ≣ e

  instance ▹-rel : Rel₃ Conditions
  Rel₃._∙_≣_ ▹-rel = _▹_≣_

module _
  {ℓe} {_≈_ : A → A → Set ℓe}
  {{ -respectsʳ   : ∀ {a b} → Respect _≈_ (a -_≣ b) }}
  {{ -respectsˡ   : ∀ {a b} → Respect _≈_ (_- a ≣ b) }}
  {{ or-sg        : IsPartialSemigroup _≈_ or }}
  {{ or-comm      : IsCommutative or }}
  where

  assocᵣ : RightAssoc ▹-rel
  assocᵣ {r₁ , e₁} {r₂ , e₂} {r₁∪r₂-e₁ , e₁∪e₂} {r₃ , e₃} {r₁∪r₂-e₁∪r₃-es , e₁∪e₂∪e₃}
    record { subtract = s₁ ; seq-req = req₁ ; seq-ens = ens₁ }
    record { subtract = s₂ ; seq-req = req₂ ; seq-ens = ens₂ } =
      let
        _ , ens₃ , ens₄ = ∙-assocᵣ ens₁ ens₂
        _ , τ₁ , τ₂     = or-sub-assocₗ s₂ (∙-comm ens₁)
        _ , τ₃ , τ₄     = ∙-assocᵣ req₁ req₂
        _ , τ₅ , τ₆     = or-sub-distribₗ s₁ τ₂ τ₄
      in
      -, seq τ₆ τ₃ ens₃
       , seq τ₁ τ₅ ens₄

  assocₗ : LeftAssoc ▹-rel
  assocₗ {r₁ , e₁} {_} {r₂ , e₂} {r₃ , e₃} {abc}
    record { subtract = s₁ ; seq-req = req₁ ; seq-ens = ens₁ }
    record { subtract = s₂ ; seq-req = req₂ ; seq-ens = ens₂ } =
      let
        _ , ens₃ , ens₄ = ∙-assocₗ ens₁ ens₂
        _ , _ , τ₁ , τ₂ , τ₃ = or-sub-distribᵣ req₂ s₁
        _ , τ₄ , τ₅ = ∙-assocₗ req₁ τ₃
        τ₇ = or-sub-assocᵣ s₂ τ₂ (∙-comm ens₃)
      in
      -, seq τ₁ τ₄ ens₃
       , seq τ₇ τ₅ ens₄

  instance ▹-sg : IsPartialSemigroup (Pointwise _≈_ _≈_) ▹-rel

  Respect.coe (IsPartialSemigroup.∙-respects-≈ ▹-sg) (eq₁ , eq₂) (seq s₁ req ens) =
    seq s₁ (coe eq₁ req) (coe eq₂ ens)
  Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ ▹-sg) (eq₁ , eq₂) (seq s₁ req ens) =
    seq (coe eq₂ s₁) (coe eq₁ req) (coe eq₂ ens)
  Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ ▹-sg) (eq₁ , eq₂) (seq s₁ req ens) =
    seq (coe eq₁ s₁) req (coe eq₂ ens)

  IsPartialSemigroup.∙-assocᵣ ▹-sg = assocᵣ
  IsPartialSemigroup.∙-assocₗ ▹-sg = assocₗ

module ReqEnsJoinoid
  {e} {_≈_ : A → A → Set e}
  {{ -respectsʳ : ∀ {a b} → Respect _≈_ (a -_≣ b) }}
  {{ -respectsˡ : ∀ {a b} → Respect _≈_ (_- a ≣ b) }}

  {⊥               : A}
  {{ or-sg         : IsPartialMonoid _≈_ or ⊥ }}
  {_∨_} {{ or-tots : IsTotal or _∨_ }}
  {{ or-comm       : IsCommutative or }}
  {{ and-sg        : IsPartialSemigroup _≈_ and }}

  (∸-idʳ           : RightIdentity sub ⊥)
  (∸-id⁻ʳ          : RightIdentity⁻ _≈_ sub ⊥)
  (∸-zeroˡ         : LeftZero sub ⊥)
  (∸-zero⁻ˡ        : LeftZero⁻ _≈_ sub ⊥)
  (deMorganʳ       : DeMorganʳ sub and or)
  (or-and-distribᵣ : and DistribOverᵣ or)
  (∪-idem          : Idempotent or)
  where

  instance ▹-isPartialMonoid : IsPartialMonoid (Pointwise _≈_ _≈_) ▹-rel (⊥ , ⊥)

  IsPartialMonoid.ε-unique ▹-isPartialMonoid (eq₁ , eq₂) with ε-unique eq₁ | ε-unique eq₂
  ... | refl | refl = refl

  IsPartialMonoid.∙-idˡ ▹-isPartialMonoid = seq ∸-idʳ   ∙-idˡ ∙-idˡ
  IsPartialMonoid.∙-idʳ ▹-isPartialMonoid = seq ∸-zeroˡ ∙-idʳ ∙-idʳ

  IsPartialMonoid.∙-id⁻ˡ ▹-isPartialMonoid (seq s req ens) = ≈-trans (∸-id⁻ʳ s) (∙-id⁻ˡ req) , (∙-id⁻ˡ ens)
  IsPartialMonoid.∙-id⁻ʳ ▹-isPartialMonoid (seq s req ens) = ∙-id⁻ʳ (coe (∸-zero⁻ˡ s) req)   , (∙-id⁻ʳ ens)

  instance joinoid : IsJoinoid (Pointwise _≈_ _≈_) ▹-rel ∥-rel ∣-rel (⊥ , ⊥)

  IsJoinoid.▹-distrib-∣ʳ joinoid {a} {b} {c} {a∣b} {d} (pre , post) (seq s req ens) with deMorganʳ post s
  ... | cᵣ-aₑ , cᵣ-bₑ , τ₁ , τ₂ , τ₃ with resplit pre τ₃ req
  ... | _ , _ , τ₄ , τ₅ , τ₆ with or-and-distribᵣ post ens
  ... | _ , _ , τ₇ , τ₈ , τ₉ =
    -,
    -, seq τ₁ τ₄ τ₇
     , seq τ₂ τ₅ τ₈
     , (τ₆ , τ₉)

  IsJoinoid.∥-distrib-∣ʳ joinoid {a} {b} {c} {a∥b} {d} (pre₁ , post₁) (pre₂ , post₂)
    with resplit pre₁ ∪-idem pre₂ | or-and-distribᵣ post₁ post₂
  ... | _ , _ , τ₁ , τ₂ , τ₃ | _ , _ , τ₄ , τ₅ , τ₆
    = -,
    -, (τ₁ , τ₄)
     , (τ₂ , τ₅)
     , (τ₃ , τ₆)

