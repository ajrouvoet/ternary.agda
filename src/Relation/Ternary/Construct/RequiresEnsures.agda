open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Structures as Tern

module Relation.Ternary.Construct.RequiresEnsures
  {a ℓe} {A : Set a}
  {_≈_ : A → A → Set ℓe} {{_ : IsEquivalence _≈_}}

  (and : Rel₃ A)

  -- the relation between ∪ and -
  {or  : Rel₃ A} {sub : Rel₃ A}
  (or-sub-assocₗ  : LeftAssoc′ or sub)
  (or-sub-assocᵣ  : RightAssoc′ or sub)
  (or-sub-distribₗ : Distribₗ or sub)
  (or-sub-distribᵣ : Distribᵣ or sub)

  where

open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality

open Rel₃ or  using () renaming (_∙_≣_ to _∪_≣_)
open Rel₃ and using () renaming (_∙_≣_ to _∩_≣_)
open Rel₃ sub using () renaming (_∙_≣_ to _-_≣_)

{- Pairs of A for requires and ensures, and their equivalences -}
module _ where

  record Conditions : Set a where
    constructor _▸_
    field
      requires : A
      ensures  : A
      
  -- lift the equivalence
  _≈c_ : Conditions → Conditions → Set ℓe
  (r₁ ▸ e₁) ≈c (r₂ ▸ e₂) = r₁ ≈ r₂ × e₁ ≈ e₂

  instance ≈c-equiv : IsEquivalence _≈c_
  IsEquivalence.refl ≈c-equiv  = ≈-refl , ≈-refl
  IsEquivalence.sym ≈c-equiv   (req , eeq) = ≈-sym req , ≈-sym eeq
  IsEquivalence.trans ≈c-equiv (req₁ , eeq₁) (req₂ , eeq₂) = ≈-trans req₁ req₂ , ≈-trans eeq₁ eeq₂

{- Parallel composition -}
module _ where

  record _∥_≣_ (cₗ : Conditions) (cᵣ : Conditions) (c : Conditions) : Set a where
    constructor par
    open Conditions cₗ renaming (requires to r₁; ensures to e₁)
    open Conditions cᵣ renaming (requires to r₂; ensures to e₂)
    open Conditions c  renaming (requires to r ; ensures to e)

    -- (r₁ , e₁) ∥ (r₂ , e₂) = (r₁ ∪ r₂ , e₁ ∩ e₂)
    field
      par-req    : r₁ ∪ r₂ ≣ r
      par-ens    : e₁ ∩ e₂ ≣ e

  ∥-rel : Rel₃ Conditions
  Rel₃._∙_≣_ ∥-rel = _∥_≣_

  open Rel₃ ∥-rel using () renaming (_⊙_ to _∥_) public

module _
  {{ or-sg  : IsPartialSemigroup {_≈_ = _≈_} or }}
  {{ and-sg : IsPartialSemigroup {_≈_ = _≈_} and }} where

  instance ∥-sg : IsPartialSemigroup {_≈_ = _≈c_} ∥-rel

  Respect.coe (IsPartialSemigroup.∙-respects-≈ ∥-sg) (eq₁ , eq₂) (par req ens) =
    par (coe eq₁ req) (coe eq₂ ens)
  Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ ∥-sg) (eq₁ , eq₂) (par req ens) =
    par (coe eq₁ req) (coe eq₂ ens)
  Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ ∥-sg) (eq₁ , eq₂) (par req ens) =
    par (coe eq₁ req) (coe eq₂ ens)

  IsPartialSemigroup.∙-assocᵣ ∥-sg (par σ₁₁ σ₁₂) (par σ₂₁ σ₂₂) =
    let
      _ , τ₁₁ , τ₁₂ = ∙-assocᵣ σ₁₁ σ₂₁
      _ , τ₂₁ , τ₂₂ = ∙-assocᵣ σ₁₂ σ₂₂
    in -, par τ₁₁ τ₂₁ , par τ₁₂ τ₂₂

  IsPartialSemigroup.∙-assocₗ ∥-sg (par σ₁₁ σ₁₂) (par σ₂₁ σ₂₂) =
    let
      _ , τ₁₁ , τ₁₂ = ∙-assocₗ σ₁₁ σ₂₁
      _ , τ₂₁ , τ₂₂ = ∙-assocₗ σ₁₂ σ₂₂
    in -, par τ₁₁ τ₂₁ , par τ₁₂ τ₂₂

module _
  {⊥ ⊤}
  {{ or-sg  : IsPartialMonoid {_≈_ = _≈_} or ⊥ }}
  {{ and-sg : IsPartialMonoid {_≈_ = _≈_} and ⊤ }} where

  instance ∥-monoid : IsPartialMonoid {_≈_ = _≈c_} ∥-rel (⊥ ▸ ⊤)

  IsPartialMonoid.ε-unique ∥-monoid (eq₁ , eq₂) with ε-unique eq₁ | ε-unique eq₂
  ... | refl | refl = refl

  IsPartialMonoid.∙-idˡ ∥-monoid = par ∙-idˡ ∙-idˡ
  IsPartialMonoid.∙-idʳ ∥-monoid = par ∙-idʳ ∙-idʳ

  IsPartialMonoid.∙-id⁻ˡ ∥-monoid (par σ₁ σ₂) = (∙-id⁻ˡ σ₁) , (∙-id⁻ˡ σ₂)
  IsPartialMonoid.∙-id⁻ʳ ∥-monoid (par σ₁ σ₂) = (∙-id⁻ʳ σ₁) , (∙-id⁻ʳ σ₂)

module _
  {{ or-comm  : IsCommutative {_≈_ = _≈_} or }}
  {{ and-comm : IsCommutative {_≈_ = _≈_} and }}
  where

  instance comm : IsCommutative {_≈_ = _≈c_} ∥-rel
  IsCommutative.∙-comm comm (par σ₁ σ₂) = par (∙-comm σ₁) (∙-comm σ₂)

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

  ▹-rel : Rel₃ Conditions
  Rel₃._∙_≣_ ▹-rel = _▹_≣_

  open Rel₃ ▹-rel using () renaming (_⊙_ to _▹_) public

module _
  {{ -respectsʳ   : ∀ {a b} → Respect _≈_ (a -_≣ b) }}
  {{ -respectsˡ   : ∀ {a b} → Respect _≈_ (_- a ≣ b) }}
  {{ or-sg        : IsPartialSemigroup {_≈_ = _≈_} or }}
  {{ or-comm      : IsCommutative {_≈_ = _≈_} or }}
  where
  
  assocᵣ : RightAssoc {_≈_ = _≈c_} ▹-rel
  assocᵣ {r₁ ▸ e₁} {r₂ ▸ e₂} {r₁∪r₂-e₁ ▸ e₁∪e₂} {r₃ ▸ e₃} {r₁∪r₂-e₁∪r₃-es ▸ e₁∪e₂∪e₃}
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

  assocₗ : LeftAssoc {_≈_ = _≈c_} ▹-rel
  assocₗ {r₁ ▸ e₁} {_} {r₂ ▸ e₂} {r₃ ▸ e₃} {abc}
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

  instance ▹-sg : IsPartialSemigroup {_≈_ = _≈c_} ▹-rel

  Respect.coe (IsPartialSemigroup.∙-respects-≈ ▹-sg) (eq₁ , eq₂) (seq s₁ req ens) =
    seq s₁ (coe eq₁ req) (coe eq₂ ens)
  Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ ▹-sg) (eq₁ , eq₂) (seq s₁ req ens) =
    seq (coe eq₂ s₁) (coe eq₁ req) (coe eq₂ ens)
  Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ ▹-sg) (eq₁ , eq₂) (seq s₁ req ens) =
    seq (coe eq₁ s₁) req (coe eq₂ ens)

  IsPartialSemigroup.∙-assocᵣ ▹-sg = assocᵣ
  IsPartialSemigroup.∙-assocₗ ▹-sg = assocₗ
