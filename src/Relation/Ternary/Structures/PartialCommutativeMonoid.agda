{-# OPTIONS --safe #-}
module Relation.Ternary.Structures.PartialCommutativeMonoid
  {a e} {A : Set a} (_≈_ : A → A → Set e) where

open import Level
open import Relation.Unary
open import Relation.Binary.Structures

open import Function using (_∘_)
open import Data.Product

open import Relation.Ternary.Core using (Rel₃; Exactly)
open import Relation.Ternary.Structures.PartialCommutativeSemigroup _≈_
open import Relation.Ternary.Structures.PartialMonoid _≈_

record IsPartialCommutativeMonoid (rel : Rel₃ A) (unit : A) : Set (a ⊔ e) where
  open Rel₃ rel

  field
    overlap {{isPartialMonoid}} : IsPartialMonoid rel unit
    ∙-comm                      : Commutative rel

{- Smart constructor -}
pcm : ∀ {rel : Rel₃ A} {unit : A} →
      let open Rel₃ rel in
        {{pcsg     : IsPartialCommutativeSemigroup rel}}
      → (ε-unique : ∀[ _≈_ unit ⇒ Exactly unit ])
      → (idˡ  : ∀ {Φ} → unit ∙ Φ ≣ Φ)
      → (id⁻ˡ : ∀ {Φ} → ∀[ unit ∙ Φ ⇒ _≈_ Φ ])
      → IsPartialCommutativeMonoid rel unit
pcm {rel} {unit} ε-unique idˡ id⁻ˡ =
  record
    { isPartialMonoid = isPartialMonoid′
    ; ∙-comm          = ∙-comm }

  where
    open Rel₃ rel

    idʳ : ∀ {Φ} → Φ ∙ unit ≣ Φ
    idʳ = ∙-comm idˡ

    id⁻ʳ   : ∀ {Φ} → ∀[ Φ ∙ unit ⇒ _≈_ Φ ]
    id⁻ʳ = id⁻ˡ ∘ ∙-comm

    isPartialMonoid′ : IsPartialMonoid rel unit
    IsPartialMonoid.ε-unique isPartialMonoid′ = ε-unique
    IsPartialMonoid.∙-idˡ isPartialMonoid′ = idˡ
    IsPartialMonoid.∙-idʳ isPartialMonoid′ = idʳ
    IsPartialMonoid.∙-id⁻ˡ isPartialMonoid′ = id⁻ˡ
    IsPartialMonoid.∙-id⁻ʳ isPartialMonoid′ = id⁻ʳ

open IsPartialCommutativeMonoid {{...}} public
