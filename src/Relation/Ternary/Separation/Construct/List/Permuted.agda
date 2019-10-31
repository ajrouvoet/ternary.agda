{-# OPTIONS --safe #-}
module Relation.Ternary.Separation.Construct.List.Permuted {a} (A : Set a) where

open import Level
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Properties using (++-isMonoid)
open import Data.List.Relation.Ternary.Interleaving.Propositional using (consˡ; consʳ)
open import Data.List.Relation.Binary.Permutation.Inductive
open import Data.List.Relation.Binary.Permutation.Inductive.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Relation.Unary hiding (_∈_; _⊢_)
open import Relation.Ternary.Separation

private 
  Carrier = List A
  variable
    xsˡ xsʳ xs ys ysˡ ysʳ zs xxs yys : Carrier

open import Relation.Ternary.Separation.Construct.List.Interleave A hiding (swap)
module Cr = HasCrossSplit

Hustle : (l r t : Carrier) → Set a
Hustle l r t = (l ++ r) ↭ t

↭-[] : xs ↭ [] → xs ≡ []
↭-[] refl = refl
↭-[] (trans p q) with ↭-[] q
... | refl with ↭-[] p
... | refl = refl

++≡[] : xs ++ ys ≡ [] → xs ≡ []
++≡[] {[]} {.[]} refl = refl

instance
  hustle-sep : RawSep Carrier
  hustle-sep = record { _⊎_≣_ = Hustle }

  hustle-is-sep : IsSep hustle-sep
  IsSep.⊎-comm  hustle-is-sep {Φ₁} {Φ₂} h = trans (++-comm Φ₂ Φ₁) h
  IsSep.⊎-assoc hustle-is-sep {a} {b} {ab} {c} {abc} h₁ h₂ =
    b ++ c
    , trans (trans (↭-sym (++-assoc a b c)) (++⁺ʳ c h₁)) h₂
    , refl

  hustle-is-concat : HasConcat hustle-sep
  hustle-is-concat = record { _∙_ = _++_ ; ⊎-∙ₗ = λ where
    {Φ₁} {Φ₂} σ → trans (++-assoc _ Φ₁ Φ₂) (++⁺ˡ _ σ) }

  hustle-has-cross : HasCrossSplit hustle-sep

  Cr.cross hustle-has-cross {a} {b} {c} {d} {[]} h₁ h₂ with ↭-[] h₁ | ↭-[] h₂
  Cr.cross hustle-has-cross {[]} {[]} {[]} {[]} {[]} h₁ h₂ | eq₁ | eq₂ =
    ([] , [] , [] , []) , refl , refl , refl , refl
  Cr.cross hustle-has-cross {a} {b} {c} {d} {x ∷ z} h₁ h₂ = -, {!!} , {!!} , {!!} , {!!}

  Cr.uncross hustle-has-cross σ₁ σ₂ σ₃ σ₄ = {!!}
