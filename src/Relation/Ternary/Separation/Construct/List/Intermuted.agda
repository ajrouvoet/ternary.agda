{-# OPTIONS --safe #-}
module Relation.Ternary.Separation.Construct.List.Intermuted {a} (A : Set a) where

open import Level
open import Data.Product
open import Data.List
open import Data.List.Properties using (++-isMonoid)
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Data.List.Relation.Binary.Permutation.Inductive

open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary hiding (_∈_; _⊢_)
open import Relation.Ternary.Separation

private 
  Carrier = List A
  variable
    xsˡ xsʳ xs ys ysˡ ysʳ zs xxs yys : Carrier

open import Relation.Ternary.Separation.Construct.List.Interleave A

data Permuted : ∀ (l r : Carrier) → Carrier → Set a where
  hustle : xsˡ ⊎ xsʳ ≣ xs → xs ↭ ys → Permuted xsˡ xsʳ ys

-- we can push permutation through separation
lemmaˡ : xsˡ ⊎ xsʳ ≣ xs → xs ↭ ys →
         Σ[ yss ∈ Carrier × Carrier ]
         let (ysˡ , ysʳ) = yss in
         ysˡ ↭ xsˡ × ysʳ ↭ xsʳ × ysˡ ⊎ ysʳ ≣ ys
lemmaˡ σ refl = _ , ↭-refl , ↭-refl , σ

lemmaˡ (consˡ σ) (prep x ρ) with lemmaˡ σ ρ
... | _ , h₁ , h₂ , σ' = -, prep x h₁ , h₂ , consˡ σ'
lemmaˡ (consʳ σ) (prep x ρ) with lemmaˡ σ ρ
... | _ , h₁ , h₂ , σ' = -, h₁ , prep x h₂ , consʳ σ'

lemmaˡ (consˡ (consˡ σ)) (_↭_.swap x y ρ) with lemmaˡ σ ρ
... | _ , h₁ , h₂ , σ' = _ , _↭_.swap y x h₁ , h₂ , consˡ (consˡ σ')
lemmaˡ (consˡ (consʳ σ)) (_↭_.swap x y ρ) with lemmaˡ σ ρ
... | _ , h₁ , h₂ , σ' = _ , prep _ h₁ , prep _ h₂ , consʳ (consˡ σ')
lemmaˡ (consʳ (consˡ σ)) (_↭_.swap x y ρ) with lemmaˡ σ ρ
... | _ , h₁ , h₂ , σ' = _ , prep _ h₁ , prep _ h₂ , consˡ (consʳ σ')
lemmaˡ (consʳ (consʳ σ)) (_↭_.swap x y ρ) with lemmaˡ σ ρ
... | _ , h₁ , h₂ , σ' = _ , h₁ , _↭_.swap y x h₂ , consʳ (consʳ σ')

lemmaˡ σ (trans ρ₁ ρ₂) with lemmaˡ σ ρ₁
... | _ , h₁ , h₂ , σ₂ with lemmaˡ σ₂ ρ₂
... | _ , h₃ , h₄ , σ₃ = _ , _↭_.trans h₃ h₁ , _↭_.trans h₄ h₂ , σ₃

-- we can pull permutations (on one side) through separation
lemmaʳ : xsˡ ⊎ xsʳ ≣ xs → xsˡ ↭ ysˡ → ∃ λ ys → ysˡ ⊎ xsʳ ≣ ys × xs ↭ ys

-- non-intersting cases
lemmaʳ []        ρ = -, ⊎-idʳ , ρ
lemmaʳ (consʳ σ) ρ with lemmaʳ σ ρ
... | _ , σ' , ρ' = -, consʳ σ' , prep _ ρ'
lemmaʳ (consˡ σ) refl =
  -, consˡ σ , refl

lemmaʳ (consˡ σ) (prep x ρ) with lemmaʳ σ ρ
... | _ , σ' , ρ' = -, consˡ σ' , prep _ ρ'

lemmaʳ (consˡ (consˡ σ)) (_↭_.swap x y ρ) with lemmaʳ σ ρ
... | _ , σ' , ρ' = -, consˡ (consˡ σ') , _↭_.swap x y ρ'

lemmaʳ (consˡ (consʳ σ)) ρ@(_↭_.swap x y _) with lemmaʳ (consˡ σ) ρ
... | _ , σ' , ρ' = -, consʳ σ' , _↭_.trans (_↭_.swap _ _ refl) (prep _ ρ')

lemmaʳ σ@(consˡ _) (_↭_.trans ρ₁ ρ₂) with lemmaʳ σ ρ₁
... | _ , σ' , ρ' with lemmaʳ σ' ρ₂
... | _ , σ'' , ρ'' = -, σ'' , _↭_.trans ρ' ρ''

instance
  hustle-sep : RawSep Carrier
  hustle-sep = record { _⊎_≣_ = Permuted }

  hustle-is-sep : IsSep hustle-sep
  IsSep.⊎-comm  hustle-is-sep (hustle σ h) = hustle (⊎-comm σ) h
  IsSep.⊎-assoc hustle-is-sep (hustle σ₁ h₁) (hustle σ₂ h₂) with lemmaˡ σ₁ h₁
  ... | _ , h₃ , h₄ , σ₃ =
    let
      _ , σ₄ , σ₅ = ⊎-assoc σ₃ σ₂
      _ , σ₆ , h₅ = lemmaʳ σ₅ h₄
      _ , σ₇ , h₆ = lemmaʳ σ₄ h₃
    in -, hustle σ₇ (↭-trans (↭-sym h₆) h₂) , hustle σ₆ (↭-sym h₅)
