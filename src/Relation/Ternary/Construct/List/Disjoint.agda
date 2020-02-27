{-# OPTIONS --safe #-}
module Relation.Ternary.Construct.List.Disjoint {t} (T : Set t) where

open import Level
open import Data.Unit using (⊤)
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties

open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

private
  Ctx = List T
  variable
    xsˡ xsʳ xs ysˡ ysʳ ys : Ctx

open import Relation.Ternary.Construct.Empty T public
open import Relation.Ternary.Construct.List.Interdivide empty-rel as Disjoint
open Disjoint public using ([]; consˡ; consʳ) renaming
  (splits to disjoint-split
  ;list-emptiness to disjoint-empty
  ;split-positive to disjoint-positive
  ;split-isComm to disjoint-commutative
  ;split-isSemigroup to disjoint-semigroup
  ;split-isMonoid to disjoint-monoid
  ;split-isTotal to disjoint-total)

open Rel₃ Disjoint.splits using ()
  renaming (_∙_≣_ to _⊕_≣_; _⊙_ to _⊕_) public

_⊆_ : Ctx → Ctx → Set t
_⊆_ = _≤_

_∈_ : T → Ctx → Set t
x ∈ xs = [ x ] ⊆ xs

-- from the stdlib Interleaving properties
toPermutation : ∀ {l r as} → l ⊕ r ≣ as → as ↭ l ++ r
toPermutation [] = ↭-refl
toPermutation (consˡ σ) = prep _ (toPermutation σ)
toPermutation (consʳ {xs = xs} {ys} {zs} {z} σ) = begin
  z ∷ zs       ↭⟨ prep z (toPermutation σ) ⟩
  z ∷ xs ++ ys ↭⟨ ↭-sym (shift z xs ys) ⟩
  xs ++ z ∷ ys  ∎
  where 
    open PermutationReasoning

⊕-functional : ∀ {xs ys zs zs'}  → xs ⊕ ys ≣ zs → xs ⊕ ys ≣ zs' → zs ↭ zs'
⊕-functional σ₁ σ₂ = ↭-trans (toPermutation σ₁) (↭-sym (toPermutation σ₂))

{- We can pull a permutation through separation -}
-- postulate ↭-∙ˡ : xsˡ ⊕ xsʳ ≣ xs → xsˡ ↭ ysˡ → Σ[ ys ∈ Ctx ] ys ↭ xs × ysˡ ⊕ xsʳ ≣ ys

-- ↭-∙ʳ : xsˡ ⊕ xsʳ ≣ xs → xsʳ ↭ ysʳ → Σ[ ys ∈ Ctx ] ys ↭ xs × xsˡ ⊕ ysʳ ≣ ys
-- ↭-∙ʳ σ ρ with ↭-∙ˡ (∙-comm σ) ρ
-- ... | _ , ρ′ , σ′ = -, ρ′ , ∙-comm σ′

-- ↭-∙ : xsˡ ⊕ xsʳ ≣ xs → xsˡ ↭ ysˡ → xsʳ ↭ ysʳ → Σ[ ys ∈ Ctx ] ys ↭ xs × ysˡ ⊕ ysʳ ≣ ys
-- ↭-∙ σ ρ₁ ρ₂ with ↭-∙ˡ σ ρ₁
-- ... | _ , ρ₃ , σ₂ with ↭-∙ʳ σ₂ ρ₂
-- ... | _ , ρ₄ , σ₃ = -, ↭-trans ρ₄ ρ₃ , σ₃

{- We can push permutation through separation. -}
∙-↭ : xsˡ ⊕ xsʳ ≣ xs → xs ↭ ys →
         Σ[ yss ∈ Ctx × Ctx ]
         let (ysˡ , ysʳ) = yss in
         ysˡ ↭ xsˡ × ysʳ ↭ xsʳ × ysˡ ⊕ ysʳ ≣ ys
-- refl
∙-↭ σ refl = _ , ↭-refl , ↭-refl , σ

-- prep
∙-↭ (consˡ σ) (prep x ρ) with ∙-↭ σ ρ
... | _ , h₁ , h₂ , σ' = -, prep x h₁ , h₂ , consˡ σ'
∙-↭ (consʳ σ) (prep x ρ) with ∙-↭ σ ρ
... | _ , h₁ , h₂ , σ' = -, h₁ , prep x h₂ , consʳ σ'
∙-↭ (divide τ σ) (prep x ρ) with ∙-↭ σ ρ
... | _ , h₁ , h₂ , σ' = -, prep _ h₁ , prep _ h₂ , divide τ σ'

-- swap
-- todo, cleanup this proof?
∙-↭ (consˡ (consˡ σ)) (swap x y ρ) with ∙-↭ σ ρ
... | _ , h₁ , h₂ , σ' = -, swap y x h₁ , h₂ , consˡ (consˡ σ')
∙-↭ (consˡ (consʳ σ)) (swap x y ρ) with ∙-↭ σ ρ
... | _ , h₁ , h₂ , σ' = -, prep _ h₁ , prep _ h₂ , consʳ (consˡ σ')
∙-↭ (consˡ (divide τ σ)) (swap x y ρ) with ∙-↭ σ ρ
... | _ , h₁ , h₂ , σ'  = -, swap _ _ h₁ , prep _ h₂ , divide τ (consˡ σ')
∙-↭ (consʳ (consˡ σ)) (swap x y ρ) with ∙-↭ σ ρ
... | _ , h₁ , h₂ , σ' = -, prep _ h₁ , prep _ h₂ , consˡ (consʳ σ')
∙-↭ (consʳ (consʳ σ)) (swap x y ρ) with ∙-↭ σ ρ
... | _ , h₁ , h₂ , σ' = -, h₁ , swap y x h₂ , consʳ (consʳ σ')
∙-↭ (consʳ (divide τ σ)) (swap x y ρ) with ∙-↭ σ ρ
... | _ , h₁ , h₂ , σ' = -, prep _ h₁ , swap _ _ h₂ , divide τ (consʳ σ') 
∙-↭ (divide τ (consˡ σ)) (swap x y ρ) with ∙-↭ σ ρ
... | _ , h₁ , h₂ , σ' = -, swap _ _ h₁ , prep _ h₂ , consˡ (divide τ σ')
∙-↭ (divide τ (consʳ σ)) (swap x y ρ) with ∙-↭ σ ρ
... | _ , h₁ , h₂ , σ' = -, prep _ h₁ , swap _ _ h₂ , consʳ (divide τ σ')
∙-↭ (divide τ (divide τ' σ)) (swap x y ρ) with ∙-↭ σ ρ
... | _ , h₁ , h₂ , σ' = -, swap _ _ h₁ , swap _ _ h₂ , divide τ' (divide τ σ')

-- trans
∙-↭ σ (trans ρ₁ ρ₂) with ∙-↭ σ ρ₁
... | _ , h₁ , h₂ , σ₂ with ∙-↭ σ₂ ρ₂
... | _ , h₃ , h₄ , σ₃ = _ , trans h₃ h₁ , trans h₄ h₂ , σ₃

threeway : ∀ {a b c ab bc : List T} → a ∙ b ≣ ab → b ∙ c ≣ bc → ∃ λ abc → ab ∙ bc ≣ abc
threeway Split.[] σ₂ = -, ∙-idˡ
threeway (consˡ σ₁) σ₂ with threeway σ₁ σ₂
... | _ , σ₃ = -, consˡ σ₃
threeway σ₁@(consʳ _) (consʳ σ₂) with threeway σ₁ σ₂
... | _ , σ₃ = -, consʳ σ₃
threeway (consʳ σ₁) (consˡ σ₂) with threeway σ₁ σ₂
... | _ , σ₃ = -, consˡ (consʳ σ₃)
