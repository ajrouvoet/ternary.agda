{-# OPTIONS --safe #-}
module Relation.Ternary.Separation.Construct.List.Intermuted {a} (A : Set a) where

open import Level
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Properties using (++-isMonoid)
open import Data.List.Relation.Ternary.Interleaving.Propositional using (consˡ; consʳ)
open import Data.List.Relation.Binary.Permutation.Inductive
open import Data.List.Relation.Binary.Permutation.Inductive.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty

{- Missing std lib lemmas -}
module _ where
  ↭-[] : ∀ {a} {A : Set a} {xs : List A} → xs ↭ [] → xs ≡ []
  ↭-[] refl = refl
  ↭-[] (trans p q) with ↭-[] q
  ... | refl with ↭-[] p
  ... | refl = refl

  open import Relation.Nullary

  ¬∷↭[] : ∀ {a} {A : Set a} {x : A} {xs} → ¬ ((x ∷ xs) ↭ [])
  ¬∷↭[] (trans s₁ s₂) with ↭-[] s₂
  ... | refl = ¬∷↭[] s₁

open import Relation.Unary hiding (_∈_; _⊢_)
open import Relation.Ternary.Separation

private 
  Carrier = List A
  variable
    xsˡ xsʳ xs ys ysˡ ysʳ zs xxs yys : Carrier

open import Relation.Ternary.Separation.Construct.List.Interleave A hiding (swap)
module Cr = HasCrossSplit

module _ where
  {- An inductive definition of xs ++ ys ↭ zs -}
  data Hustle : ∀ (l r : Carrier) → Carrier → Set a where
    hustle : (σ : xsˡ ⊎ xsʳ ≣ xs) → (h : xs ↭ ys) → Hustle xsˡ xsʳ ys

  comm : ∀ {l r t} → Hustle l r t → Hustle r l t
  comm (hustle σ h) = hustle (⊎-comm σ) h

  {- The semantics of hustle -}
  ⟦_⟧ : Hustle xsˡ xsʳ xs → xs ↭ xsˡ ++ xsʳ
  ⟦ hustle σ h ⟧ = trans (↭-sym h) (toPermutation σ)

{- Permutations commute with interleavings -}
module _ where

  {- We can push permutation through separation. -}
  ⊎-↭ : xsˡ ⊎ xsʳ ≣ xs → xs ↭ ys →
           Σ[ yss ∈ Carrier × Carrier ]
           let (ysˡ , ysʳ) = yss in
           ysˡ ↭ xsˡ × ysʳ ↭ xsʳ × ysˡ ⊎ ysʳ ≣ ys
  -- refl
  ⊎-↭ σ refl = _ , ↭-refl , ↭-refl , σ

  -- prep
  ⊎-↭ (consˡ σ) (prep x ρ) with ⊎-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = -, prep x h₁ , h₂ , consˡ σ'
  ⊎-↭ (consʳ σ) (prep x ρ) with ⊎-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = -, h₁ , prep x h₂ , consʳ σ'

  -- swap
  ⊎-↭ (consˡ (consˡ σ)) (swap x y ρ) with ⊎-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = _ , swap y x h₁ , h₂ , consˡ (consˡ σ')
  ⊎-↭ (consˡ (consʳ σ)) (swap x y ρ) with ⊎-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = _ , prep _ h₁ , prep _ h₂ , consʳ (consˡ σ')
  ⊎-↭ (consʳ (consˡ σ)) (swap x y ρ) with ⊎-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = _ , prep _ h₁ , prep _ h₂ , consˡ (consʳ σ')
  ⊎-↭ (consʳ (consʳ σ)) (swap x y ρ) with ⊎-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = _ , h₁ , swap y x h₂ , consʳ (consʳ σ')

  -- trans
  ⊎-↭ σ (trans ρ₁ ρ₂) with ⊎-↭ σ ρ₁
  ... | _ , h₁ , h₂ , σ₂ with ⊎-↭ σ₂ ρ₂
  ... | _ , h₃ , h₄ , σ₃ = _ , trans h₃ h₁ , trans h₄ h₂ , σ₃

  {- We can pull permutations (on the left side) through separation. -}
  ↭-⊎ʳ : xsˡ ⊎ xsʳ ≣ xs → xsˡ ↭ ysˡ → ∃ λ ys → ysˡ ⊎ xsʳ ≣ ys × xs ↭ ys

  -- non-intersting cases
  ↭-⊎ʳ []        ρ = -, ⊎-idʳ , ρ
  ↭-⊎ʳ (consʳ σ) ρ with ↭-⊎ʳ σ ρ
  ... | _ , σ' , ρ' = -, consʳ σ' , prep _ ρ'
  ↭-⊎ʳ (consˡ σ) refl =
    -, consˡ σ , refl

  -- consˡ: the interesting case
  ↭-⊎ʳ (consˡ σ) (prep x ρ) with ↭-⊎ʳ σ ρ
  ... | _ , σ' , ρ' = -, consˡ σ' , prep _ ρ'

  ↭-⊎ʳ (consˡ (consˡ σ)) (swap x y ρ) with ↭-⊎ʳ σ ρ
  ... | _ , σ' , ρ' = -, consˡ (consˡ σ') , swap x y ρ'

  ↭-⊎ʳ (consˡ (consʳ σ)) ρ@(swap x y _) with ↭-⊎ʳ (consˡ σ) ρ
  ... | _ , σ' , ρ' = -, consʳ σ' , trans (swap _ _ refl) (prep _ ρ')

  ↭-⊎ʳ σ@(consˡ _) (trans ρ₁ ρ₂) with ↭-⊎ʳ σ ρ₁
  ... | _ , σ' , ρ' with ↭-⊎ʳ σ' ρ₂
  ... | _ , σ'' , ρ'' = -, σ'' , trans ρ' ρ''

  {- We can pull permutations (on the left side) through separation. -}
  ↭-⊎ˡ : xsˡ ⊎ xsʳ ≣ xs → xsʳ ↭ ysʳ → ∃ λ ys → xsˡ ⊎ ysʳ ≣ ys × xs ↭ ys
  ↭-⊎ˡ σ h with ↭-⊎ʳ (⊎-comm σ) h
  ... | _ , σ' , h' = -, ⊎-comm σ' , h' 

  {- We can pull permutations (on both sides) through separation. -}
  ↭-⊎ : xsˡ ⊎ xsʳ ≣ xs → xsˡ ↭ ysˡ → xsʳ ↭ ysʳ → ∃ λ ys → ysˡ ⊎ ysʳ ≣ ys × xs ↭ ys
  ↭-⊎ σ h₁ h₂ with ↭-⊎ʳ σ h₁
  ... | _ , σ'  , ρ with ↭-⊎ˡ σ' h₂
  ... | _ , σ'' , ρ' = -, σ'' , trans ρ ρ'

{- The identity laws for hustle, with respect to permutations -}
module _ where
  hustle-ε⁻ˡ : ∀ {xs ys} → Hustle ε xs ys → ys ↭ xs
  hustle-ε⁻ˡ (hustle σ h) with ⊎-id⁻ˡ σ
  ... | refl = ↭-sym h

  hustle-ε⁻ʳ : ∀ {xs ys} → Hustle xs ε ys → ys ↭ xs
  hustle-ε⁻ʳ (hustle σ h) with ⊎-id⁻ʳ σ
  ... | refl = ↭-sym h

  hustle-ε : ∀ {a b} → Hustle a b [] → a ≡ [] × b ≡ []
  hustle-ε (hustle σ h) with ↭-[] h
  ... | refl = ⊎-ε σ

{- Hustle is a separation logic -}
instance
  hustle-sep : RawSep Carrier
  hustle-sep = record { _⊎_≣_ = Hustle }

  hustle-is-sep : IsSep hustle-sep
  IsSep.⊎-comm  hustle-is-sep = comm
  IsSep.⊎-assoc hustle-is-sep (hustle σ₁ h₁) (hustle σ₂ h₂) with ⊎-↭ σ₁ h₁
  ... | _ , h₃ , h₄ , σ₃ =
    let
      _ , σ₄ , σ₅ = ⊎-assoc σ₃ σ₂
      _ , σ₆ , h₅ = ↭-⊎ʳ σ₅ h₄
      _ , σ₇ , h₆ = ↭-⊎ʳ σ₄ h₃
    in -, hustle σ₇ (↭-trans (↭-sym h₆) h₂) , hustle σ₆ (↭-sym h₅)

  hustle-has-cross : HasCrossSplit hustle-sep

  hustle-has-concat : IsConcattative hustle-sep
  hustle-has-concat = record
    { _∙_  = _++_
    ; ⊎-∙ₗ = λ where (hustle σ h) → hustle (⊎-∙ₗ σ) (++⁺ˡ _ h) }

  Cr.cross hustle-has-cross (hustle σ₁ h₁) (hustle σ₂ h₂) with ⊎-↭ σ₁ (trans h₁ (↭-sym h₂))
  ... | _ , h₃ , h₄ , σ₃ with ⊎-cross σ₃ σ₂
  ... | _ , τ₁ , τ₂ , τ₃ , τ₄ = -, hustle τ₁ h₃ , hustle τ₂ h₄ , hustle τ₃ refl , hustle τ₄ refl

  Cr.uncross hustle-has-cross {a} {b} {c} {d} {ac} {ad} {bc} {bd} σ₁ σ₂ σ₃ σ₄ =
    -, hustle ⊎-∙ refl
     , hustle ⊎-∙ (
       let ρ₁ = ⟦ σ₁ ⟧; ρ₂ = ⟦ σ₂ ⟧
           ρ₃ = ⟦ σ₃ ⟧; ρ₄ = ⟦ σ₄ ⟧ 
           a++b = ++⁺ ρ₁ ρ₂
           c++d = ++⁺ ρ₃ ρ₄
           q = trans a++b (↭-sym (++-assoc (ac ++ ad) bc bd)) 
           r = trans q (++⁺ʳ bd (trans (++-assoc ac ad bc) (++⁺ˡ ac (++-comm ad bc))) )
           s = trans r (++-assoc ac (bc ++ ad) bd)
           t = trans s (++⁺ˡ ac (++-assoc bc ad bd))
           u = trans t (↭-sym (++-assoc ac bc (ad ++ bd)))
       in trans c++d (↭-sym u)
     )
