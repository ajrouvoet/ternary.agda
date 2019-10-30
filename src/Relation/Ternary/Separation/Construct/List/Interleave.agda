{-# OPTIONS --safe #-}
module Relation.Ternary.Separation.Construct.List.Interleave {a} (A : Set a) where

open import Level
open import Data.Product
open import Data.List
open import Data.List.Properties using (++-isMonoid)
open import Data.List.Relation.Ternary.Interleaving.Propositional as I public
open import Data.List.Relation.Ternary.Interleaving.Properties
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Binary.Permutation.Inductive

open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary hiding (_∈_; _⊢_)
open import Relation.Ternary.Separation

private C = List A

instance separation : RawSep C
separation = record { _⊎_≣_ = Interleaving }

-- TODO add to stdlib
interleaving-assoc : ∀ {a b ab c abc : List A} →
          Interleaving a b ab → Interleaving ab c abc →
          ∃ λ bc → Interleaving a bc abc × Interleaving b c bc
interleaving-assoc l (consʳ r)         = let _ , p , q = interleaving-assoc l r in -, consʳ p , consʳ q
interleaving-assoc (consˡ l) (consˡ r) = let _ , p , q = interleaving-assoc l r in -, consˡ p , q
interleaving-assoc (consʳ l) (consˡ r) = let _ , p , q = interleaving-assoc l r in -, consʳ p , consˡ q
interleaving-assoc [] []               = [] , [] , []

instance list-has-sep : IsSep separation
list-has-sep = record
  { ⊎-comm = I.swap
  ; ⊎-assoc = interleaving-assoc
  }

instance list-is-unital : IsUnitalSep _ _
IsUnitalSep.isSep list-is-unital               = list-has-sep
IsUnitalSep.⊎-idˡ list-is-unital               = right (≡⇒≋ P.refl)
IsUnitalSep.⊎-id⁻ˡ list-is-unital []           = refl
IsUnitalSep.⊎-id⁻ˡ list-is-unital (refl ∷ʳ px) = cong (_ ∷_) (⊎-id⁻ˡ px)

instance list-has-concat : IsConcattative separation
IsConcattative._∙_ list-has-concat = _++_
IsConcattative.⊎-∙ₗ list-has-concat {Φₑ = []} ps = ps
IsConcattative.⊎-∙ₗ list-has-concat {Φₑ = x ∷ Φₑ} ps = consˡ (⊎-∙ₗ ps)

instance list-unitalsep : UnitalSep _
list-unitalsep = record
  { isUnitalSep = list-is-unital }

instance list-resource : MonoidalSep _
list-resource = record
  { sep = separation
  ; isSep = list-has-sep
  ; isUnitalSep   = list-is-unital
  ; isConcat      = list-has-concat
  ; monoid = ++-isMonoid }

instance list-positive : IsPositive separation ε
list-positive = record
  { ⊎-εˡ = λ where [] → refl }

-- instance list-has-crosssplit : HasCrossSplit separation

-- HasCrossSplit.cross list-has-crosssplit [] [] =
--   -, [] , [] , [] , []
-- HasCrossSplit.cross list-has-crosssplit (consˡ σ₁) (consˡ σ₂) with cross σ₁ σ₂
-- ... | _ , τ₁ , τ₂ , τ₃ , τ₄ = -, consˡ τ₁ , τ₂ , consˡ τ₃ , τ₄
-- HasCrossSplit.cross list-has-crosssplit (consˡ σ₁) (consʳ σ₂) with cross σ₁ σ₂
-- ... | _ , τ₁ , τ₂ , τ₃ , τ₄ = -, consʳ τ₁ , τ₂ , τ₃ , consˡ τ₄
-- HasCrossSplit.cross list-has-crosssplit (consʳ σ₁) (consˡ σ₂) with cross σ₁ σ₂
-- ... | _ , τ₁ , τ₂ , τ₃ , τ₄ = -, τ₁ , consˡ τ₂ , consʳ τ₃ , τ₄
-- HasCrossSplit.cross list-has-crosssplit (consʳ σ₁) (consʳ σ₂) with cross σ₁ σ₂
-- ... | _ , τ₁ , τ₂ , τ₃ , τ₄ = -, τ₁ , consʳ τ₂ , τ₃ , consʳ τ₄

-- HasCrossSplit.uncross list-has-crosssplit [] σ₂ σ₃ σ₄ with ⊎-id⁻ˡ σ₃ | ⊎-id⁻ˡ σ₄
-- ... | refl | refl = -, ⊎-idˡ , σ₂
-- HasCrossSplit.uncross list-has-crosssplit (consˡ σ₁) σ₂ σ₃ σ₄ = {!!}
-- HasCrossSplit.uncross list-has-crosssplit (consʳ σ₁) σ₂ σ₃ σ₄ = {!!}

-- HasCrossSplit.uncross list-has-crosssplit (consˡ σ₁) σ₂ (consˡ σ₃) σ₄ with uncross σ₁ σ₂ σ₃ σ₄
-- ... | _ , τ₁ , τ₂ = -, consˡ τ₁ , consˡ τ₂

-- HasCrossSplit.uncross list-has-crosssplit σ₁@(consˡ _) (consˡ σ₂) (consʳ σ₃) σ₄ with uncross σ₁ σ₂ σ₃ σ₄
-- ... | _ , τ₁ , τ₂ = -, consʳ τ₁ , consˡ τ₂

-- HasCrossSplit.uncross list-has-crosssplit (consˡ σ₁) (consʳ σ₂) (consʳ σ₃) (consˡ σ₄) = {!!}
-- HasCrossSplit.uncross list-has-crosssplit (consˡ σ₁) (consʳ σ₂) (consʳ σ₃) (consʳ σ₄) = {!!}
-- HasCrossSplit.uncross list-has-crosssplit (consʳ σ₁) σ₂ σ₃ σ₄ = {!!}


-- HasCrossSplit.uncross list-has-crosssplit [] σ₂ σ₃ σ₄ with ⊎-id⁻ˡ σ₃ | ⊎-id⁻ˡ σ₄
-- ... | refl | refl = -, ⊎-idˡ , σ₂
-- HasCrossSplit.uncross list-has-crosssplit (consˡ σ₁) σ₂ σ₃ σ₄ = {!!}
-- HasCrossSplit.uncross list-has-crosssplit (consʳ σ₁) σ₂ σ₃ σ₄ = {!!}

-- HasCrossSplit.uncross list-has-crosssplit σ₁ σ₂ [] with ⊎-id⁻ˡ σ₂ | ⊎-id⁻ʳ σ₁
-- ... | refl | refl = -, ⊎-∙ , ⊎-idˡ
-- HasCrossSplit.uncross list-has-crosssplit (consˡ σ₁) σ₂ σ@(consˡ _) with uncross σ₁ σ₂ σ
-- ... | _ , σ₃ , σ₄ = -, consˡ σ₃ , consʳ σ₄
-- HasCrossSplit.uncross list-has-crosssplit (consʳ σ₁) σ₂ (consˡ σ)   with uncross σ₁ σ₂ σ
-- ... | _ , σ₃ , σ₄ = -, consˡ σ₃ , consˡ σ₄
-- HasCrossSplit.uncross list-has-crosssplit σ₁ (consˡ σ₂) (consʳ σ)   with uncross σ₁ σ₂ σ
-- ... | _ , σ₃ , σ₄ = -, consʳ σ₃ , consˡ σ₄
-- HasCrossSplit.uncross list-has-crosssplit σ₁ (consʳ σ₂) σ@(consʳ _) with uncross σ₁ σ₂ σ
-- ... | _ , σ₃ , σ₄ = -, consʳ σ₃ , consʳ σ₄
