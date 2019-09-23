open import Relation.Unary hiding (_∈_)
open import Data.List
open import Data.Product

module Relation.Unary.Separation.Monad.Market {ℓ} {T : Set ℓ} 
  {V : List T → Pred (List T) ℓ} 
  where

open import Level hiding (Lift)
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
import Relation.Binary.HeterogeneousEquality as HEq
open import Relation.Unary.PredicateTransformer hiding (_⊔_; [_])
open import Relation.Unary.Separation
open import Relation.Unary.Separation.Construct.List
open import Relation.Unary.Separation.Construct.Product
open import Relation.Unary.Separation.Construct.Market
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad

open import Data.Unit
open import Data.List.Relation.Ternary.Interleaving.Propositional as I

private
  ST = List T

module _ where

  -- typed stores in auth
  Cells : Pred (ST × ST) ℓ
  Cells = Bigstar (uncurry V)

  St : Pred (Market ST) ℓ
  St = ● Cells

  -- we are constructing a relative monad over the market resource morphism
  open Monads (market ST)
  open Morphism (market ST)

  State : Pred (List T) ℓ → Pred (Market (List T)) ℓ
  State P = St ─✴ (J P) ✴ St

  instance
    M-monad : Monad ⊤ _ (λ _ _ → State)
    app (Monad.return M-monad px) st σ₂ = (inj px ×⟨ σ₂ ⟩ st )
    app (app (Monad.bind M-monad {Q = Q} f) m σ₁) st σ₂ with ⊎-assoc σ₁ σ₂
    ... | _ , σ₃ , σ₄ with app m st σ₄
    app (app (Monad.bind M-monad {Q = Q} f) m σ₁) st σ₂ | _ , offerᵣ σ , σ₄ | inj px ×⟨ offerᵣ σ₅ ⟩ st' with ⊎-unassoc σ₅ σ 
    ... | _ , τ₁ , τ₂ = let mq = app f px (⊎-comm τ₁) in app mq st' (offerᵣ τ₂)

  module StateOps 
    (unit : List T) (tt : V unit ε) (unit-emp : ∀ {Φ} → (tt' : V unit Φ) → Φ ≡ ε)
    where

    -- Creating a reference to a cell containing unit.
    -- Note that in the market monoid this is pure!
    -- Because we get a reference that consumes the freshly created resource.
    mkref : ε[ State (Exactly unit) ]
    app mkref (lift st σ₁) (offerᵣ σ₂) rewrite ⊎-id⁻ˡ σ₂ =
      inj refl
        ×⟨ offerᵣ ⊎-∙ ⟩
      lift (cons (tt ×⟨ ⊎-∙ , ⊎-∙ ⟩ st)) (⊎-∙ᵣ σ₁)

    -- -- A linear read on a store: you lose the reference.
    -- -- This is pure, because with the reference being lost, the cell is destroyed: no resources leak.
    read : ∀ {a} → ∀[ Just a ⇒ⱼ State (V a) ]
    app (read refl) (lift st σ₁) (offerᵣ σ₂) with ⊎-assoc σ₂ (⊎-comm σ₁)
    ... | _ , σ₃ , σ₄ with repartition σ₃ st
    ... | cons (v ×⟨ σ₅ ⟩ nil) ×⟨ σ₆ ⟩ st' with ⊎-id⁻ʳ σ₅ | ⊎-assoc (⊎-comm σ₆) (⊎-comm σ₄)
    ... | refl | _ , τ₁ , τ₂ = inj v ×⟨ offerᵣ τ₂ ⟩ lift st' τ₁

    -- -- Writing into an empty cell
    -- write : ∀ {a} → ∀[ Just unit ✴ (V a) ⇒ⱼ State (Just a) ]
    -- app (write (refl ×⟨ σ₁ ⟩ v)) (lift st σ₂) (offerᵣ σ₃) with ⊎-assoc (⊎-comm σ₁) σ₃
    -- -- first we reassociate the arguments in the order that we want to piece it back together
    -- ... | _ , τ₁ , τ₂ with ⊎-assoc (⊎-comm τ₁) (⊎-comm σ₂)
    -- ... | _ , τ₃ , τ₄ with ⊎-assoc τ₂ τ₃
    -- ... | _ , τ₅ , τ₆
    -- -- then we reorganize the store internally to take out the unit value
    --   with repartition τ₅ st
    -- ... | cons (tt' ×⟨ σ₅ ⟩ nil) ×⟨ σ₆ ⟩ st'
    -- -- we apply three (! :() identity lemmas to inform agda that we haven't lost any resources
    --   with unit-emp tt' | ⊎-id⁻ʳ σ₅
    -- ... | refl | refl with ⊎-id⁻ˡ σ₆
    -- ... | refl =
    -- -- and finally we piece back together the parts
    --   inj refl
    --     ×⟨ offerᵣ (consˡ ⊎-idˡ) ⟩
    --   lift (cons (v ×⟨ τ₄ ⟩ st')) (consʳ (⊎-comm τ₆))

    -- -- A linear (strong) update on the store
    -- update! : ∀ {a b} → ∀[ Just a ✴ (V a ─✴ⱼ State (V b)) ⇒ⱼ State (Just b) ]
    -- update! {a} {b} (ptr ×⟨ σ ⟩ f) = do
    --   a ×⟨ σ₁ ⟩ f ← str _ (read ptr ×⟨ j-map σ ⟩ inj f)
    --   b           ← app f a (⊎-comm σ₁)
    --   r ×⟨ σ ⟩ b  ← str _ (mkref ×⟨ ⊎-idˡ ⟩ inj b)
    --   write (r ×⟨ σ ⟩ b)