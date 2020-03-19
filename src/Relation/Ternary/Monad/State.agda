open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Monad.State {ℓ} {C : Set ℓ} (r : Rel₃ C) 
  {e u} {_≈_ : C → C → Set e}
  {{m : IsPartialMonoid _≈_ r u}}
  {{c : IsCommutative r}} where

open import Level hiding (Lift)
open import Data.Product
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Unary.PredicateTransformer using (Pt; PT)
open import Relation.Unary hiding (_∈_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Construct.List.Disjoint
open import Relation.Ternary.Monad

open import Data.Unit
open import Data.Product

open import Relation.Ternary.Construct.Market r as Market hiding (_≈_)

private
  instance _ = r

module _ where

  STATET : (M : Pt Market ℓ) → (l r : Pred C ℓ) → Pt C ℓ
  STATET M St St' P = (● St ─⊙ M (○ P ⊙ ● St')) ∘ demand

  StateT : (M : Pt Market ℓ) → Pred C ℓ → Pt C ℓ
  StateT M St = STATET M St St

  open import Relation.Ternary.Monad.Identity

  State : Pred C ℓ → Pt C ℓ
  State St = STATET Id St St
  
module StateTransformer
  (M : Pt Market ℓ) {{monad : Monad ⊤ (λ _ _ → M) }}
  {St : Pred C ℓ}
  where

  instance state-respects : ∀ {P St St'} → Respect _≈_ (STATET M St St' P)
  Respect.coe state-respects eq st = coe (demands eq) st

  instance
    state-monad : Monad ⊤ (λ _ _ → StateT M St)
    Monad.return state-monad px ⟨ σ₂ ⟩ st = return (lift px ∙⟨ σ₂ ⟩ st )
    ((Monad.bind state-monad {P = P} {Q = Q} f) ⟨ σ₁ ⟩ m) ⟨ σ₂@(offerᵣ σ₅) ⟩ st@(lift _) with ∙-assocᵣ (demand σ₁) σ₂
    ... | _ , σ₃ , σ₄ = bind bound ⟨ σ₃ ⟩ (m ⟨ σ₄ ⟩ st)
      where
        bound : ((○ P ⊙ ● St) ─⊙ M (○ Q ⊙ ● St)) (demand _)
        bound ⟨ offerᵣ σ₆ ⟩ (lift px ∙⟨ offerᵣ σ₅ ⟩ st') with ∙-assocₗ σ₅ σ₆
        ... | _ , τ₁ , τ₂ = let mq = f ⟨ ∙-comm τ₁ ⟩ px in mq ⟨ offerᵣ τ₂ ⟩ st'

  {- Lift an M computation into a transformed state operation -}
  liftM : ∀ {Φ P} → M P (demand Φ) → StateT M St (P ∘ demand) Φ
  liftM mp ⟨ (offerᵣ σ) ⟩ (lift μ) =
    mapM′ (arr λ where σ@(offerₗ _) px → lift px ∙⟨ ∙-comm σ ⟩ lift μ) ⟨ offerₗ (∙-comm σ) ⟩ mp

  {- Lift a state computation into a transformed state operation -}
  liftState : ∀ {P} → ∀[ State St P ⇒ StateT M St P ]
  liftState mp ⟨ σ ⟩ st = Monad.return monad (mp ⟨ σ ⟩ st)
 
-- module StateWithErr {ℓ}
--   {C : Set ℓ} {{r : Rel₃ C}}
--   {u} {{s : IsPartialMonoid _≡_ r u}}
--   (Exc : Set ℓ) where

--   open import Relation.Ternary.Monad.Error
--   open ExceptMonad {A = Market C} Exc public
--   open StateTransformer {C = C} (Except Exc) {{ monad = except-monad }} public

--   open import Data.Sum

--   State? : ∀ (S : Pred (C × C) ℓ) → Pt C ℓ
--   State? = StateT (Except Exc)

--   _orElse_ : ∀ {S P} {M : Pt Market ℓ} {{monad : Monads.Monad ⊤ ℓ (λ _ _ → M) }}
--                 → ∀[ State? S P ⇒ (⋂[ _ ∶ Exc ] StateT M S P) ⇒ StateT M S P ]
--   app (mp orElse mq) μ σ with app mp μ σ
--   ... | error e = app (mq e) μ σ
--   ... | ✓ px    = return px

--   try : ∀ {S P} → ε[ State? S P ] → ε[ State S (Emp ∪ P) ]
--   app (try mp?) st σ with app mp? st σ
--   ... | error e                = inj (inj₁ empty) ∙⟨ σ ⟩ st
--   ... | ✓ (inj px ∙⟨ σ' ⟩ st') = inj (inj₂ px) ∙⟨ σ' ⟩ st'

--   raise : ∀ {S P} → Exc → ∀[ State? S P ]
--   app (raise {P} e) μ σ = partial (inj₁ e)
