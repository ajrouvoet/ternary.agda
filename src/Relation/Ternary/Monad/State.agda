{-# OPTIONS --no-qualified-instances --safe #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Monad.State {ℓ} {C : Set ℓ} (r : Rel₃ C)
  {e u} {_≈_ : C → C → Set e}
  {{m : IsPartialMonoid _≈_ r u}}
  {{c : IsCommutative r}} where

private instance _ = r

open import Level hiding (Lift)
open import Data.Product
open import Data.Sum
open import Function using (_∘_; case_of_; const)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Unary.PredicateTransformer using (Pt; PT)
open import Relation.Unary hiding (_∈_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Construct.List.Disjoint
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Error
open import Relation.Ternary.Monad.Identity using (module Wrapped; module Unwrapped)

open import Data.Unit
open import Data.Product

open Wrapped

open import Relation.Ternary.Construct.Market r as Market hiding (_≈_)

private
  instance r-rel = r

-- state interfaces
module _ where

  ActionT : Pt Market ℓ → Pred C ℓ → Pred C ℓ → Pred C ℓ → Pred C ℓ
  ActionT M S S' P = (● S ─✴ M (○ P ✴ ● S')) ∘ demand

  Action : Pred C ℓ → Pred C ℓ → Pred C ℓ
  Action S P = ActionT Unwrapped.Id S S P

  record MonadState (M : Pt C ℓ) (S : Pred C ℓ) : Set (suc ℓ) where
    field
      overlap {{monad}} : Monad ⊤ (λ _ _ → M)
      withState         : ∀ {P} → ∀[ Action S P ⇒ M P ]

module _ where

  record STATET (M : Pt Market ℓ) (S S' : Pred C ℓ) (P : Pred C ℓ) (c : C) : Set ℓ where
    constructor state
    field
      runState : ActionT M S S' P c

  open STATET public

  StateT : (M : Pt Market ℓ) → Pred C ℓ → Pt C ℓ
  StateT M St = STATET M St St

  State : Pred C ℓ → Pt C ℓ
  State St = STATET Id St St

module StateTransformer (M : Pt Market ℓ) (St : Pred C ℓ) where

  instance state-respects : ∀ {P St St'} → Respect _≈_ (STATET M St St' P)
  Respect.coe state-respects eq (state st) = state (coe (demands eq) st)

  module _ {{_ : Functor M}} where

    instance state-functor : Functor (StateT M St)
    runState (Functor.fmap state-functor f (state m)) ⟨ σ ⟩ st = do
      (λ where (lift px ∙⟨ σ ⟩ st) → lift (f px) ∙⟨ σ ⟩ st) ⟨$⟩ (m ⟨ σ ⟩ st)

  module _ {{_ : Monad ⊤ (λ _ _ → M)}} where

    instance state-monad : Monad ⊤ (λ _ _ → StateT M St)
    runState (Monad.return state-monad px) ⟨ σ₂ ⟩ st = return (lift px ∙⟨ σ₂ ⟩ st )
    runState (Monad._=<<_ state-monad f (state m)) ⟨ σ ⟩ st = do
      lift px ∙⟨ σ ⟩ st ← m ⟨ σ ⟩ st
      runState (f px) ⟨ σ ⟩ st

    instance state-monadstate : MonadState (StateT M St) St
    runState (MonadState.withState state-monadstate f) ⟨ σ ⟩ μ = return (f ⟨ σ ⟩ μ)

    {- Lift a state computation into a transformed state operation -}
    liftState : ∀ {P} → ∀[ State St P ⇒ StateT M St P ]
    runState (liftState (state m)) ⟨ σ ⟩ st = return (runId (m ⟨ σ ⟩ st))

  module _ {{_ : Strong ⊤ (λ _ _ → M)}} where

    instance state-strong : Strong ⊤ (λ _ _ → StateT M St)
    runState (Strong.str state-strong {Q = Q} qx ⟨ σ₁ ⟩ (state mpx)) ⟨ σ₂ ⟩ st = do
      let _ , σ₃ , σ₄  = ∙-assocᵣ (demand σ₁) σ₂
      lift qx ∙⟨ supplyᵣ σ₅ ⟩ lift px ∙⟨ supplyᵣ σ₆ ⟩ st ← ○ Q ∋ lift qx &⟨ σ₃ ⟩ (mpx ⟨ σ₄ ⟩ st)
      let _ , σ₇ , σ₈  = ∙-assocₗ σ₆ σ₅
      return ((lift (qx ∙⟨ ∙-comm σ₇ ⟩ px)) ∙⟨ supplyᵣ σ₈ ⟩ st)

    {- Lift an M computation into a transformed state operation -}
    liftM : ∀ {Φ P} → M P (demand Φ) → StateT M St (P ∘ demand) Φ
    runState (liftM m) ⟨ supplyᵣ σ ⟩ (lift μ) =
      mapM′ (arr λ where σ@(supplyₗ _) px → lift px ∙⟨ ∙-comm σ ⟩ lift μ) ⟨ supplyₗ (∙-comm σ) ⟩ m

module Substate {S₁ S₂} (M : Pt C ℓ) {{m : MonadState M S₁}}
  (zoom : ∀ {p} {P : Pred C p} → ∀[ (● S₂ ─✴ (○ P ✴ ● S₂)) ⇒ ● S₁ ─✴ (○ P ✴ ● S₁) ]) where

  instance monad-state' : MonadState M S₂
  MonadState.withState monad-state' f = MonadState.withState m (arr (λ σ px → zoom f ⟨ σ ⟩ px))

module StateWithErr (Exc : Set) (S : Pred C ℓ) where

  open StateTransformer (Except Exc) S public

  State? : Pt C ℓ
  State? = StateT (Except Exc) S

  runState? : ∀ {P} → ∀[ State? P ⇒ (● S ─✴ (const Exc ∪ (○ P ✴ ● S))) ∘ demand ]
  runState? c ⟨ σ ⟩ μ  = runExc (runState c ⟨ σ ⟩ μ)

  _orElse_ : ∀ {P} {M : Pt Market ℓ} {{monad : Monad ⊤ (λ _ _ → M) }}
           → ∀[ State? P ⇒ (⋂[ _ ∶ Exc ] StateT M S P) ⇒ StateT M S P ]
  runState (mp orElse mq) ⟨ σ ⟩ μ =
    case (runState? mp ⟨ σ ⟩ μ) of λ where
         (inj₁ e)   → runState (mq e) ⟨ σ ⟩ μ
         (inj₂ px)  → return px

  liftErr : ∀ {P} → ∀[ Except Exc P ⇒ State? P ]
  runState (liftErr m) ⟨ σ ⟩ μ = do
    case (runExc m) of λ where
      (inj₁ e) → raise e
      (inj₂ p) → return (lift p ∙⟨ σ ⟩ μ)

  try : ∀ {P} → ε[ State? P ] → ε[ State S (Emp ∪ P) ]
  runState (try mp?) ⟨ σ ⟩ st = case runState? mp? ⟨ σ ⟩ st of λ where
    (inj₁ e)                     → return (lift (inj₁ refl) ∙⟨ σ  ⟩ st)
    (inj₂ (lift px ∙⟨ σ' ⟩ st')) → return (lift (inj₂ px)   ∙⟨ σ' ⟩ st')

  instance state?-error : MonadError Exc State?
  runState (MonadError.raise state?-error e) ⟨ σ ⟩ μ = except (inj₁ e)

open MonadState {{...}} public

{- If we have state and error, then we can get an exceptional withState operation -}
module _ {M : Pt C ℓ} {S} {E : Set} {{ms : MonadState M S}} {{me : MonadError E M}} where

  withState? : ∀ {P} → ∀[ (● S ─✴ (Except E (○ P ✴ ● S))) ∘ demand ⇒ M P ]
  withState? f = do
    inj₂ px ← withState (arr λ σ st →
      -- remarkably the following switcheroo works out resource-wise
      case runExc (f ⟨ σ ⟩ st) of λ where
        (inj₁ e)                     → lift (inj₁ e) ∙⟨ σ ⟩ st
        (inj₂ (lift px ∙⟨ σ' ⟩ st')) → lift (inj₂ px) ∙⟨ σ' ⟩ st'
      )
      where inj₁ e → raise e
    return px
