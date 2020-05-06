module Relation.Ternary.Construct.Sets.Examples where

open import Level
open import Data.Bool using (Bool; true; false)
open import Data.Product
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Sum

open import Relation.Nullary hiding (Irrelevant)
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Core
open import Relation.Ternary.Respect.Propositional
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax hiding (_∣_)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open P.≡-Reasoning

open import Function using (id; case_of_; _∘_; Inverse; _$_)
open import Function.Structures
open import Function.Bundles

open import Relation.Ternary.Construct.Sets.Union
open import Relation.Ternary.Construct.Sets
open import Relation.Ternary.Monad
open import Relation.Ternary.Comonad
open import Relation.Ternary.Monad.Necessary
open import Relation.Ternary.Monad.Possibly

open Union

-- A graded relation for expressing the lowerbound on a future world
_~[_]_ : Set → Set → Set → Set₁
A ~[ lb ] B = Union A lb B

open Necessary {A = Set} _~[_]_ 

ISet : Set → Set₁
ISet T = T → Set

iset-resp : Respect _↔_ ISet
Respect.coe iset-resp eqv P = P ∘ f⁻¹ 
  where open Inverse eqv

-- Data are presented as ISet transformers
Data : Set → Set₁
Data I = ISet I → ISet I

-- "Open" predicates that only assume a lower bound on there index.
module _ where

  record Open (P : Set → Set₁) I : Set₁ where
    field
      closer : ∀ {J} → □[ I ] P J

  open Open public

  open-mono : ∀ {P I J} → Open P I → I ≤ J → Open P J
  future (closer (open-mono D σ₁)) σ₂
    with _ , τ , κ ← ∙-assocₗ σ₂ (∙-comm (proj₂ σ₁))
    = future (closer D) κ

  instance open-functor : Functor Open
  future (closer (Functor.fmap open-functor f D)) r = f (future (closer D) r)

  instance open-comonad : Comonad Open
  Comonad.co-return open-comonad D = future (closer D) (∙-copy _) 
  future (closer ((open-comonad Comonad.<<= f) D)) r = f (open-mono D (-, ∙-comm r))

  private strength : ∀ {P Q : Set → Set₁} → ∀[ Q ⇒ Open P ─✴ Open (Q ✴ P) ]
  future (closer (strength Q ⟨ σ ⟩ P)) r with _ , σ₂ , σ₃ ← ∙-assocₗ r (∙-comm σ)
    = Q ∙⟨ ∙-comm σ₃ ⟩ future (closer P) σ₂

  instance open-strong-comonad : StrongComonad Open
  StrongComonad.co-str open-strong-comonad = strength

  -- The empty open type at any index
  Bot : ∀[ Open Data ]
  future (closer Bot) ext D = ∅

closed-onions : ∀[ Data ⇒ Data ─✴ Data ]
closed-onions D₁ ⟨ σ ⟩ D₂ = λ R i → {!!}
  where

onions : ∀[ Open Data ⇒ Open Data ─✴ Open Data ]
onions D₁ ⟨ σ ⟩ D₂ = (λ (X ∙⟨ σ ⟩ Y) → closed-onions X ⟨ σ ⟩ Y) ⟨$⟩ (co-mzip D₁ ⟨ σ ⟩ D₂)

-- Some concrete examples
module _ where

  data Nats : Set where
    nat  : Nats

  data Bools : Set where
    bool : Bools

  -- Manually
  data Exp₁ {T' : Set} (σ : Bools ≤ T') (E : T' → Set) : (T' → Set) where
    bool       : Bool → Exp₁ σ E (inja (proj₂ σ) bool)
    ifthenelse : ∀ {t : T'} → E (inja (proj₂ σ) bool) → E t → E t → Exp₁ σ E t

  -- Using wand in somwhat strange way? 
  Exp₂ : ∀[ Own Bools ─✴ (ISet ⇒ ISet) ]
  (Exp₂ ⟨ σ ⟩ refl) E =
    (λ t → Bool × t ≡ (injb σ bool))
    ∪
    λ t → E (injb σ bool) × E t × E t

  -- Using necessity comonad
  Exp₃ : ∀[ □[ Bools ] (ISet ⇒ ISet) ]
  Necessary.future Exp₃ ext E = -- ∀ T . Bools ≤ T . (E : T → Set) . T → Set
      (λ t → Bool × t ≡ injb ext bool)      -- true | false
    ∪ (λ t → E (injb ext bool) × E t × E t) -- if c then d else e

  -- not quite right
  -- Exp₄ : ∀[ Own Bools ⇒ ISet ─✴ ISet ]
  -- Exp₄ refl ⟨ σ ⟩ E = (λ t → Bool × t ≡ (inja σ bool)) ∪ λ t → E {!inja σ bool!} × E {!!} × E {!!}

  data NatsAndBools : Set where
    nat  : NatsAndBools
    bool : NatsAndBools

  -- Using necessity comonad
  Exp₅ : ∀[ □[ NatsAndBools ] (ISet ⇒ ISet) ]
  Necessary.future Exp₅ ext E =
      (λ t → ℕ                                   × t ≡ injb ext nat)  -- 0, 1, ...
    ∪ (λ t → E (injb ext nat) × E (injb ext nat) × t ≡ injb ext bool) -- e ≥ f

  postulate Arith : ∀[ □[ Nats ] (ISet ⇒ ISet) ]
  -- Arith = {!!}

  postulate n≤n&b : Union Nats NatsAndBools NatsAndBools

  -- El : ∀[ Open ⇒ ISet ⇒ ISet ]
  -- El {I} D R i = close D R i 

  -- El : ∀[ Open ⇒ El ]
