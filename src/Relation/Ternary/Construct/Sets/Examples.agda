module Relation.Ternary.Construct.Sets.Examples where

open import Level
open import Data.Bool using (Bool; true; false)
open import Data.Product
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Sum

open import Relation.Nullary hiding (Irrelevant)
open import Relation.Unary hiding (⌊_⌋)
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

  mono′ : ∀ {P Q : Set → Set₁} → ∀[ Open P ⇒ Q ─✴ Open P ]
  mono′ D ⟨ σ ⟩ _ = open-mono D (-, σ)

  instance open-functor : Functor Open
  future (closer (Functor.fmap open-functor f D)) r = f (future (closer D) r)

  instance open-comonad : Comonad Open
  Comonad.co-return open-comonad D = future (closer D) (∙-copy _) 
  future (closer ((open-comonad Comonad.<<= f) D)) r = f (open-mono D (-, ∙-comm r))

  ∩-zip : ∀ {P Q : Set → Set₁} → ∀[ Open Q ⇒ Open P ─✴ Open (Q ∩ P) ]
  future (closer (∩-zip Q ⟨ σ ⟩ P)) r
    with _ , σ₂ , σ₃ ← ∙-assocₗ r (∙-comm σ)
       | _ , σ₄ , σ₅ ← ∙-assocₗ r σ
    = co-return (open-mono Q (-, ∙-comm σ₃)) , co-return (open-mono P (-, ∙-comm σ₅))

  private ✴-strength : ∀ {P Q : Set → Set₁} → ∀[ Q ⇒ Open P ─✴ Open (Q ✴ P) ]
  future (closer (✴-strength Q ⟨ σ ⟩ P)) r with _ , σ₂ , σ₃ ← ∙-assocₗ r (∙-comm σ)
    = Q ∙⟨ ∙-comm σ₃ ⟩ future (closer P) σ₂

  instance open-strong-comonad : StrongComonad Open
  StrongComonad.co-str open-strong-comonad = ✴-strength

  -- The empty open type at any index
  Bot : ∀[ Open Data ]
  future (closer Bot) ext D = ∅

  -- The unit type at any index
  Top : ∀[ Open Data ]
  future (closer Top) ext D = U

module _ where
  unions : ∀[ Open Data ⇒ Open Data ─✴ Open Data ]
  unions D₁ ⟨ σ ⟩ D₂ = (λ (X , Y) R → X R ∪ Y R) ⟨$⟩ (∩-zip D₁ ⟨ σ ⟩ D₂)

  prods : ∀[ Open Data ⇒ Open Data ─✴ Open Data ]
  prods D₁ ⟨ σ ⟩ D₂ = (λ (X , Y) R → X R ∩ Y R) ⟨$⟩ (∩-zip D₁ ⟨ σ ⟩ D₂)

  -- syntax definitions
  infixr 10 unions-syntax
  unions-syntax : ∀ {I J K} → Open Data I → Union I J K → Open Data J → Open Data K
  unions-syntax D σ E = unions D  ⟨ σ ⟩ E
  syntax unions-syntax D σ E = D ∪⟨ σ ⟩ E

  infixr 10 prods-syntax
  prods-syntax : ∀ {I J K} → Open Data I → Union I J K → Open Data J → Open Data K
  prods-syntax D σ E = prods D ⟨ σ ⟩ E
  syntax prods-syntax D σ E = D ∩⟨ σ ⟩ E

  El : Set → Set₁
  El X = Lift _ X

  say : ∀[ El ⇒ Open Data ]
  future (closer (say x)) ext D i = i ≡ E.injb (lower x)
    where module E = Union ext

  κ : (X : Set) → ∀[ (λ i → X → Open Data i) ⇒ Open Data ]
  future (closer (κ X D₁)) ext R i = Σ[ x ∈ X ] future (closer (D₁ x)) ext R i 

  ask : ∀[ El ⇒ Open Data ]
  future (closer (ask i′)) ext R i = R (E.injb (lower i′))
    where module E = Union ext

-- Some concrete examples
module _ where

  data Nats : Set where
    nat  : Nats

  data Bools : Set where
    bool : Bools

  N|B = Nats ⊎ Bools

  Exp : Open Data N|B
  Exp = (           (κ ℕ    λ n → say (lift nat))
      ∪⟨ ∙-∙      ⟩ (κ Bool λ b → say (lift bool)))
      ∪⟨ ∙-copy _ ⟩ (κ N|B  λ t → ask (lift bool) ∩⟨ subᵣ _ ⟩ ask (lift t) ∩⟨ ∙-copy _ ⟩ ask (lift t))

  NBExp = co-return Exp

  nb-true : NBExp U (inj₂ bool)
  nb-true = inj₂ (inj₁ nat , _ , _ , _)
