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
A ~[ lb ] B = Union lb A B

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

  open-mono : ∀ {P I J K} → Open P I → Union I J K → Open P K
  future (closer (open-mono D σ₁)) σ₂
    with _ , τ , κ ← ∙-assocᵣ σ₁ σ₂
    = future (closer D) τ

  syntax open-mono px σ = px ▿ σ

  mono : ∀ {P} → ∀[ Open P ⇒ U ─✴ Open P ]
  mono P ⟨ σ ⟩ _  = open-mono P σ

  instance open-functor : Functor Open
  future (closer (Functor.fmap open-functor f D)) r = f (future (closer D) r)

  instance open-comonad : Comonad Open
  Comonad.extract open-comonad D = future (closer D) (∙-copy _) 
  future (closer (Comonad.extend open-comonad f D)) r = f (open-mono D r)

  ∩-zip : ∀ {P Q : Set → Set₁} → ∀[ Open Q ⇒ Open P ─✴ Open (Q ∩ P) ]
  future (closer (∩-zip Q ⟨ σ ⟩ P)) r
    with _ , σ₂ , σ₃ ← ∙-assocᵣ σ r 
       | _ , σ₄ , σ₅ ← ∙-assocᵣ (∙-comm σ) r
    = extract (open-mono Q σ₂) , extract (open-mono P σ₄)

  private ✴-strength : ∀ {P Q : Set → Set₁} → ∀[ Q ⇒ Open P ─✴ Open (Q ✴ P) ]
  future (closer (✴-strength Q ⟨ σ ⟩ P)) r with _ , σ₂ , σ₃ ← ∙-assocᵣ σ r
    = Q ∙⟨ σ₂ ⟩ future (closer P) σ₃

  instance open-strong-comonad : StrongComonad Open
  StrongComonad.co-str open-strong-comonad = ✴-strength

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
  future (closer (say x)) ext D i = i ≡ E.inja (lower x)
    where module E = Union ext

  κ : (X : Set) → ∀[ (λ i → X → Open Data i) ⇒ Open Data ]
  future (closer (κ X D₁)) ext R i = Σ[ x ∈ X ] extract ((D₁ x) ▿ ext) R i

  ask : ∀[ El ⇒ Open Data ]
  future (closer (ask i′)) ext R i = R (E.inja (lower i′))
    where module E = Union ext

  -- The empty open type at any index
  Bot : ∀[ Open Data ]
  future (closer Bot) ext D = ∅

  -- The unit type at any index
  Top : ∀[ Open Data ]
  future (closer Top) ext D = U

-- module _ where

--   OwFun : ∀[ Open Data ⇒ Open Data ⇒ Open ISet ]
--   OwFun E V = {!E !}

  -- future (closer (OwFun E V)) ext i = {!closer (E ) !}

-- -- Some concrete examples
-- module _ where

--   data Nats : Set where
--     nat  : Nats

--   data Bools : Set where
--     bool : Bools

--   N|B = Nats ⊎ Bools

--   Exp : Open Data N|B
--   Exp = (           (κ ℕ    λ n → say (lift nat))
--       ∪⟨ ∙-∙      ⟩ (κ Bool λ b → say (lift bool)))
--       ∪⟨ ∙-copy _ ⟩ (κ N|B  λ t → ask (lift bool) ∩⟨ subᵣ _ ⟩ ask (lift t) ∩⟨ ∙-copy _ ⟩ ask (lift t))

--   {-# NO_POSITIVITY_CHECK #-}
--   data MU {I} (D : Data I) : ISet I where
--     fix : ∀ {i} → D (MU D) i → MU D i

--   μ : ∀[ Open Data ⇒ ISet ]
--   μ D = MU (extract D)

--   iftrue : μ Exp (inj₂ bool)
--   iftrue =
--     fix (
--       inj₂ ( inj₁ nat -- type of the branches
--         , fix (inj₁ (inj₂ (true , refl))) -- condition
--         , fix (inj₁ (inj₁ (42 , refl)))   -- then
--         , fix (inj₁ (inj₁ (18 , refl)))   -- else
--       )
--     )
