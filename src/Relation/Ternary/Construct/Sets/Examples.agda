module Relation.Ternary.Construct.Sets.Examples where

open import Level
open import Data.Bool using (Bool; true; false)
open import Data.Product
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using (⊤ ; tt)
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

open import Relation.Ternary.Construct.Function

open import Relation.Ternary.Monad
open import Relation.Ternary.Comonad
open import Relation.Ternary.Monad.Necessary
open import Relation.Ternary.Monad.Possibly

open Union

-- A graded relation for expressing the lowerbound on a future world
_~[_]_ : Set → Set → Set → Set₁
A ~[ lb ] B = Union lb A B

instance →⊔-rel : Rel₃ (Set → Set)
→⊔-rel = →-rel

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

  record Open (P : Set → Set₁) (T : Set) (F : Set → Set) : Set₁ where
    field
      closer : ∀ {G : Set → Set} → F T ∙ G T ≣ T → P T

  open Open public

  open-mono : ∀ {P I J K T} → Open P T I → I ∙ J ≣ K → Open P T K
  closer (open-mono {T = T} D σ₁) σ₂
    with _ , τ , _ ←  ∙-assocᵣ (σ₁ T) σ₂
    = closer D τ
    
  syntax open-mono px σ = px ▿ σ

  mono : ∀ {P T} → ∀[ Open P T ⇒ U ─✴ Open P T ]
  mono P ⟨ σ ⟩ _  = open-mono P σ
  
--   instance open-comonad : Comonad Open
--   Comonad.extract open-comonad D = future (closer D) (∙-copy _) 
--   future (closer (Comonad.extend open-comonad f D)) r = f (open-mono D r)

  ∩-zip : ∀ {P Q : Set → Set₁} {T} → ∀[ Open P T ⇒ Open Q T ─✴ Open (P ∩ Q) T ]
  closer (∩-zip {T = T} Q ⟨ σ ⟩ P) r
    with _ , σ₂ , σ₃ ← ∙-assocᵣ (σ T) r
       | _ , σ₄ , σ₅ ← ∙-assocᵣ (∙-comm (σ T)) r 
    = closer Q σ₂ , closer P σ₄

--   future (closer (∩-zip Q ⟨ σ ⟩ P)) r
--     with _ , σ₂ , σ₃ ← ∙-assocᵣ σ r 
--        | _ , σ₄ , σ₅ ← ∙-assocᵣ (∙-comm σ) r
--     = extract (open-mono Q σ₂) , extract (open-mono P σ₄)

--   private ✴-strength : ∀ {P Q : Set → Set₁} → ∀[ Q ⇒ Open P ─✴ Open (Q ✴ P) ]
--   future (closer (✴-strength Q ⟨ σ ⟩ P)) r with _ , σ₂ , σ₃ ← ∙-assocᵣ σ r
--     = Q ∙⟨ σ₂ ⟩ future (closer P) σ₃

--   instance open-strong-comonad : StrongComonad Open
--   StrongComonad.co-str open-strong-comonad = ✴-strength

module _ where
  unions : ∀ {T} → ∀[ Open Data T ⇒ Open Data T ─✴ Open Data T ]
  closer (unions D₁ ⟨ σ ⟩ D₂) {G = G} pr 
    with ρ ← closer (∩-zip D₁ ⟨ σ ⟩ D₂)
    = case ρ {G = G} pr of
      λ where (X , Y) R → X R ∪ Y R

  prods : ∀ {T} → ∀[ Open Data T ⇒ Open Data T ─✴ Open Data T ]
  closer (prods D₁ ⟨ σ ⟩ D₂) {G = G} pr
    with ρ ← closer (∩-zip D₁ ⟨ σ ⟩ D₂)
    = case ρ {G = G} pr of
      λ where (X , Y) R → X R ∩ Y R 

  -- syntax definitions
  infixr 10 unions-syntax
  unions-syntax : ∀ {I J K T} → Open Data T I → I ∙ J ≣ K → Open Data T J → Open Data T K
  unions-syntax D σ E = unions D ⟨ σ ⟩ E 

  syntax unions-syntax D σ E = D ∪⟨ σ ⟩ E

  infixr 10 prods-syntax
  prods-syntax : ∀ {I J K T} → Open Data T I → I ∙ J ≣ K → Open Data T J → Open Data T K
  prods-syntax D σ E = prods D ⟨ σ ⟩ E
  syntax prods-syntax D σ E = D ∩⟨ σ ⟩ E

  {-# NO_POSITIVITY_CHECK #-}
  data MUᴵ (F : Set → Set) : Set where
    fixᴵ : F (MUᴵ F) → MUᴵ F

  μᴵ : (Set → Set) → Set
  μᴵ = MUᴵ

  El : Set → (Set → Set) → Set₁
  El T X = Lift _ (X T)

  say : ∀ {T} → ∀[ El T ⇒ Open Data T ]
  closer (say x) ext D i = i ≡ E.inja (lower x)
    where module E = Union ext

  say′ : ∀ {T} → T → ∀[ Open Data T ]
  closer (say′ i′) _ _ i = i′ ≡ i
  
--   (closer (say x)) ext D i = i ≡ E.inja (lower x)
--     where module E = Union ext

  κ : (S : Set) → ∀ {T} → ∀[ (λ i → S → Open Data T i) ⇒ Open Data T ]
  closer (κ S D₁) {G} ext R i = Σ[ s ∈ S ] closer (D₁ s) {G = G} ext R i

--   future (closer (κ X D₁)) ext R i = Σ[ x ∈ X ] extract ((D₁ x) ▿ ext) R i

  ask : ∀ {T} → ∀[ El T ⇒ Open Data T ]
  closer (ask i′) ext R i = R (E.inja (lower i′))
    where module E = Union ext

  ask′ : ∀ {T} → T → ∀[ Open Data T ]
  closer (ask′ i′) _ R _ = R i′

--   future (closer (ask i′)) ext R i = R (E.inja (lower i′))
--     where module E = Union ext

--   poke : ∀ {I} → (∀ {J Φ′} → J ~[ I ] Φ′ → Data Φ′) → Open Data I
--   future (closer (poke f)) ext R i = f ext R i

  π′ : ∀ {T} → ∀[ (λ F → T → Open Data T F) ⇒ Open Data T ]
  closer (π′ f) {G} ext R i = closer (f i) {G} ext R i

  -- The empty open type at any index
  Bot : ∀ {T} → ∀[ Open Data T ]
  (closer Bot) ext D = ∅

  -- The unit type at any index
  Top : ∀ {T} → ∀[ Open Data T ]
  (closer Top) ext D = U

{-# NO_POSITIVITY_CHECK #-}
data MU {I} (D : Data I) : ISet I where
  fix : ∀ {i} → D (MU D) i → MU D i

open Inverse

MU-init : ∀ {T : Set → Set} → (MUᴵ T) ↔ T (MUᴵ T)
f      MU-init = λ where (fixᴵ v) → v
f⁻¹    MU-init = fixᴵ
cong₁  MU-init = P.cong (f MU-init)
cong₂  MU-init = P.cong (f⁻¹ MU-init)
proj₁ (inverse MU-init) _        = refl
proj₂ (inverse MU-init) (fixᴵ _) = refl

μ : ∀ {T} → Open Data ((MUᴵ T)) T → ISet (MUᴵ T)
μ D with D' ← closer D {G = ε} (coe {{ ∙-respects-≈ˡ }} MU-init ∙-idʳ)
         = MU D'
         
μ⟦_⟧ : ∀ {T} → Open Data ((MUᴵ T)) T → ISet (MUᴵ T)
μ⟦ D ⟧ with D' ← closer D {G = ε} (coe {{ ∙-respects-≈ˡ }} MU-init ∙-idʳ)
            = D' (MU D')

-- module _ where

--   OwFun : ∀[ Open Data ⇒ Open Data ⇒ Open ISet ]
--   OwFun E V = {!E !}

--   future (closer (OwFun E V)) ext i = {!closer (E ) !}

-- Some concrete examples
module _ where

  data Nats (R : Set) : Set where
    nat  : Nats R

  data Bools (R : Set) : Set where
    bool : Bools R

  data Pairs (R : Set) : Set where
    ⟨_,_⟩ : (l r : R) → Pairs R

  N∣B∣P = Nats ∪ Bools ∪ Pairs

  Indexed : (Set → Set) → Set
  Indexed F = ∀ {T} → Open Data T F

  NatExp : Indexed Nats
  NatExp =                       say (lift nat)
  
         ∪⟨ (λ _ → ∙-copy _) ⟩ ( ask (lift nat) ∩⟨ (λ _ → ∙-copy _) ⟩ say (lift nat) )
         
         ∪⟨ (λ _ → ∙-copy _) ⟩  ( ask (lift nat) ∩⟨ (λ _ → ∙-copy _) ⟩                  
                                  ask (lift nat) ∩⟨ (λ _ → ∙-copy _) ⟩ say (lift nat) )


  BoolExp : Indexed Bools
  BoolExp =                     say (lift bool)
          ∪⟨ (λ _ → ∙-copy _) ⟩ say (lift bool)
          ∪⟨ (λ _ → ∙-copy _) ⟩ π′ λ t → ask (lift bool)  ∩⟨ (λ _ → ∙-copy _) ⟩ 
                                         ask′ t           ∩⟨ (λ _ → ∙-copy _) ⟩
                                         ask′ t           ∩⟨ (λ _ → ∙-copy _) ⟩ say′ t


  PairExp : Indexed Pairs
  PairExp {T} =                       κ (T × T) ( λ where (t₁ , t₂) →   ask′ t₁ ∩⟨ (λ _ → ∙-copy _) ⟩
                                                                        ask′ t₂ ∩⟨ (λ _ → ∙-copy _) ⟩
                                                                        say (lift ⟨ t₁ , t₂ ⟩))
                                                                        
              ∪⟨ (λ _ → ∙-copy _) ⟩ ( κ (T × T)   λ where (t₁ , t₂) → ( ask (lift ⟨ t₁ , t₂ ⟩)) ∩⟨ (λ _ → ∙-copy _) ⟩
                                                                        say′ t₁ )
                                                                        
              ∪⟨ (λ _ → ∙-copy _) ⟩ ( κ (T × T)   λ where (t₁ , t₂) →   ask (lift ⟨ t₁ , t₂ ⟩) ∩⟨ (λ _ → ∙-copy _) ⟩
                                                                        say (lift ⟨ t₂ , t₁ ⟩) )

  Exp : Indexed N∣B∣P
  Exp =                       NatExp
      ∪⟨ (λ _ → ∙-disjoint) ⟩ BoolExp
      ∪⟨ (λ _ → ∙-disjoint) ⟩ PairExp


  --
  -- Type constructors
  --

  tnat : μᴵ N∣B∣P
  tnat = fixᴵ (inj₁ nat)

  tbool : μᴵ N∣B∣P
  tbool = fixᴵ (inj₂ (inj₁ bool))

  tpair : μᴵ N∣B∣P → μᴵ N∣B∣P → μᴵ N∣B∣P
  tpair l r = fixᴵ (inj₂ (inj₂ ⟨ l , r ⟩))


  --
  -- Nat expression constructors 
  --
  zz : μ Exp tnat
  zz = fix (inj₁ (inj₁ refl))

  ss : μ Exp tnat → μ Exp tnat
  ss n = fix (inj₁ (inj₂ (inj₁ (n , refl))))

  add : μ Exp tnat → μ Exp tnat → μ Exp tnat
  add n m = fix (inj₁ (inj₂ (inj₂ (n , (m , refl)))))

  --
  -- Bool expression constructors 
  --

  ttt : μ Exp tbool
  ttt = fix (inj₂ (inj₁ (inj₁ refl)))

  fff : μ Exp tbool
  fff = fix (inj₂ (inj₁ (inj₂ (inj₁ refl))))

  `if_then_else_ : ∀ {t} → μ Exp tbool → μ Exp t → μ Exp t → μ Exp t
  `if e₁ then e₂ else e₃ = fix (inj₂ (inj₁ (inj₂ (inj₂ (e₁ , e₂ , (e₃ , refl))))))

  --
  -- Pair expression constructors 
  -- 

  mkpair : ∀ {t₁ t₂} → μ Exp t₁ → μ Exp t₂ → μ Exp (tpair t₁ t₂)
  mkpair {t₁} {t₂} l r = fix (inj₂ (inj₂ (inj₁ ((t₁ , t₂) , l , r , refl))))

  fst : ∀ {t₁ t₂} → μ Exp (tpair t₁ t₂) → μ Exp t₁
  fst {t₁} {t₂} p = fix (inj₂ (inj₂ (inj₂ (inj₁ ((t₁ , t₂) , p , refl)))))

  `swap : ∀ {t₁ t₂} → μ Exp (tpair t₁ t₂) → μ Exp (tpair t₂ t₁)
  `swap {t₁} {t₂} p = fix (inj₂ (inj₂ (inj₂ (inj₂ ((t₁ , t₂) , p , refl)))))

  snd : ∀ {t₁ t₂} → μ Exp (tpair t₁ t₂) → μ Exp t₂
  snd p = fst (`swap p)

  --
  -- Example expressions
  --

  expr₁ : μ Exp tnat
  expr₁ = fst (mkpair (`if snd (mkpair (ss (ss zz)) fff) then zz else ss zz) ttt)

  expr₂ : μ Exp (tpair (tpair tbool tnat) tbool)
  expr₂ = `if fff then `swap (mkpair (snd (mkpair ttt fff)) (mkpair fff zz)) else mkpair (mkpair fff (ss zz)) ttt
  
