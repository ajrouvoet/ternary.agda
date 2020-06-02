{-# OPTIONS --without-K #-}
module Relation.Ternary.Construct.Sets.Union where

open import Data.Product as Pr
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.These as These
open import Data.These.Properties
open import Level

open import Relation.Nullary hiding (Irrelevant)
open import Relation.Unary
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

-- TODO move to These.Properties 
¬this&that : ∀ {A B : Set} {x : These A B} {a b} → x ≡ this a → ¬ x ≡ that b
¬this&that refl ()

¬this&these : ∀ {A B : Set} {x : These A B} {a a' b} → x ≡ this a → ¬ x ≡ these a' b
¬this&these refl ()

¬that&these : ∀ {A B : Set} {x : These A B} {b' a' b} → x ≡ that b' → ¬ x ≡ these a' b
¬that&these refl ()

module From {A B C : Set} (from : C → These A B) where

  -- You can point out the elements of C that are only in A/B/in both A & B.
  module _ where

    _A≺_  = λ a c   → from c ≡ this a
    _B≺_  = λ b c   → from c ≡ that b
    _&_≺_ = λ a b c → from c ≡ these a b
    
  module _ (P : Pred A 0ℓ) (Q : Pred B 0ℓ) (R : Pred (A × B) 0ℓ) where

    From⟪_,_,_⟫ : C → Set
    From⟪_,_,_⟫ c = fold P Q (curry R) (from c)

    -- A useful view on applications of the 'from' function of the below structure.
    -- Helps avoid green slime and helps to remember equations.
    data From⟨_,_,_⟩  c : Set where
      this    : ∀ a → (i : a A≺ c) → (px : P a) → From⟨_,_,_⟩ c
      that    : ∀ b → (i : b B≺ c) → (qx : Q b) → From⟨_,_,_⟩ c
      these : ∀ a b → (i : a & b ≺ c) → (rx : R (a , b)) → From⟨_,_,_⟩ c

  module _ {P : Pred A 0ℓ} {Q : Pred B 0ℓ} {R : Pred (A × B) 0ℓ} where
  
    intro-from-a : ∀ {a c} → a A≺ c → P a → From⟪ P , Q , R ⟫ c
    intro-from-a eq px rewrite eq = px

    intro-from-b : ∀ {b c} → b B≺ c → Q b → From⟪ P , Q , R ⟫ c
    intro-from-b eq qx rewrite eq = qx
    
    intro-from-ab : ∀ {a b c} → a & b ≺ c → R (a , b) → From⟪ P , Q , R ⟫ c
    intro-from-ab eq qx rewrite eq = qx

    from-elim-a : ∀ {a c} → From⟪ P , Q , R ⟫ c → a A≺ c → P a
    from-elim-a f eq rewrite eq = f

    from-elim-b : ∀ {b c} → From⟪ P , Q , R ⟫ c → b B≺ c → Q b
    from-elim-b f eq rewrite eq = f

    from-elim-ab : ∀ {a b c} → From⟪ P , Q , R ⟫ c → a & b ≺ c → R (a , b)
    from-elim-ab f eq rewrite eq = f

  --
  -- the types of the inverse functions
  --

  InjaInverses : (A → C) → A → Set
  InjaInverses inja a = From⟪ (_≡ a) , ∅ , (_≡ a) ∘ proj₁ ⟫ (inja a)

  InjbInverses : (B → C) → B → Set
  InjbInverses injb b = From⟪ ∅ , (_≡ b) , (_≡ b) ∘ proj₂ ⟫ (injb b)

  RightInverses : (A → C) → (B → C) → C → Set
  RightInverses inja injb c = 
    From⟪ (λ a → inja a ≡ c) 
        , (λ b → injb b ≡ c) 
        , (λ (a , b) → inja a ≡ c × injb b ≡ c) ⟫ c

-- C is a possible union of the Sets A and B.
-- The union is given by to injections inja and injb,
-- and their reverse 'from', which tells you for every element in C whether it came from
-- A, from B, or from both.
--
-- You have to prove that these functions are inverses in a way.
record Union (A B C : Set) : Set₁ where
  constructor union
  field
    inja : A → C
    injb : B → C
    from : C → These A B

  open From from public

  field
    a-inv   : ∀ a → InjaInverses inja a
    b-inv   : ∀ b → InjbInverses injb b
    from-inv : ∀ c → RightInverses inja injb c

  -- Knowing that c came from a, tells you something about inja, etc
  module _ where

    A≺-inv : ∀ {a c} → a A≺ c → inja a ≡ c
    A≺-inv {a} {c} eq = from-elim-a (from-inv c) eq

    B≺-inv : ∀ {b c} → b B≺ c → injb b ≡ c
    B≺-inv {b} {c} eq = from-elim-b (from-inv c) eq

    A&B≺-inv : ∀ {a b c} → a & b ≺ c → inja a ≡ c × injb b ≡ c
    A&B≺-inv {a} {b} {c} eq = from-elim-ab (from-inv c) eq

  -- Variants of the inverses that you can easily pattern match on,
  -- and that generate a bunch of equations to work with
  module _ where

    a-inv'    : ∀ a → From⟨ (λ a' → a ≡ a') 
              , ∅
              , (λ (a' , _) → a ≡ a') ⟩ (inja a)
    a-inv' a with from (inja a) | P.inspect from (inja a)
    ... | this x | P.[ eq ]     = this _ eq $ P.sym $ from-elim-a (a-inv a) eq
    ... | that x | P.[ eq ]     = that _ eq $ from-elim-b (a-inv a) eq
    ... | these x x₁ | P.[ eq ] = these _ _ eq $ P.sym $ from-elim-ab (a-inv a) eq

    b-inv'    : ∀ b → From⟨ ∅
              , (λ b' → b ≡ b') 
              , (λ (_ , b') → b ≡ b') ⟩ (injb b)
    b-inv' b with from (injb b) | P.inspect from (injb b)
    ... | this x | P.[ eq ]     = this _ eq $ from-elim-a (b-inv b) eq
    ... | that x | P.[ eq ]     = that _ eq $ P.sym $ from-elim-b (b-inv b) eq
    ... | these x x₁ | P.[ eq ] = these _ _ eq $ P.sym $ from-elim-ab (b-inv b) eq

    from-inv' : ∀ c → From⟨ (λ a → inja a ≡ c) 
              , (λ b → injb b ≡ c) 
              , (λ (a , b) → inja a ≡ c × injb b ≡ c) ⟩ c
    from-inv' c with from c | P.inspect from c
    ... | this a | P.[ eq ]    = this _ eq (A≺-inv eq)
    ... | that b | P.[ eq ]    = that _ eq (B≺-inv eq)
    ... | these a b | P.[ eq ] = these _ _ eq (A&B≺-inv eq)

  -- We can prove that inja, injb and from are injective using the inverses
  module _ where

    from-injective : ∀ {c c'} → from c ≡ from c' → c ≡ c'
    from-injective {c} {c'} eq with from-inv' c
    ... | From.this a i refl = from-elim-a (from-inv c') (P.trans (P.sym eq) i)
    ... | From.that b i refl = from-elim-b (from-inv c') (P.trans (P.sym eq) i)
    ... | From.these a b i (refl , eq') = begin
      inja a ≡⟨ P.sym eq' ⟩
      injb b ≡⟨ (proj₂ $ from-elim-ab (from-inv c') (P.trans (P.sym eq) i)) ⟩
      c' ∎

    inja-injective : ∀ {a a'} → inja a ≡ inja a' → a ≡ a'
    inja-injective {a} {a'} eq with a-inv' a
    ... | From.this a₁ i refl    = from-elim-a (a-inv a') (P.trans (P.cong from (P.sym eq)) i)
    ... | From.these a₁ b i refl = from-elim-ab (a-inv a') (P.trans (P.cong from (P.sym eq)) i)

    injb-injective : ∀ {b b'} → injb b ≡ injb b' → b ≡ b'
    injb-injective {b} {b'} eq with b-inv' b
    ... | From.that _ i refl    = from-elim-b (b-inv b') (P.trans (P.cong from (P.sym eq)) i)
    ... | From.these _ b i refl = from-elim-ab (b-inv b') (P.trans (P.cong from (P.sym eq)) i)

  module _ where

    a≺inja : ∀ {a a'} → a' A≺ inja a → a ≡ a'
    a≺inja p with q ← A≺-inv p = P.sym $ inja-injective q

    b≺injb : ∀ {b b'} → b' B≺ injb b → b ≡ b'
    b≺injb p with q ← B≺-inv p = P.sym $ injb-injective q

    a&b≺injb : ∀ {a b b'} → a & b' ≺ injb b → a & b ≺ injb b
    a&b≺injb eq with eq' ← proj₂ (A&B≺-inv eq) rewrite injb-injective eq' = eq

    a&b≺inja : ∀ {a b a'} → a' & b ≺ inja a → a & b ≺ inja a
    a&b≺inja eq with eq' ← proj₁ (A&B≺-inv eq) rewrite inja-injective eq' = eq

    a&b≺inja' : ∀ {a b a'} → a' & b ≺ inja a → a ≡ a'
    a&b≺inja' eq with eq' ← proj₁ (A&B≺-inv eq) = inja-injective (P.sym eq')

    ¬A≺injb : ∀ {a b} → ¬ (a A≺ injb b)
    ¬A≺injb {a} {b} eq with b-inv' b
    ... | that _ i qx     = ¬this&that eq i
    ... | these _ b₁ i rx = ¬this&these eq i

    ¬B≺inja : ∀ {a b} → ¬ (b B≺ inja a)
    ¬B≺inja {a} {b} eq with a-inv' a
    ... | this _ i qx     = ¬this&that i eq
    ... | these _ b₁ i rx = ¬that&these eq i
