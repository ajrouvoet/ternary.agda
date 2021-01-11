module Relation.Ternary.Monad.Delay {a e} {A : Set a} {_≈_ : A → A → Set e} where

open import Level
open import Size
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)

open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad

open import Codata.Thunk as T using (force) public
open import Codata.Delay as D using (now; later) public
open import Data.Unit

module _
  {{rel : Rel₃ A}}
  {u} {{us : IsPartialMonoid _≈_ rel u}}
 where

  Delay : ∀ {ℓ} i → Pt A ℓ
  Delay i P c = D.Delay (P c) i
    
  Thunk : ∀ {ℓ} i → (Size → Pred A ℓ) → Pred A ℓ
  Thunk i P c = T.Thunk (λ j → P j c) i

  instance
    delay-functor : ∀ {i} → Functor (Delay i)
    Functor.fmap delay-functor f d = D.map f d

    delay-monad : ∀ {i} → Monad ⊤ (λ _ _ → Delay i)
    Monad.return delay-monad    = D.now
    Monad._=<<_ delay-monad f d = D.bind d f

    delay-strong : ∀ {i} → Strong ⊤ (λ _ _ → Delay i)
    Strong.str delay-strong q ⟨ σ ⟩ now p = now (q ∙⟨ σ ⟩ p)
    Strong.str delay-strong q ⟨ σ ⟩ later ▹p = later (str' q ⟨ σ ⟩ ▹p)
      where
        str' : ∀ {i} {P Q : Pred A a} → ∀[ Q ⇒ Thunk i (λ j → Delay j P) ─✴ Thunk i (λ j → Delay j (Q ✴ P)) ]
        T.force (str' q ⟨ σ ⟩ t) = str q ⟨ σ ⟩ (T.force t)
