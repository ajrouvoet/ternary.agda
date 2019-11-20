{-# OPTIONS --safe --without-K #-}

-- Proof relevant separation algebras
module Relation.Ternary.Separation where

open import Relation.Unary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Ternary.Separation.Core public

{- Just this, because we don't know where to put it... -}
module _ where
  open import Data.List

  Just : ∀ {a} {A : Set a} → A → Pred (List A) _
  Just {A = A} t = Exactly [ t ]
