{-# OPTIONS --safe #-}

open import Relation.Unary

module Relation.Ternary.Respect.Propositional
 {a p} {A : Set a} {P : Pred A p} where

open import Function using (id)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core

open import Relation.Binary.PropositionalEquality

instance respect-≡ : Respect _≡_ P
Respect.coe respect-≡ refl = id
