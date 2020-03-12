{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Separation where

open import Relation.Ternary.Core public
open import Relation.Ternary.Structures.Syntax public
  renaming
    ( _∙_≣_ to _⊎_≣_
    ; _∙⟨_⟩_ to _×⟨_⟩_
    ; _⊙_ to _✴_
    ; _─⊙_ to _─✴_)
