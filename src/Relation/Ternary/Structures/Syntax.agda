{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Structures.Syntax where

open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open IsEquivalence      {{...}} using () renaming
  ( refl to ≈-refl
  ; sym to ≈-sym
  ; trans to ≈-trans
  ; reflexive to ≈-reflexive) public

open Rel₃               {{...}} public
open Emptiness          {{...}} public
open IsPartialSemigroup {{...}} public
open IsPartialMonoid    {{...}} public
open IsPositive         {{...}} public
open IsPositiveWithZero {{...}} public
open IsCommutative      {{...}} public
open IsCrosssplittable  {{...}} public
open IsIntuitionistic   {{...}} public
open IsJoinoid          {{...}} public
open IsTotal            {{...}} public

open CommutativeSemigroupOps public
