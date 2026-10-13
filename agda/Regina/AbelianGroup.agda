{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- AbelianGroup(MatrixInt), engine/algebra/abeliangroup.cpp.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.AbelianGroup where

open import Regina.Foundation
open import Regina.IntegerMatrix
open import Regina.SmithNormalForm
open import Agda.Builtin.Nat using (_-_)

record AbelianGroup : Set where
  constructor abelian_group
  field
    free_rank : Nat
    invariant_factors : List Nat
open AbelianGroup public

removeUnits : List Nat → List Nat
removeUnits [] = []
removeUnits (zero ∷ remaining) = removeUnits remaining
removeUnits (suc zero ∷ remaining) = removeUnits remaining
removeUnits (suc (suc magnitude) ∷ remaining) =
  suc (suc magnitude) ∷ removeUnits remaining

groupFromSmith : {relations generators : Nat} →
  (original : Matrix relations generators) → SmithCertificate original → AbelianGroup
groupFromSmith {generators = generators} original smithResult = abelian_group
  (generators - length nonzeroDiagonal) (removeUnits nonzeroDiagonal)
  where
  nonzeroDiagonal : List Nat
  nonzeroDiagonal = smithDiagonal (reduced_matrix (smith_state smithResult))

groupFromPresentation : {relations generators : Nat} → Nat →
  Matrix relations generators → Maybe AbelianGroup
groupFromPresentation fuel original with smithNormalForm fuel original
... | nothing = nothing
... | just smithResult = just (groupFromSmith original smithResult)

torsionRank : Nat → AbelianGroup → Nat
torsionRank prime currentGroup = fold_right count zero (invariant_factors currentGroup)
  where
  open import Regina.Integer using (divides; pos)
  count : Nat → Nat → Nat
  count factor remaining with divides (pos prime) (pos factor)
  ... | true = suc remaining
  ... | false = remaining
