{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- AbelianGroup(boundary, nextBoundary), engine/algebra/abeliangroup.cpp.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.ChainHomology where

open import Regina.Foundation
open import Regina.IntegerMatrix
open import Regina.SmithNormalForm
open import Regina.AbelianGroup
open import Regina.Integer using (pos)
import Regina.Integer as Integer

private
  variable
    lower middle upper : Nat

filter : {element : Set} → (element → Bool) → List element → List element
filter predicate [] = []
filter predicate (head ∷ tail) with predicate head
... | true = head ∷ filter predicate tail
... | false = filter predicate tail

lookup : {element : Set} → (values : List element) → Fin (length values) → element
lookup [] ()
lookup (head ∷ tail) fzero = head
lookup (head ∷ tail) (fsuc index) = lookup tail index

chainCondition : Matrix lower middle → Matrix middle upper → Bool
chainCondition {lower} {upper = upper} boundary nextBoundary =
  matrix_equal (product boundary nextBoundary) (zeroMatrix lower upper)

kernelIndices : {rows columns : Nat} → Matrix rows columns → List (Fin columns)
kernelIndices {columns = columns} smithMatrix = filter
  (λ index → not (Integer.natural_less (fin_to_nat index)
    (length (smithDiagonal smithMatrix)))) (all_fin columns)

-- The right basis supplies a kernel basis for the first boundary map.
-- Move the second map into this basis, then retain its kernel coordinates.
kernelPresentation : (indices : List (Fin middle)) → Matrix middle upper →
  Matrix upper (length indices)
kernelPresentation {upper = upper} indices transformedNext = transpose
  (tabulate (length indices) upper
    (λ index currentColumn → entry transformedNext (lookup indices index) currentColumn))

zeroNonkernelRows : Nat → Matrix middle upper → Bool
zeroNonkernelRows {middle} {upper} boundaryRank transformedNext = all
  (λ currentRow → rowValue currentRow) (all_fin middle)
  where
  rowValue : Fin middle → Bool
  rowValue currentRow with Integer.natural_less (fin_to_nat currentRow) boundaryRank
  ... | false = true
  ... | true = all (λ currentColumn → Integer.integer_equal
    (entry transformedNext currentRow currentColumn) (pos zero)) (all_fin upper)

finishInKernel : Nat → Matrix lower middle → Matrix middle upper → Maybe AbelianGroup
finishInKernel fuel smithMatrix transformedNext
  with zeroNonkernelRows (length (smithDiagonal smithMatrix)) transformedNext
... | false = nothing
... | true = groupFromPresentation fuel
  (kernelPresentation (kernelIndices smithMatrix) transformedNext)

homologyInSmithBasis : Nat → (boundary : Matrix lower middle) →
  Matrix middle upper → SmithCertificate boundary → Maybe AbelianGroup
homologyInSmithBasis fuel boundary nextBoundary smithResult = finishInKernel fuel
  (reduced_matrix (smith_state smithResult))
  (product (right_basis_inverse (smith_state smithResult)) nextBoundary)

-- Failure to satisfy ∂∘∂=0 is distinct from a homology group: no matrix
-- pair that is not a chain complex is accepted.
chainHomology : Nat → Matrix lower middle → Matrix middle upper → Maybe AbelianGroup
chainHomology fuel boundary nextBoundary with chainCondition boundary nextBoundary
... | false = nothing
... | true with smithNormalForm fuel boundary
... | nothing = nothing
... | just smithResult = homologyInSmithBasis fuel boundary nextBoundary smithResult
