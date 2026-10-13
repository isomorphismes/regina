{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- Checked semantics of Perm<n>::contract() in engine/maths/perm.h.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.PermutationContraction where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.PermutationExtension

record Contraction {number_of_vertices : Nat}
  (original : Permutation (suc number_of_vertices)) : Set where
  constructor contraction
  field
    contracted_permutation : Permutation number_of_vertices
    contraction_preserves_images :
      SameImages (extendPermutation contracted_permutation) original
open Contraction public

private
  takeImages : {element : Set} → Nat → List element → List element
  takeImages zero values = []
  takeImages (suc remaining) [] = []
  takeImages (suc remaining) (value ∷ values) =
    value ∷ takeImages remaining values

-- Regina assumes the initial labels are preserved as a set. The Agda
-- entry point checks this precondition and carries the image agreement.
contractPermutation : {number_of_vertices : Nat} →
  (original : Permutation (suc number_of_vertices)) →
  Maybe (Contraction original)
contractPermutation {number_of_vertices} original
  with from_image_list number_of_vertices
    (takeImages number_of_vertices (image_table original))
... | nothing = nothing
... | just restricted with permutation_dec_equal
    (extendPermutation restricted) original
... | no disagreement = nothing
... | yes agreement = just (contraction restricted agreement)

contractionCarriesInitialVertex : {number_of_vertices : Nat}
  {original : Permutation (suc number_of_vertices)} →
  (result : Contraction original) (vertex : Fin number_of_vertices) →
  image original (includeInitialIndex vertex) ≡
    includeInitialIndex (image (contracted_permutation result) vertex)
contractionCarriesInitialVertex result vertex = trans
  (sym (contraction_preserves_images result (includeInitialIndex vertex)))
  (extensionPreservesInitialImage (contracted_permutation result) vertex)

contractionFixesFinalVertex : {number_of_vertices : Nat}
  {original : Permutation (suc number_of_vertices)} →
  (result : Contraction original) →
  image original (finalIndex number_of_vertices) ≡ finalIndex number_of_vertices
contractionFixesFinalVertex result = trans
  (sym (contraction_preserves_images result (finalIndex _)))
  (extensionFixesFinalIndex (contracted_permutation result))
