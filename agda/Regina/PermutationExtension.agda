{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- The one-new-vertex case of Regina Perm<n>::extend(Perm<k>).
-- Source: engine/maths/perm.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission.

module Regina.PermutationExtension where

open import Regina.Foundation
open import Regina.Permutation

-- Keep existing labels unchanged when appending a new final label.
includeInitialIndex : {number_of_vertices : Nat} →
  Fin number_of_vertices → Fin (suc number_of_vertices)
includeInitialIndex {suc remaining} fzero = fzero
includeInitialIndex {suc remaining} (fsuc currentIndex) =
  fsuc (includeInitialIndex currentIndex)

finalIndex : (number_of_vertices : Nat) → Fin (suc number_of_vertices)
finalIndex zero = fzero
finalIndex (suc remaining) = fsuc (finalIndex remaining)

-- Every enlarged index is an old index or the newly appended final one.
data AppendView (number_of_vertices : Nat) :
  Fin (suc number_of_vertices) → Set where
  initial_position : (currentIndex : Fin number_of_vertices) →
    AppendView number_of_vertices (includeInitialIndex currentIndex)
  final_position : AppendView number_of_vertices (finalIndex number_of_vertices)

appendView : (number_of_vertices : Nat) →
  (currentIndex : Fin (suc number_of_vertices)) →
  AppendView number_of_vertices currentIndex
appendView zero fzero = final_position
appendView (suc remaining) fzero = initial_position fzero
appendView (suc remaining) (fsuc currentIndex)
  with appendView remaining currentIndex
... | initial_position oldIndex = initial_position (fsuc oldIndex)
... | final_position = final_position

appendViewInitial : {number_of_vertices : Nat}
  (currentIndex : Fin number_of_vertices) →
  appendView number_of_vertices (includeInitialIndex currentIndex) ≡
    initial_position currentIndex
appendViewInitial {suc remaining} fzero = refl
appendViewInitial {suc remaining} (fsuc currentIndex)
  rewrite appendViewInitial currentIndex = refl

appendViewFinal : (number_of_vertices : Nat) →
  appendView number_of_vertices (finalIndex number_of_vertices) ≡ final_position
appendViewFinal zero = refl
appendViewFinal (suc remaining) rewrite appendViewFinal remaining = refl

extendIndexFunction : {number_of_vertices : Nat} →
  (Fin number_of_vertices → Fin number_of_vertices) →
  Fin (suc number_of_vertices) → Fin (suc number_of_vertices)
extendIndexFunction {number_of_vertices} currentMapping currentIndex
  with appendView number_of_vertices currentIndex
... | initial_position oldIndex = includeInitialIndex (currentMapping oldIndex)
... | final_position = finalIndex number_of_vertices

extendedFunctionInitial : {number_of_vertices : Nat}
  (currentMapping : Fin number_of_vertices → Fin number_of_vertices)
  (currentIndex : Fin number_of_vertices) →
  extendIndexFunction currentMapping (includeInitialIndex currentIndex) ≡
    includeInitialIndex (currentMapping currentIndex)
extendedFunctionInitial currentMapping currentIndex
  rewrite appendViewInitial currentIndex = refl

extendedFunctionFinal : {number_of_vertices : Nat}
  (currentMapping : Fin number_of_vertices → Fin number_of_vertices) →
  extendIndexFunction currentMapping (finalIndex number_of_vertices) ≡
    finalIndex number_of_vertices
extendedFunctionFinal {number_of_vertices} currentMapping
  rewrite appendViewFinal number_of_vertices = refl

private
  extendedRoundTrip : {number_of_vertices : Nat}
    (forward backward : Fin number_of_vertices → Fin number_of_vertices)
    (roundTrip : (currentIndex : Fin number_of_vertices) →
      backward (forward currentIndex) ≡ currentIndex)
    (currentIndex : Fin (suc number_of_vertices)) →
    extendIndexFunction backward (extendIndexFunction forward currentIndex) ≡
      currentIndex
  extendedRoundTrip {number_of_vertices} forward backward roundTrip currentIndex
    with appendView number_of_vertices currentIndex
  ... | initial_position oldIndex = trans
    (extendedFunctionInitial backward (forward oldIndex))
    (cong includeInitialIndex (roundTrip oldIndex))
  ... | final_position = extendedFunctionFinal backward

-- The inverse laws are inherited by proof, without exhaustive recertification.
extendPermutation : {number_of_vertices : Nat} →
  Permutation number_of_vertices → Permutation (suc number_of_vertices)
extendPermutation currentPermutation = permutation
  (extendIndexFunction (image currentPermutation))
  (extendIndexFunction (preimage currentPermutation))
  (extendedRoundTrip
    (image currentPermutation) (preimage currentPermutation)
    (preimage_image currentPermutation))
  (extendedRoundTrip
    (preimage currentPermutation) (image currentPermutation)
    (image_preimage currentPermutation))

extensionPreservesInitialImage : {number_of_vertices : Nat}
  (currentPermutation : Permutation number_of_vertices)
  (currentIndex : Fin number_of_vertices) →
  image (extendPermutation currentPermutation) (includeInitialIndex currentIndex) ≡
    includeInitialIndex (image currentPermutation currentIndex)
extensionPreservesInitialImage currentPermutation =
  extendedFunctionInitial (image currentPermutation)

extensionFixesFinalIndex : {number_of_vertices : Nat}
  (currentPermutation : Permutation number_of_vertices) →
  image (extendPermutation currentPermutation) (finalIndex number_of_vertices) ≡
    finalIndex number_of_vertices
extensionFixesFinalIndex currentPermutation =
  extendedFunctionFinal (image currentPermutation)

extensionCommutesWithInverse : {number_of_vertices : Nat}
  (currentPermutation : Permutation number_of_vertices) →
  SameImages (extendPermutation (inverse currentPermutation))
    (inverse (extendPermutation currentPermutation))
extensionCommutesWithInverse currentPermutation currentIndex = refl

extensionPreservesIdentity : {number_of_vertices : Nat} →
  SameImages (extendPermutation (identity {number_of_vertices})) identity
extensionPreservesIdentity {number_of_vertices} currentIndex
  with appendView number_of_vertices currentIndex
... | initial_position oldIndex = refl
... | final_position = refl

extensionPreservesComposition : {number_of_vertices : Nat}
  (leftPermutation rightPermutation : Permutation number_of_vertices) →
  SameImages (extendPermutation (compose leftPermutation rightPermutation))
    (compose (extendPermutation leftPermutation) (extendPermutation rightPermutation))
extensionPreservesComposition {number_of_vertices}
  leftPermutation rightPermutation currentIndex
  with appendView number_of_vertices currentIndex
... | initial_position oldIndex = sym
  (extendedFunctionInitial (image leftPermutation) (image rightPermutation oldIndex))
... | final_position = sym (extendedFunctionFinal (image leftPermutation))
