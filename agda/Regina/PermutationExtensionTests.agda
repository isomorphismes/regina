{-# OPTIONS --safe --without-K #-}

-- Computation checks for appending fixed permutation labels.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission.
-- Translation changes: 2026-10-12. See ../../LICENSE.txt.

module Regina.PermutationExtensionTests where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.PermutationExtension

private
  extendedImages : List Nat → Maybe (List Nat)
  extendedImages inputImages with from_image_list 3 inputImages
  ... | nothing = nothing
  ... | just currentPermutation = just (image_table (extendPermutation currentPermutation))

  twiceExtendedImages : List Nat → Maybe (List Nat)
  twiceExtendedImages inputImages with from_image_list 3 inputImages
  ... | nothing = nothing
  ... | just currentPermutation = just
    (image_table (extendPermutation (extendPermutation currentPermutation)))

  extendedInverseImages : List Nat → Maybe (List Nat)
  extendedInverseImages inputImages with from_image_list 3 inputImages
  ... | nothing = nothing
  ... | just currentPermutation = just
    (image_table (inverse (extendPermutation currentPermutation)))

all_six_triangle_permutations_keep_the_new_fourth_label_fixed :
  map extendedImages
    ((0 ∷ 1 ∷ 2 ∷ []) ∷ (0 ∷ 2 ∷ 1 ∷ []) ∷
     (1 ∷ 0 ∷ 2 ∷ []) ∷ (1 ∷ 2 ∷ 0 ∷ []) ∷
     (2 ∷ 0 ∷ 1 ∷ []) ∷ (2 ∷ 1 ∷ 0 ∷ []) ∷ []) ≡
    (just (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ∷ just (0 ∷ 2 ∷ 1 ∷ 3 ∷ []) ∷
     just (1 ∷ 0 ∷ 2 ∷ 3 ∷ []) ∷ just (1 ∷ 2 ∷ 0 ∷ 3 ∷ []) ∷
     just (2 ∷ 0 ∷ 1 ∷ 3 ∷ []) ∷ just (2 ∷ 1 ∷ 0 ∷ 3 ∷ []) ∷ [])
all_six_triangle_permutations_keep_the_new_fourth_label_fixed = refl

successive_extensions_keep_both_new_labels_fixed :
  twiceExtendedImages (1 ∷ 2 ∷ 0 ∷ []) ≡ just (1 ∷ 2 ∷ 0 ∷ 3 ∷ 4 ∷ [])
successive_extensions_keep_both_new_labels_fixed = refl

extension_inverse_retains_the_original_inverse_action :
  extendedInverseImages (1 ∷ 2 ∷ 0 ∷ []) ≡ just (2 ∷ 0 ∷ 1 ∷ 3 ∷ [])
extension_inverse_retains_the_original_inverse_action = refl

empty_permutation_extends_to_a_single_fixed_label :
  image_table (extendPermutation (identity {zero})) ≡ (0 ∷ [])
empty_permutation_extends_to_a_single_fixed_label = refl

single_label_permutation_extends_to_identity_on_two_labels :
  image_table (extendPermutation (identity {1})) ≡ (0 ∷ 1 ∷ [])
single_label_permutation_extends_to_identity_on_two_labels = refl
