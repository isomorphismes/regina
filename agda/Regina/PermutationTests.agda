{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-09. License: ../../LICENSE.txt.

-- Reduction tests for the Regina permutation translation.
-- Copyright (c) 1999-2026, Ben Burton, for the Regina source being translated.
-- Distributed under GPL-2.0-or-later, with Regina's online distribution
-- exception. See ../../LICENSE.txt for the full terms and acknowledgements.

module Regina.PermutationTests where

open import Regina.Foundation
open import Regina.Permutation

private
  vertex_zero vertex_one vertex_two vertex_three : Fin 4
  vertex_zero = fzero
  vertex_one = fsuc fzero
  vertex_two = fsuc (fsuc fzero)
  vertex_three = fsuc (fsuc (fsuc fzero))

  cycle_forward : Fin 4 → Fin 4
  cycle_forward fzero = vertex_one
  cycle_forward (fsuc fzero) = vertex_two
  cycle_forward (fsuc (fsuc fzero)) = vertex_three
  cycle_forward (fsuc (fsuc (fsuc fzero))) = vertex_zero

  candidate_table : {number_of_vertices : Nat} →
                    Maybe (Permutation number_of_vertices) → Maybe (List Nat)
  candidate_table nothing = nothing
  candidate_table (just candidate) = just (image_table candidate)

  candidate_inverse_table : {number_of_vertices : Nat} →
                            Maybe (Permutation number_of_vertices) → Maybe (List Nat)
  candidate_inverse_table nothing = nothing
  candidate_inverse_table (just candidate) = just (image_table (inverse candidate))

  candidate_composition_table : {number_of_vertices : Nat} →
                                Maybe (Permutation number_of_vertices) →
                                Maybe (Permutation number_of_vertices) → Maybe (List Nat)
  candidate_composition_table (just left) (just right) =
    just (image_table (compose left right))
  candidate_composition_table nothing _ = nothing
  candidate_composition_table (just _) nothing = nothing

  cycle_candidate swap_candidate : Maybe (Permutation 4)
  cycle_candidate = from_image_list 4 (1 ∷ 2 ∷ 3 ∷ 0 ∷ [])
  swap_candidate = from_image_list 4 (1 ∷ 0 ∷ 2 ∷ 3 ∷ [])

empty_permutation_accepted :
  candidate_table (from_image_list 0 []) ≡ just []
empty_permutation_accepted = refl

singleton_permutation_accepted :
  candidate_table (from_image_list 1 (0 ∷ [])) ≡ just (0 ∷ [])
singleton_permutation_accepted = refl

four_cycle_imported :
  candidate_table cycle_candidate ≡ just (1 ∷ 2 ∷ 3 ∷ 0 ∷ [])
four_cycle_imported = refl

four_cycle_inverse_computed :
  candidate_inverse_table cycle_candidate ≡ just (3 ∷ 0 ∷ 1 ∷ 2 ∷ [])
four_cycle_inverse_computed = refl

four_cycle_from_function :
  candidate_table (from_image_function cycle_forward) ≡
    just (1 ∷ 2 ∷ 3 ∷ 0 ∷ [])
four_cycle_from_function = refl

composition_acts_right_first :
  candidate_composition_table cycle_candidate swap_candidate ≡
    just (2 ∷ 1 ∷ 3 ∷ 0 ∷ [])
composition_acts_right_first = refl

composition_order_matters :
  candidate_composition_table swap_candidate cycle_candidate ≡
    just (0 ∷ 2 ∷ 3 ∷ 1 ∷ [])
composition_order_matters = refl

duplicate_images_rejected :
  from_image_list 4 (0 ∷ 0 ∷ 2 ∷ 3 ∷ []) ≡ nothing
duplicate_images_rejected = refl

out_of_range_image_rejected :
  from_image_list 4 (0 ∷ 1 ∷ 2 ∷ 4 ∷ []) ≡ nothing
out_of_range_image_rejected = refl

short_table_rejected :
  from_image_list 4 (0 ∷ 1 ∷ 2 ∷ []) ≡ nothing
short_table_rejected = refl

long_table_rejected :
  from_image_list 4 (0 ∷ 1 ∷ 2 ∷ 3 ∷ 0 ∷ []) ≡ nothing
long_table_rejected = refl

incorrect_inverse_rejected :
  make_permutation cycle_forward cycle_forward ≡ nothing
incorrect_inverse_rejected = refl

identity_table_checked : image_table (identity {4}) ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
identity_table_checked = refl

identity_equality_checked : permutation_equal (identity {4}) identity ≡ true
identity_equality_checked = refl

finite_enumeration_checked :
  map fin_to_nat (all_fin 4) ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
finite_enumeration_checked = refl

upper_bound_rejected : fin_from_nat 4 4 ≡ nothing
upper_bound_rejected = refl
