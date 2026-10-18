{-# OPTIONS --safe --without-K #-}

-- Reduction tests for Regina's printable second-generation signatures.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-18.

module Regina.SecondGenerationSignatureTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.SignatureDecoding
open import Regina.SecondGenerationSignature3
open import Regina.Skeleton using (face_class_count; count_matching)
open import Agda.Builtin.String using (String)
import Regina.ClassicalSignatureReader as Classical
import Regina.Components as Components
import Regina.IsomorphismSignature as ClassicalSignatures
import Regina.Validity3 as Validity

private
  read_size : String → Maybe Nat
  read_size signatureText with
    read_second_generation_signature3 signatureText
  ... | nothing = nothing
  ... | just decodedValue = just
    (Classical.decoded_simplex_count decodedValue)

  round_trip_to_classical : String → Maybe String
  round_trip_to_classical signatureText with
    read_second_generation_signature3 signatureText
  ... | nothing = nothing
  ... | just decodedValue = ClassicalSignatures.classical_signature true
    (Classical.decoded_tri decodedValue)

  read_component_count : String → Maybe Nat
  read_component_count signatureText with
    read_second_generation_signature3 signatureText
  ... | nothing = nothing
  ... | just decodedValue = just (length
    (Components.simplexComponents (Classical.decoded_tri decodedValue)))

  read_unpaired : String → Maybe Nat
  read_unpaired signatureText with
    read_second_generation_signature3 signatureText
  ... | nothing = nothing
  ... | just decodedValue = just
    (unpaired_facet_count (Classical.decoded_tri decodedValue))

  read_simplex_locks : String → Maybe Nat
  read_simplex_locks signatureText with
    read_second_generation_signature3 signatureText
  ... | nothing = nothing
  ... | just decodedValue = just (count_matching
    (simplex_is_locked (raw_state (Classical.decoded_tri decodedValue)))
    (all_fin (Classical.decoded_simplex_count decodedValue)))

  read_faces : String → Maybe (List Nat)
  read_faces signatureText with
    read_second_generation_signature3 signatureText
  ... | nothing = nothing
  ... | just decodedValue = just (map
    (face_class_count (Classical.decoded_tri decodedValue))
    (0 ∷ 1 ∷ 2 ∷ []))

  read_validity : String → Maybe Bool
  read_validity signatureText with
    read_second_generation_signature3 signatureText
  ... | nothing = nothing
  ... | just decodedValue = just
    (Validity.threeDimensionalValidityValue
      (Classical.decoded_tri decodedValue))

low_order_bits_are_decoded_first :
  decode_bits 2 (bit_cursor ('V' ∷ []) zero) ≡
    just (bit_parsed 3 (bit_cursor ('V' ∷ []) 2))
low_order_bits_are_decoded_first = refl

six_bits_consume_one_character :
  decode_bits 6 (bit_cursor ('q' ∷ []) zero) ≡
    just (bit_parsed 16 (bit_cursor [] zero))
six_bits_consume_one_character = refl

zero_padding_is_accepted :
  flush_zero_padding (bit_cursor ('q' ∷ []) 5) ≡
    just (bit_cursor [] zero)
zero_padding_is_accepted = refl

nonzero_padding_is_rejected :
  flush_zero_padding (bit_cursor ('-' ∷ []) 5) ≡ nothing
nonzero_padding_is_rejected = refl

three_values_need_two_bits : bits_required 3 ≡ 2
three_values_need_two_bits = refl

twenty_four_permutations_need_five_bits : bits_required 24 ≡ 5
twenty_four_permutations_need_five_bits = refl

sign_index_two_maps_to_lexicographic_three : sn4_to_ordered_index 2 ≡ 3
sign_index_two_maps_to_lexicographic_three = refl

sign_index_three_maps_to_lexicographic_two : sn4_to_ordered_index 3 ≡ 2
sign_index_three_maps_to_lexicographic_two = refl

empty_signature_decodes_to_zero_simplices : read_size "a" ≡ just 0
empty_signature_decodes_to_zero_simplices = refl

ball_signature_decodes_to_one_tetrahedron : read_size "b-F" ≡ just 1
ball_signature_decodes_to_one_tetrahedron = refl

ball_signature_recovers_four_boundary_facets : read_unpaired "b-F" ≡ just 4
ball_signature_recovers_four_boundary_facets = refl

ball_signature_recovers_face_quotients :
  read_faces "b-F" ≡ just (4 ∷ 6 ∷ 4 ∷ [])
ball_signature_recovers_face_quotients = refl

ball_converts_to_classical_signature :
  round_trip_to_classical "b-F" ≡ just "baa"
ball_converts_to_classical_signature = refl

two_ball_components_remain_separate :
  read_component_count "b-Fb-F" ≡ just 2
two_ball_components_remain_separate = refl

two_ball_components_convert_to_classical_signature :
  round_trip_to_classical "b-Fb-F" ≡ just "baabaa"
two_ball_components_convert_to_classical_signature = refl

figure_eight_signature_decodes_to_two_tetrahedra :
  read_size "cV6cqb" ≡ just 2
figure_eight_signature_decodes_to_two_tetrahedra = refl

figure_eight_signature_has_no_boundary_facets :
  read_unpaired "cV6cqb" ≡ just 0
figure_eight_signature_has_no_boundary_facets = refl

figure_eight_signature_recovers_face_quotients :
  read_faces "cV6cqb" ≡ just (1 ∷ 2 ∷ 4 ∷ [])
figure_eight_signature_recovers_face_quotients = refl

figure_eight_converts_to_source_classical_signature :
  round_trip_to_classical "cV6cqb" ≡ just "cPcbbbiht"
figure_eight_converts_to_source_classical_signature = refl

locked_figure_eight_recovers_one_simplex_lock :
  read_simplex_locks "cV6cqb.ai" ≡ just 1
locked_figure_eight_recovers_one_simplex_lock = refl

locked_figure_eight_converts_with_lock_suffix :
  round_trip_to_classical "cV6cqb.ai" ≡ just "cPcbbbiht.aq"
locked_figure_eight_converts_with_lock_suffix = refl

figure_eight_decodes_as_valid : read_validity "cV6cqb" ≡ just true
figure_eight_decodes_as_valid = refl

nonorientable_nine_tetrahedron_signature_decodes :
  read_size "jdcXQdpe-d0I3yicnqBb" ≡ just 9
nonorientable_nine_tetrahedron_signature_decodes = refl

surrounding_whitespace_is_accepted :
  read_size "\t cV6cqb \n" ≡ just 2
surrounding_whitespace_is_accepted = refl

classical_signature_is_not_misread_as_second_generation :
  read_size "cPcbbbiht" ≡ nothing
classical_signature_is_not_misread_as_second_generation = refl

truncated_second_generation_signature_is_rejected :
  read_size "cV6" ≡ nothing
truncated_second_generation_signature_is_rejected = refl

invalid_base64_character_is_rejected : read_size "cV?cqb" ≡ nothing
invalid_base64_character_is_rejected = refl

nonzero_final_padding_is_rejected : read_size "b--" ≡ nothing
nonzero_final_padding_is_rejected = refl
