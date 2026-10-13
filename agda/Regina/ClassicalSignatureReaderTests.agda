{-# OPTIONS --safe --without-K #-}
module Regina.ClassicalSignatureReaderTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Skeleton using (face_class_count; count_matching)
open import Regina.SignatureDecoding
open import Regina.ClassicalSignatureReader
open import Regina.IsomorphismSignature using (classical_signature)
open import Agda.Builtin.String using (String)
import Regina.Components as Components
import Regina.Validity3 as Validity

private
  read_size : Nat → String → Maybe Nat
  read_size requestedDimension signatureText with read_classical_signature requestedDimension signatureText
  ... | nothing = nothing
  ... | just decodedValue = just (decoded_simplex_count decodedValue)

  round_trip : Nat → String → Maybe String
  round_trip requestedDimension signatureText with read_classical_signature requestedDimension signatureText
  ... | nothing = nothing
  ... | just decodedValue = classical_signature true (decoded_tri decodedValue)

  read_components_count : String → Maybe Nat
  read_components_count signatureText with read_classical_signature 3 signatureText
  ... | nothing = nothing
  ... | just decodedValue = just (length (Components.simplexComponents (decoded_tri decodedValue)))

  read_unpaired : String → Maybe Nat
  read_unpaired signatureText with read_classical_signature 3 signatureText
  ... | nothing = nothing
  ... | just decodedValue = just (unpaired_facet_count (decoded_tri decodedValue))

  read_facet_locks : String → Maybe Nat
  read_facet_locks signatureText with read_classical_signature 3 signatureText
  ... | nothing = nothing
  ... | just decodedValue = just (count_matching
      (facet_is_locked (raw_state (decoded_tri decodedValue)))
      (all_facets 3 (decoded_simplex_count decodedValue)))

  read_faces : String → Maybe (List Nat)
  read_faces signatureText with read_classical_signature 3 signatureText
  ... | nothing = nothing
  ... | just decodedValue = just (map (face_class_count (decoded_tri decodedValue)) (0 ∷ 1 ∷ 2 ∷ []))

empty_signature_decodes_to_zero_simplices : read_size 3 "a" ≡ just 0
empty_signature_decodes_to_zero_simplices = refl

ball_signature_decodes_to_one_tetrahedron : read_size 3 "baa" ≡ just 1
ball_signature_decodes_to_one_tetrahedron = refl

ball_reader_recovers_four_boundary_facets : read_unpaired "baa" ≡ just 4
ball_reader_recovers_four_boundary_facets = refl

ball_reader_recovers_actual_face_quotients : read_faces "baa" ≡ just (4 ∷ 6 ∷ 4 ∷ [])
ball_reader_recovers_actual_face_quotients = refl

sphere_reader_recovers_six_edges : read_faces "cPcbbbaaa" ≡ just (4 ∷ 6 ∷ 4 ∷ [])
sphere_reader_recovers_six_edges = refl

solid_torus_reader_round_trip : round_trip 3 "bGaj" ≡ just "bGaj"
solid_torus_reader_round_trip = refl

figure_eight_reader_round_trip : round_trip 3 "cPcbbbiht" ≡ just "cPcbbbiht"
figure_eight_reader_round_trip = refl

two_sphere_reader_round_trip : round_trip 2 "cPbbaa" ≡ just "cPbbaa"
two_sphere_reader_round_trip = refl

four_sphere_reader_round_trip : round_trip 4 "cPkbbbbaaaaaaaa" ≡ just "cPkbbbbaaaaaaaa"
four_sphere_reader_round_trip = refl

disconnected_components_keep_separate_indices : read_components_count "baabaa" ≡ just 2
disconnected_components_keep_separate_indices = refl

disconnected_signature_round_trip : round_trip 3 "baabaa" ≡ just "baabaa"
disconnected_signature_round_trip = refl

simplex_lock_reader_round_trip : round_trip 3 "baa.q" ≡ just "baa.q"
simplex_lock_reader_round_trip = refl

facet_lock_reader_round_trip : round_trip 3 "baa.b" ≡ just "baa.b"
facet_lock_reader_round_trip = refl

paired_facet_locks_are_read_on_both_sides : read_facet_locks "cPcbbbaaa.bb" ≡ just 2
paired_facet_locks_are_read_on_both_sides = refl

inconsistent_paired_facet_locks_are_rejected : read_size 3 "cPcbbbaaa.ba" ≡ nothing
inconsistent_paired_facet_locks_are_rejected = refl

out_of_range_lock_bits_are_rejected : read_size 3 "baa.G" ≡ nothing
out_of_range_lock_bits_are_rejected = refl

incomplete_facet_actions_are_rejected : read_size 3 "ba" ≡ nothing
incomplete_facet_actions_are_rejected = refl

nonzero_padding_trits_are_rejected : read_size 3 "bae" ≡ nothing
nonzero_padding_trits_are_rejected = refl

excess_facet_weight_is_rejected : read_size 3 "bac" ≡ nothing
excess_facet_weight_is_rejected = refl

out_of_range_permutation_indices_are_rejected : read_size 3 "bcaZ" ≡ nothing
out_of_range_permutation_indices_are_rejected = refl

gluing_to_an_unseen_simplex_is_rejected : read_size 3 "bcbg" ≡ nothing
gluing_to_an_unseen_simplex_is_rejected = refl

too_many_new_simplices_are_rejected : read_size 3 "bba" ≡ nothing
too_many_new_simplices_are_rejected = refl

facet_gluing_to_itself_is_rejected : read_size 3 "bcab" ≡ nothing
facet_gluing_to_itself_is_rejected = refl

empty_signature_cannot_have_a_second_component : read_size 3 "abaa" ≡ nothing
empty_signature_cannot_have_a_second_component = refl

invalid_base64_character_is_rejected : read_size 3 "b?a" ≡ nothing
invalid_base64_character_is_rejected = refl

empty_text_is_rejected : read_size 3 "" ≡ nothing
empty_text_is_rejected = refl

second_generation_input_is_not_misread_as_classical : read_size 3 "cV6cqb" ≡ nothing
second_generation_input_is_not_misread_as_classical = refl

surrounding_whitespace_is_accepted : read_size 3 "\t baa \n" ≡ just 1
surrounding_whitespace_is_accepted = refl

interior_whitespace_is_rejected : read_size 3 "b aa" ≡ nothing
interior_whitespace_is_rejected = refl

long_form_zero_width_empty_signature_matches_source_decoder : read_size 3 "-a" ≡ just 0
long_form_zero_width_empty_signature_matches_source_decoder = refl
