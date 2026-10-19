{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-18. License: ../../LICENSE.txt.
-- Base64BitDecoder and TriangulationBase<3>::fillComponentFromSig2(),
-- engine/utilities/sigutils.h and engine/triangulation/detail/isosig-impl.h.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.SecondGenerationSignature3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.SignatureEncoding
open import Regina.SignatureDecoding
open import Regina.Skeleton using (less_than)
open import Agda.Builtin.Char using (Char; primCharToNat)
open import Agda.Builtin.Nat using (_-_)
open import Agda.Builtin.String using (String; primStringToList)
import Regina.ClassicalSignatureReader as Classical

record BitCursor : Set where
  constructor bit_cursor
  field
    bit_characters : List Char
    consumed_low_bits : Nat
open BitCursor public

record BitParsed (element : Set) : Set where
  constructor bit_parsed
  field
    bit_value : element
    remaining_bits : BitCursor
open BitParsed public

-- Regina's bit streams store low-order bits first inside each base64
-- character.  The cursor retains the current character until all six bits
-- have been consumed, which also lets us enforce zero padding at boundaries.
decode_bit : BitCursor → Maybe (BitParsed Nat)
decode_bit (bit_cursor [] currentOffset) = nothing
decode_bit (bit_cursor (headCharacter ∷ remainingCharacters) currentOffset)
  with less_than currentOffset 6 | decode_character headCharacter
... | false | _ = nothing
... | true | nothing = nothing
... | true | just characterNumber
  with small_remainder
    (small_quotient characterNumber (power_of_two currentOffset)) 2 |
    nat_equal currentOffset 5
... | currentBit | true = just
  (bit_parsed currentBit (bit_cursor remainingCharacters zero))
... | currentBit | false = just
  (bit_parsed currentBit
    (bit_cursor (headCharacter ∷ remainingCharacters) (suc currentOffset)))

decode_bits : Nat → BitCursor → Maybe (BitParsed Nat)
decode_bits zero currentCursor = just (bit_parsed zero currentCursor)
decode_bits (suc remainingWidth) currentCursor with decode_bit currentCursor
... | nothing = nothing
... | just firstResult with decode_bits remainingWidth
  (remaining_bits firstResult)
... | nothing = nothing
... | just remainingResult = just (bit_parsed
  (bit_value firstResult + 2 * bit_value remainingResult)
  (remaining_bits remainingResult))

decode_bit_numbers : Nat → Nat → BitCursor → Maybe (BitParsed (List Nat))
decode_bit_numbers zero bitWidth currentCursor =
  just (bit_parsed [] currentCursor)
decode_bit_numbers (suc remainingNumbers) bitWidth currentCursor
  with decode_bits bitWidth currentCursor
... | nothing = nothing
... | just firstResult with decode_bit_numbers remainingNumbers bitWidth
  (remaining_bits firstResult)
... | nothing = nothing
... | just remainingResult = just (bit_parsed
  (bit_value firstResult ∷ bit_value remainingResult)
  (remaining_bits remainingResult))

flush_zero_padding : BitCursor → Maybe BitCursor
flush_zero_padding currentCursor@(bit_cursor currentCharacters zero) =
  just currentCursor
flush_zero_padding (bit_cursor [] (suc currentOffset)) = nothing
flush_zero_padding
  (bit_cursor (headCharacter ∷ remainingCharacters) (suc currentOffset))
  with decode_character headCharacter
... | nothing = nothing
... | just characterNumber with nat_equal
  (small_quotient characterNumber (power_of_two (suc currentOffset))) zero
... | false = nothing
... | true = just (bit_cursor remainingCharacters zero)

bit_width_steps : Nat → Nat → Nat
bit_width_steps zero currentNumber = zero
bit_width_steps (suc remainingSteps) zero = zero
bit_width_steps (suc remainingSteps) currentNumber@(suc _) =
  suc (bit_width_steps remainingSteps (small_quotient currentNumber 2))

-- This is utilities/intutils.h::bitsRequired(): the bit width of n - 1.
bits_required : Nat → Nat
bits_required currentNumber =
  bit_width_steps currentNumber (currentNumber - 1)

reverse_list : {element : Set} → List element → List element
reverse_list [] = []
reverse_list (headElement ∷ remainingElements) =
  reverse_list remainingElements ++ (headElement ∷ [])

record DestinationData : Set where
  constructor destination_result
  field
    decoded_destinations : List Nat
    represented_facet_sides : Nat
    boundary_destination_count : Nat
    after_destinations : BitCursor
open DestinationData public

read_destinations : Nat → Nat → Nat → Nat → Nat → Nat → BitCursor →
  Maybe DestinationData
read_destinations zero targetSides simplexCount bitWidth representedSides
  boundaryCount currentCursor with less_than representedSides targetSides
... | true = nothing
... | false = just (destination_result [] representedSides boundaryCount
  currentCursor)
read_destinations (suc remainingFuel) targetSides simplexCount bitWidth
  representedSides boundaryCount currentCursor
  with less_than representedSides targetSides
... | false = just (destination_result [] representedSides boundaryCount
  currentCursor)
... | true with decode_bits bitWidth currentCursor
... | nothing = nothing
... | just destinationResult
  with nat_equal (bit_value destinationResult) simplexCount
... | true with read_destinations remainingFuel targetSides simplexCount bitWidth
  (suc representedSides) (suc boundaryCount)
  (remaining_bits destinationResult)
... | nothing = nothing
... | just remainingResult = just (destination_result
  (bit_value destinationResult ∷ decoded_destinations remainingResult)
  (represented_facet_sides remainingResult)
  (boundary_destination_count remainingResult)
  (after_destinations remainingResult))
read_destinations (suc remainingFuel) targetSides simplexCount bitWidth
  representedSides boundaryCount currentCursor
  | true | just destinationResult | false
  with read_destinations remainingFuel targetSides simplexCount bitWidth
    (2 + representedSides) boundaryCount (remaining_bits destinationResult)
... | nothing = nothing
... | just remainingResult = just (destination_result
  (bit_value destinationResult ∷ decoded_destinations remainingResult)
  (represented_facet_sides remainingResult)
  (boundary_destination_count remainingResult)
  (after_destinations remainingResult))

facet_bit_count : DestinationData → Nat
facet_bit_count currentData = small_quotient
  (represented_facet_sides currentData +
    boundary_destination_count currentData) 2

join_count_base : DestinationData → Nat
join_count_base currentData =
  facet_bit_count currentData - boundary_destination_count currentData + 1

valid_join_count : Nat → DestinationData → Bool
valid_join_count simplexCount currentData =
  not (less_than (facet_bit_count currentData)
    (boundary_destination_count currentData)) and
  not (less_than (join_count_base currentData) simplexCount)

join_count : Nat → DestinationData → Nat
join_count simplexCount currentData =
  join_count_base currentData - simplexCount

permutation_bit_width : Bool → Nat
permutation_bit_width true = 4
permutation_bit_width false = 5

normalise_permutation_indices : Bool → List Nat → List Nat
normalise_permutation_indices false currentIndices = currentIndices
normalise_permutation_indices true currentIndices =
  map (λ currentIndex → 2 * currentIndex + 1) currentIndices

record SecondGenerationData : Set where
  constructor second_generation_payload
  field
    encoded_oriented : Bool
    encoded_facet_types : List Nat
    encoded_destinations : List Nat
    encoded_permutations : List Nat
    after_component_bits : BitCursor
open SecondGenerationData public

decodeAfterDestinations : Nat → Bool → DestinationData →
  Maybe SecondGenerationData
decodeAfterDestinations numberOfSimplices orientationFlag destinationPayload
  with decode_bit_numbers (facet_bit_count destinationPayload) 1
    (after_destinations destinationPayload)
... | nothing = nothing
... | just facetResult with valid_join_count numberOfSimplices destinationPayload
... | false = nothing
... | true with decode_bit_numbers (join_count numberOfSimplices destinationPayload)
  (permutation_bit_width orientationFlag) (remaining_bits facetResult)
... | nothing = nothing
... | just permutationResult = just (second_generation_payload orientationFlag
  (reverse_list (bit_value facetResult))
  (decoded_destinations destinationPayload)
  (normalise_permutation_indices orientationFlag (bit_value permutationResult))
  (remaining_bits permutationResult))

decodeAfterOrientation : Nat → Bool → BitCursor →
  Maybe SecondGenerationData
decodeAfterOrientation numberOfSimplices orientationFlag currentCursor
  with read_destinations (suc (4 * numberOfSimplices))
    (4 * numberOfSimplices) numberOfSimplices
    (bits_required (suc numberOfSimplices))
    (2 * (numberOfSimplices - 1)) zero currentCursor
... | nothing = nothing
... | just destinationResult =
  decodeAfterDestinations numberOfSimplices orientationFlag destinationResult

decode_component_bits : Nat → BitCursor → Maybe SecondGenerationData
decode_component_bits simplexCount currentCursor
  with decode_bits 2 currentCursor
... | nothing = nothing
... | just markerResult with nat_equal (bit_value markerResult) 3
... | false = nothing
... | true with decode_bits 1 (remaining_bits markerResult)
... | nothing = nothing
... | just orientationResult with nat_equal (bit_value orientationResult) 1
... | false = decodeAfterOrientation simplexCount false
  (remaining_bits orientationResult)
... | true = decodeAfterOrientation simplexCount true
  (remaining_bits orientationResult)

sn4_to_ordered_index : Nat → Nat
sn4_to_ordered_index currentIndex with small_remainder currentIndex 4
... | zero = currentIndex
... | suc zero = currentIndex
... | suc (suc zero) = suc currentIndex
... | suc (suc (suc _)) = currentIndex - 1

decoded_sn4_permutation : Nat → Maybe (Permutation 4)
decoded_sn4_permutation currentIndex with less_than currentIndex 24
... | false = nothing
... | true = Classical.decoded_permutation 4
  (sn4_to_ordered_index currentIndex)

swap_zero_one : Maybe (Permutation 4)
swap_zero_one = from_image_list 4 (1 ∷ 0 ∷ 2 ∷ 3 ∷ [])

record SecondDecodeState (simplexCount : Nat) : Set where
  constructor second_decode_state
  field
    second_triangulation : Triangulation 3 simplexCount
    second_next_unseen : Nat
    unused_facet_types : List Nat
    unused_second_destinations : List Nat
    unused_second_permutations : List Nat
open SecondDecodeState public

apply_second_action : {simplexCount : Nat} → Facet 3 simplexCount →
  SecondDecodeState simplexCount → Maybe (SecondDecodeState simplexCount)
apply_second_action {simplexCount} currentFacet currentState
  with unused_facet_types currentState
... | [] = nothing
... | zero ∷ remainingTypes with
  fin_from_nat simplexCount (second_next_unseen currentState) | swap_zero_one
... | nothing | _ = nothing
... | _ | nothing = nothing
... | just targetSimplex | just vertexMapping
  with join (second_triangulation currentState) currentFacet targetSimplex
    vertexMapping
... | rejected _ = nothing
... | accepted transitionValue = just (second_decode_state
  (resulting_triangulation transitionValue)
  (suc (second_next_unseen currentState)) remainingTypes
  (unused_second_destinations currentState)
  (unused_second_permutations currentState))
apply_second_action {simplexCount} currentFacet currentState
  | suc zero ∷ remainingTypes with unused_second_destinations currentState
... | [] = nothing
... | destinationNumber ∷ remainingDestinations
  with nat_equal destinationNumber simplexCount
... | true = just (second_decode_state (second_triangulation currentState)
  (second_next_unseen currentState) remainingTypes remainingDestinations
  (unused_second_permutations currentState))
... | false with unused_second_permutations currentState
... | [] = nothing
... | permutationNumber ∷ remainingPermutations
  with less_than destinationNumber (second_next_unseen currentState) |
    fin_from_nat simplexCount destinationNumber |
    decoded_sn4_permutation permutationNumber
... | false | _ | _ = nothing
... | _ | nothing | _ = nothing
... | _ | _ | nothing = nothing
... | true | just targetSimplex | just vertexMapping
  with join (second_triangulation currentState) currentFacet targetSimplex
    vertexMapping
... | rejected _ = nothing
... | accepted transitionValue = just (second_decode_state
  (resulting_triangulation transitionValue)
  (second_next_unseen currentState) remainingTypes remainingDestinations
  remainingPermutations)
apply_second_action currentFacet currentState | suc (suc _) ∷ remainingTypes =
  nothing

apply_second_facets : {simplexCount : Nat} → List (Facet 3 simplexCount) →
  SecondDecodeState simplexCount → Maybe (SecondDecodeState simplexCount)
apply_second_facets [] currentState = just currentState
apply_second_facets (currentFacet ∷ remainingFacets) currentState
  with is_paired (raw_state (second_triangulation currentState)) currentFacet
... | true = apply_second_facets remainingFacets currentState
... | false with apply_second_action currentFacet currentState
... | nothing = nothing
... | just nextState = apply_second_facets remainingFacets nextState

read_component_locks : {simplexCount : Nat} →
  Triangulation 3 simplexCount → BitCursor →
  Maybe (BitParsed (Classical.DecodedTriangulation 3))
read_component_locks {simplexCount} currentTriangulation
  currentCursor@(bit_cursor [] zero) = just (bit_parsed
  (Classical.decoded_triangulation simplexCount currentTriangulation)
  currentCursor)
read_component_locks {simplexCount} currentTriangulation
  currentCursor@(bit_cursor (headCharacter ∷ remainingCharacters) zero)
  with nat_equal (primCharToNat headCharacter) 46
... | false = just (bit_parsed
  (Classical.decoded_triangulation simplexCount currentTriangulation)
  currentCursor)
... | true with decode_bit_numbers simplexCount 5
  (bit_cursor remainingCharacters zero)
... | nothing = nothing
... | just masksResult with Classical.apply_masks currentTriangulation
  (bit_value masksResult)
... | nothing = nothing
... | just lockedTriangulation with flush_zero_padding
  (remaining_bits masksResult)
... | nothing = nothing
... | just alignedCursor = just (bit_parsed
  (Classical.decoded_triangulation simplexCount lockedTriangulation)
  alignedCursor)
read_component_locks currentTriangulation
  (bit_cursor currentCharacters (suc currentOffset)) = nothing

construct_component : (simplexCount : Nat) → SecondGenerationData →
  Maybe (BitParsed (Classical.DecodedTriangulation 3))
construct_component simplexCount currentData
  with apply_second_facets (all_facets 3 simplexCount)
    (second_decode_state (unpaired_simplices 3 simplexCount) 1
      (encoded_facet_types currentData)
      (encoded_destinations currentData)
      (encoded_permutations currentData))
... | nothing = nothing
... | just completedState with unused_facet_types completedState |
  unused_second_destinations completedState |
  unused_second_permutations completedState
... | [] | [] | [] with flush_zero_padding (after_component_bits currentData)
... | nothing = nothing
... | just alignedCursor = read_component_locks
  (second_triangulation completedState) alignedCursor
construct_component simplexCount currentData | just completedState | _ | _ | _ =
  nothing

read_second_generation_component : (simplexCount : Nat) → BitCursor →
  Maybe (BitParsed (Classical.DecodedTriangulation 3))
read_second_generation_component simplexCount currentCursor
  with decode_component_bits simplexCount currentCursor
... | nothing = nothing
... | just currentData = construct_component simplexCount currentData

read_component_sequence : Nat → Nat → BitCursor →
  Maybe (List (Classical.DecodedTriangulation 3))
read_component_sequence zero simplexCount currentCursor = nothing
read_component_sequence (suc remainingFuel) simplexCount currentCursor
  with read_second_generation_component simplexCount currentCursor
... | nothing = nothing
... | just componentResult with remaining_bits componentResult
... | bit_cursor [] zero = just (bit_value componentResult ∷ [])
... | bit_cursor [] (suc currentOffset) = nothing
... | bit_cursor (_ ∷ _) (suc currentOffset) = nothing
... | bit_cursor currentCharacters@(headCharacter ∷ remainingCharacters) zero
  with decode_size currentCharacters
... | nothing = nothing
... | just sizeResult with component_simplex_count (parsed_value sizeResult)
... | zero = nothing
... | suc remainingSize with read_component_sequence remainingFuel
  (suc remainingSize)
  (bit_cursor (remaining_characters sizeResult) zero)
... | nothing = nothing
... | just remainingComponents = just
  (bit_value componentResult ∷ remainingComponents)

read_second_generation_signature3 : String →
  Maybe (Classical.DecodedTriangulation 3)
read_second_generation_signature3 signatureText
  with trim_whitespace (primStringToList signatureText)
... | currentCharacters with decode_size currentCharacters
... | nothing = nothing
... | just sizeResult with component_simplex_count (parsed_value sizeResult)
... | zero with remaining_characters sizeResult
... | [] = just (Classical.decoded_triangulation zero
  (unpaired_simplices 3 zero))
... | _ ∷ _ = nothing
read_second_generation_signature3 signatureText | currentCharacters |
  just sizeResult | suc remainingSize
  with read_component_sequence (length currentCharacters) (suc remainingSize)
    (bit_cursor (remaining_characters sizeResult) zero)
... | nothing = nothing
... | just components = Classical.join_components 3 components
