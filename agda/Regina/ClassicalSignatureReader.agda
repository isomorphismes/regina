{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-13. License: ../../LICENSE.txt.
-- Classical TriangulationBase<dim>::fromSig() and fillComponentFromSig1(),
-- detail/isosig-impl.h, 871-1006,1103-1176. Second-generation input is rejected.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.ClassicalSignatureReader where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton using (count_matching; less_than; filter_list)
open import Regina.SignatureEncoding
open import Regina.SignatureDecoding
open import Regina.DisjointUnion
open import Agda.Builtin.Char using (Char; primCharToNat)
open import Agda.Builtin.String using (String; primStringToList)
open import Agda.Builtin.Nat using (_-_)
import Regina.IsomorphismSignature as Signatures
import Regina.SubfaceIncidence3 as Lists

private
  variable
    simplexDimension simplexCount : Nat

record DecodeState (simplexDimension simplexCount : Nat) : Set where
  constructor decode_state
  field
    decode_triangulation : Triangulation simplexDimension simplexCount
    next_unseen_simplex : Nat
    unused_actions : List Nat
    unused_destinations : List Nat
    unused_permutations : List Nat
open DecodeState public

decoded_permutation : (vertexCount rankNumber : Nat) → Maybe (Permutation vertexCount)
decoded_permutation vertexCount rankNumber with Lists.lookupList rankNumber
  (Signatures.permutation_tables vertexCount (map fin_to_nat (all_fin vertexCount)))
... | nothing = nothing
... | just imageNumbers = from_image_list vertexCount imageNumbers

apply_action : Facet simplexDimension simplexCount → DecodeState simplexDimension simplexCount →
  Maybe (DecodeState simplexDimension simplexCount)
apply_action currentFacet currentState with unused_actions currentState
... | [] = nothing
... | zero ∷ remainingActions = just (decode_state (decode_triangulation currentState)
    (next_unseen_simplex currentState) remainingActions
    (unused_destinations currentState) (unused_permutations currentState))
... | 1 ∷ remainingActions with fin_from_nat _ (next_unseen_simplex currentState)
... | nothing = nothing
... | just targetSimplex with join (decode_triangulation currentState) currentFacet targetSimplex identity
... | rejected _ = nothing
... | accepted transitionValue = just (decode_state (resulting_triangulation transitionValue)
    (suc (next_unseen_simplex currentState)) remainingActions
    (unused_destinations currentState) (unused_permutations currentState))
apply_action {simplexDimension = simplexDimension} currentFacet currentState | 2 ∷ remainingActions
  with unused_destinations currentState | unused_permutations currentState
... | [] | _ = nothing
... | _ ∷ _ | [] = nothing
... | destinationNumber ∷ remainingDestinations | permutationNumber ∷ remainingPermutations
  with less_than destinationNumber (next_unseen_simplex currentState)
... | false = nothing
... | true with fin_from_nat _ destinationNumber | decoded_permutation (suc simplexDimension) permutationNumber
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just targetSimplex | just vertexMapping with join (decode_triangulation currentState)
    currentFacet targetSimplex vertexMapping
... | rejected _ = nothing
... | accepted transitionValue = just (decode_state (resulting_triangulation transitionValue)
    (next_unseen_simplex currentState) remainingActions remainingDestinations remainingPermutations)
apply_action currentFacet currentState | suc (suc (suc _)) ∷ _ = nothing

apply_facets : List (Facet simplexDimension simplexCount) → DecodeState simplexDimension simplexCount →
  Maybe (DecodeState simplexDimension simplexCount)
apply_facets [] currentState = just currentState
apply_facets (currentFacet ∷ remainingFacets) currentState
  with is_paired (raw_state (decode_triangulation currentState)) currentFacet
... | true = apply_facets remainingFacets currentState
... | false with apply_action currentFacet currentState
... | nothing = nothing
... | just nextState = apply_facets remainingFacets nextState

bit_is_set : Nat → Nat → Bool
bit_is_set maskNumber bitNumber = nat_equal
  (small_remainder (small_quotient maskNumber (power_of_two bitNumber)) 2) 1

mask_at : List Nat → Nat → Nat
mask_at masks simplexNumber with Lists.lookupList simplexNumber masks
... | nothing = zero
... | just maskNumber = maskNumber

apply_masks : Triangulation simplexDimension simplexCount → List Nat →
  Maybe (Triangulation simplexDimension simplexCount)
apply_masks {simplexDimension = simplexDimension} {simplexCount = simplexCount} currentTriangulation masks
  with nat_equal (length masks) simplexCount and
    all (λ maskNumber → less_than maskNumber (power_of_two (suc (suc simplexDimension)))) masks
... | false = nothing
... | true with certify (raw_triangulation (adjacency (raw_state currentTriangulation))
    (λ currentFacet → bit_is_set (mask_at masks (fin_to_nat (simplex_number currentFacet)))
      (fin_to_nat (opposite_vertex currentFacet)))
    (λ simplexIndex → bit_is_set (mask_at masks (fin_to_nat simplexIndex)) (suc simplexDimension)))
... | rejected _ = nothing
... | accepted checkedTriangulation = just checkedTriangulation

read_locks : Triangulation simplexDimension simplexCount → List Char →
  Maybe (Parsed (Triangulation simplexDimension simplexCount))
read_locks currentTriangulation [] = just (parsed currentTriangulation [])
read_locks {simplexDimension = simplexDimension} {simplexCount = simplexCount}
  currentTriangulation (headCharacter ∷ remainingCharacters)
  with nat_equal (primCharToNat headCharacter) 46
... | false = just (parsed currentTriangulation (headCharacter ∷ remainingCharacters))
... | true with decode_numbers simplexCount (integer_width (power_of_two (suc (suc simplexDimension)) - 1))
    remainingCharacters
... | nothing = nothing
... | just masksResult with apply_masks currentTriangulation (parsed_value masksResult)
... | nothing = nothing
... | just checkedTriangulation = just (parsed checkedTriangulation (remaining_characters masksResult))

record DecodedTriangulation (simplexDimension : Nat) : Set where
  constructor decoded_triangulation
  field
    decoded_simplex_count : Nat
    decoded_tri : Triangulation simplexDimension decoded_simplex_count
open DecodedTriangulation public

read_component_body : (simplexDimension componentSize integerWidth : Nat) → List Char →
  Maybe (Parsed (DecodedTriangulation simplexDimension))
read_component_body simplexDimension componentSize integerWidth currentCharacters
  with decode_actions (length currentCharacters) (componentSize * suc simplexDimension) currentCharacters
... | nothing = nothing
... | just actionsResult with decode_numbers
    (count_matching (λ actionNumber → nat_equal actionNumber 2) (parsed_value actionsResult))
    integerWidth (remaining_characters actionsResult)
... | nothing = nothing
... | just destinationsResult with decode_numbers
    (length (parsed_value destinationsResult)) (integer_width (factorial (suc simplexDimension) - 1))
    (remaining_characters destinationsResult)
... | nothing = nothing
... | just permutationsResult with apply_facets (all_facets simplexDimension componentSize)
    (decode_state (unpaired_simplices simplexDimension componentSize) 1 (parsed_value actionsResult)
      (parsed_value destinationsResult) (parsed_value permutationsResult))
... | nothing = nothing
... | just completedState with unused_actions completedState |
    unused_destinations completedState | unused_permutations completedState
... | [] | [] | [] with read_locks (decode_triangulation completedState)
    (remaining_characters permutationsResult)
... | nothing = nothing
... | just locksResult = just (parsed
    (decoded_triangulation componentSize (parsed_value locksResult)) (remaining_characters locksResult))
read_component_body simplexDimension componentSize integerWidth currentCharacters
  | just actionsResult | just destinationsResult | just permutationsResult | just completedState
  | _ | _ | _ = nothing

read_components : Nat → (simplexDimension : Nat) → List Char →
  Maybe (List (DecodedTriangulation simplexDimension))
read_components remainingFuel simplexDimension [] = just []
read_components zero simplexDimension (_ ∷ _) = nothing
read_components (suc remainingFuel) simplexDimension currentCharacters with decode_size currentCharacters
... | nothing = nothing
... | just sizeResult with component_simplex_count (parsed_value sizeResult)
... | zero = nothing
... | suc remainingSize with read_component_body simplexDimension (suc remainingSize)
    (component_integer_width (parsed_value sizeResult)) (remaining_characters sizeResult)
... | nothing = nothing
... | just componentResult with read_components remainingFuel simplexDimension (remaining_characters componentResult)
... | nothing = nothing
... | just remainingComponents = just (parsed_value componentResult ∷ remainingComponents)

join_components : (simplexDimension : Nat) → List (DecodedTriangulation simplexDimension) →
  Maybe (DecodedTriangulation simplexDimension)
join_components simplexDimension [] = just (decoded_triangulation zero (unpaired_simplices simplexDimension zero))
join_components simplexDimension (headComponent ∷ remainingComponents) with join_components simplexDimension remainingComponents
... | nothing = nothing
... | just tailResult with disjoint_union (decoded_tri headComponent) (decoded_tri tailResult)
... | rejected _ = nothing
... | accepted checkedTriangulation = just (decoded_triangulation
    (decoded_simplex_count headComponent + decoded_simplex_count tailResult) checkedTriangulation)

read_classical_signature : (simplexDimension : Nat) → String → Maybe (DecodedTriangulation simplexDimension)
read_classical_signature simplexDimension signatureText
  with trim_whitespace (primStringToList signatureText)
... | currentCharacters with decode_size currentCharacters
... | nothing = nothing
... | just sizeResult with component_simplex_count (parsed_value sizeResult)
... | zero with remaining_characters sizeResult
... | [] = just (decoded_triangulation zero (unpaired_simplices simplexDimension zero))
... | _ ∷ _ = nothing
read_classical_signature simplexDimension signatureText | currentCharacters | just sizeResult | suc remainingSize
  with read_components (length currentCharacters) simplexDimension currentCharacters
... | nothing = nothing
... | just components = join_components simplexDimension components
