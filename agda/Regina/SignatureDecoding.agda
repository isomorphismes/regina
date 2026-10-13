{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-13. License: ../../LICENSE.txt.
-- Base64Decoder and first-generation facet-action parsing, sigutils.h and
-- detail/isosig-impl.h at e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.SignatureDecoding where

open import Regina.Foundation
open import Regina.SignatureEncoding
open import Regina.Skeleton using (less_than; count_matching)
open import Agda.Builtin.Char using (Char; primCharToNat)
open import Agda.Builtin.Nat using (_-_)
import Regina.Integer as Integer

record Parsed (element : Set) : Set where
  constructor parsed
  field
    parsed_value : element
    remaining_characters : List Char
open Parsed public

decode_character : Char → Maybe Nat
decode_character currentCharacter
  with not (less_than characterNumber 97) and less_than characterNumber 123
  where
  characterNumber = primCharToNat currentCharacter
... | true = just (primCharToNat currentCharacter - 97)
... | false with not (less_than characterNumber 65) and less_than characterNumber 91
  where
  characterNumber = primCharToNat currentCharacter
... | true = just (26 + (primCharToNat currentCharacter - 65))
... | false with not (less_than characterNumber 48) and less_than characterNumber 58
  where
  characterNumber = primCharToNat currentCharacter
... | true = just (52 + (primCharToNat currentCharacter - 48))
... | false with nat_equal (primCharToNat currentCharacter) 43
... | true = just 62
... | false with nat_equal (primCharToNat currentCharacter) 45
... | true = just 63
... | false = nothing

decode_integer : Nat → List Char → Maybe (Parsed Nat)
decode_integer zero currentCharacters = just (parsed zero currentCharacters)
decode_integer (suc remainingWidth) [] = nothing
decode_integer (suc remainingWidth) (headCharacter ∷ remainingCharacters)
  with decode_character headCharacter | decode_integer remainingWidth remainingCharacters
... | just firstNumber | just remainingResult = just (parsed
    (firstNumber + 64 * parsed_value remainingResult) (remaining_characters remainingResult))
... | _ | _ = nothing

decode_numbers : Nat → Nat → List Char → Maybe (Parsed (List Nat))
decode_numbers zero characterWidth currentCharacters = just (parsed [] currentCharacters)
decode_numbers (suc remainingNumbers) characterWidth currentCharacters
  with decode_integer characterWidth currentCharacters
... | nothing = nothing
... | just firstResult with decode_numbers remainingNumbers characterWidth
    (remaining_characters firstResult)
... | nothing = nothing
... | just remainingResult = just (parsed
    (parsed_value firstResult ∷ parsed_value remainingResult) (remaining_characters remainingResult))

record ComponentSize : Set where
  constructor component_size
  field
    component_simplex_count : Nat
    component_integer_width : Nat
open ComponentSize public

decode_size : List Char → Maybe (Parsed ComponentSize)
decode_size currentCharacters with decode_integer 1 currentCharacters
... | nothing = nothing
... | just firstResult with nat_equal (parsed_value firstResult) 63
... | false = just (parsed (component_size (parsed_value firstResult) 1)
    (remaining_characters firstResult))
... | true with decode_integer 1 (remaining_characters firstResult)
... | nothing = nothing
... | just widthResult with decode_integer (parsed_value widthResult) (remaining_characters widthResult)
... | nothing = nothing
... | just sizeResult = just (parsed (component_size (parsed_value sizeResult) (parsed_value widthResult))
    (remaining_characters sizeResult))

small_quotient : Nat → Nat → Nat
small_quotient dividendNumber divisorNumber with Integer.natural_division dividendNumber divisorNumber
... | Integer.division (Integer.pos quotientNumber) _ = quotientNumber
... | _ = zero

small_remainder : Nat → Nat → Nat
small_remainder dividendNumber divisorNumber with Integer.natural_division dividendNumber divisorNumber
... | Integer.division _ (Integer.pos remainderNumber) = remainderNumber
... | _ = zero

unpack_trits : Nat → List Nat
unpack_trits characterNumber = small_remainder characterNumber 4 ∷
  small_remainder (small_quotient characterNumber 4) 4 ∷ small_quotient characterNumber 16 ∷ []

record ActionChunk : Set where
  constructor action_chunk
  field
    unrepresented_facets : Nat
    decoded_actions : List Nat
open ActionChunk public

consume_trits : Nat → List Nat → Maybe ActionChunk
consume_trits remainingFacets [] = just (action_chunk remainingFacets [])
consume_trits zero (zero ∷ remainingTrits) = consume_trits zero remainingTrits
consume_trits zero (suc _ ∷ _) = nothing
consume_trits (suc remainingFacets) (headTrit ∷ remainingTrits)
  with less_than headTrit 3
... | false = nothing
... | true with measure headTrit
  where
  measure : Nat → Nat
  measure zero = 1
  measure (suc _) = 2
... | facetMeasure with less_than (suc remainingFacets) facetMeasure
... | true = nothing
... | false with consume_trits (suc remainingFacets - facetMeasure) remainingTrits
... | nothing = nothing
... | just tailResult = just (action_chunk (unrepresented_facets tailResult)
    (headTrit ∷ decoded_actions tailResult))

decode_actions : Nat → Nat → List Char → Maybe (Parsed (List Nat))
decode_actions characterFuel zero currentCharacters = just (parsed [] currentCharacters)
decode_actions zero (suc _) currentCharacters = nothing
decode_actions (suc remainingFuel) (suc remainingFacets) [] = nothing
decode_actions (suc remainingFuel) (suc remainingFacets) (headCharacter ∷ remainingCharacters)
  with decode_character headCharacter
... | nothing = nothing
... | just characterNumber with consume_trits (suc remainingFacets) (unpack_trits characterNumber)
... | nothing = nothing
... | just chunkResult with decode_actions remainingFuel (unrepresented_facets chunkResult)
    remainingCharacters
... | nothing = nothing
... | just tailResult = just (parsed (decoded_actions chunkResult ++ parsed_value tailResult)
    (remaining_characters tailResult))

is_whitespace : Char → Bool
is_whitespace currentCharacter = any (nat_equal (primCharToNat currentCharacter))
  (9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 32 ∷ [])

trim_front : List Char → List Char
trim_front [] = []
trim_front (headCharacter ∷ remainingCharacters) with is_whitespace headCharacter
... | true = trim_front remainingCharacters
... | false = headCharacter ∷ remainingCharacters

reverse_characters : List Char → List Char
reverse_characters [] = []
reverse_characters (headCharacter ∷ remainingCharacters) =
  reverse_characters remainingCharacters ++ (headCharacter ∷ [])

trim_whitespace : List Char → List Char
trim_whitespace currentCharacters = trim_front
  (reverse_characters (trim_front (reverse_characters currentCharacters)))
