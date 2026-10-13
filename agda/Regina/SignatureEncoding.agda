{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-13. License: ../../LICENSE.txt.
-- Classical signature encodings from engine/utilities/sigutils.h and
-- engine/triangulation/detail/isosig-impl.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.SignatureEncoding where

open import Regina.Foundation
open import Agda.Builtin.Nat using (_-_)
open import Agda.Builtin.Char using (Char; primNatToChar; primCharToNat)
open import Agda.Builtin.String using (String; primStringFromList; primStringToList)
open import Regina.Skeleton using (less_than; count_matching; concat_map)
import Regina.Integer as Integer
import Regina.DualPresentation3 as Sequence

factorial : Nat → Nat
factorial zero = 1
factorial (suc remainingNumber) = suc remainingNumber * factorial remainingNumber

permutation_rank : List Nat → Nat
permutation_rank [] = zero
permutation_rank (headNumber ∷ tailNumbers) =
  count_matching (λ candidateNumber → less_than candidateNumber headNumber) tailNumbers *
    factorial (length tailNumbers) + permutation_rank tailNumbers

base64_character : Nat → Maybe Char
base64_character characterNumber with less_than characterNumber 26
... | true = just (primNatToChar (97 + characterNumber))
... | false with less_than characterNumber 52
... | true = just (primNatToChar (65 + (characterNumber - 26)))
... | false with less_than characterNumber 62
... | true = just (primNatToChar (48 + (characterNumber - 52)))
... | false with nat_equal characterNumber 62
... | true = just '+'
... | false with nat_equal characterNumber 63
... | true = just '-'
... | false = nothing

width_steps : Nat → Nat → Nat
width_steps zero currentNumber = 1
width_steps (suc remainingSteps) currentNumber with less_than currentNumber 64
... | true = 1
... | false with Integer.natural_division currentNumber 64
... | Integer.division (Integer.pos quotientNumber) _ =
    suc (width_steps remainingSteps quotientNumber)
... | _ = 1

integer_width : Nat → Nat
integer_width currentNumber = width_steps currentNumber currentNumber

encode_integer : Nat → Nat → Maybe (List Char)
encode_integer zero zero = just []
encode_integer zero (suc _) = nothing
encode_integer (suc remainingWidth) currentNumber
  with Integer.natural_division currentNumber 64
... | Integer.division (Integer.pos quotientNumber) (Integer.pos remainderNumber)
  with base64_character remainderNumber | encode_integer remainingWidth quotientNumber
... | just headCharacter | just remainingCharacters = just (headCharacter ∷ remainingCharacters)
... | _ | _ = nothing
encode_integer (suc remainingWidth) currentNumber | _ = nothing

encode_integers : Nat → List Nat → Maybe (List Char)
encode_integers characterWidth currentNumbers
  with Sequence.sequence (map (encode_integer characterWidth) currentNumbers)
... | nothing = nothing
... | just groups = just (concat_map (λ characterGroup → characterGroup) groups)

encode_size : Nat → Maybe (List Char)
encode_size componentSize with less_than componentSize 63
... | true with base64_character componentSize
... | nothing = nothing
... | just sizeCharacter = just (sizeCharacter ∷ [])
encode_size componentSize | false with base64_character (integer_width componentSize) |
  encode_integer (integer_width componentSize) componentSize
... | just widthCharacter | just sizeCharacters = just ('-' ∷ widthCharacter ∷ sizeCharacters)
... | _ | _ = nothing

encode_trits : List Nat → Maybe (List Char)
encode_trits [] = just []
encode_trits (firstTrit ∷ []) with less_than firstTrit 3 | base64_character firstTrit
... | true | just firstCharacter = just (firstCharacter ∷ [])
... | _ | _ = nothing
encode_trits (firstTrit ∷ secondTrit ∷ []) with less_than firstTrit 3 and less_than secondTrit 3 |
  base64_character (firstTrit + 4 * secondTrit)
... | true | just firstCharacter = just (firstCharacter ∷ [])
... | _ | _ = nothing
encode_trits (firstTrit ∷ secondTrit ∷ thirdTrit ∷ remainingTrits)
  with less_than firstTrit 3 and less_than secondTrit 3 and less_than thirdTrit 3 |
    base64_character (firstTrit + 4 * secondTrit + 16 * thirdTrit) | encode_trits remainingTrits
... | true | just firstCharacter | just remainingCharacters = just (firstCharacter ∷ remainingCharacters)
... | _ | _ | _ = nothing

characters_less : List Char → List Char → Bool
characters_less [] [] = false
characters_less [] (_ ∷ _) = true
characters_less (_ ∷ _) [] = false
characters_less (firstCharacter ∷ firstTail) (secondCharacter ∷ secondTail)
  with nat_equal (primCharToNat firstCharacter) (primCharToNat secondCharacter)
... | true = characters_less firstTail secondTail
... | false = less_than (primCharToNat firstCharacter) (primCharToNat secondCharacter)

insert_signature : List Char → List (List Char) → List (List Char)
insert_signature newSignature [] = newSignature ∷ []
insert_signature newSignature (headSignature ∷ remainingSignatures)
  with characters_less newSignature headSignature
... | true = newSignature ∷ headSignature ∷ remainingSignatures
... | false = headSignature ∷ insert_signature newSignature remainingSignatures

sort_signatures : List (List Char) → List (List Char)
sort_signatures [] = []
sort_signatures (headSignature ∷ remainingSignatures) =
  insert_signature headSignature (sort_signatures remainingSignatures)

smallest_signature : List (List Char) → Maybe (List Char)
smallest_signature [] = nothing
smallest_signature (headSignature ∷ remainingSignatures) = just
  (fold_right choose headSignature remainingSignatures)
  where
  choose : List Char → List Char → List Char
  choose firstSignature secondSignature with characters_less firstSignature secondSignature
  ... | true = firstSignature
  ... | false = secondSignature

power_of_two : Nat → Nat
power_of_two zero = 1
power_of_two (suc remainingBits) = 2 * power_of_two remainingBits
