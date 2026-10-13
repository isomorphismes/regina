{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- Exact integer operations used by Regina's Matrix<Integer> and AbelianGroup.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.Integer where

open import Regina.Foundation
open import Agda.Builtin.Int public using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (_-_)

integer_equal : Int → Int → Bool
integer_equal (pos first) (pos second) = nat_equal first second
integer_equal (negsuc first) (negsuc second) = nat_equal first second
integer_equal _ _ = false

private
  successor_injective : {first second : Nat} → suc first ≡ suc second → first ≡ second
  successor_injective refl = refl

  natural_dec_equal : (first second : Nat) → Dec (first ≡ second)
  natural_dec_equal zero zero = yes refl
  natural_dec_equal zero (suc _) = no (λ ())
  natural_dec_equal (suc _) zero = no (λ ())
  natural_dec_equal (suc first) (suc second) with natural_dec_equal first second
  ... | yes proof = yes (cong suc proof)
  ... | no refute = no (λ proof → refute (successor_injective proof))

  positive_injective : {first second : Nat} → pos first ≡ pos second → first ≡ second
  positive_injective refl = refl

  negative_injective : {first second : Nat} → negsuc first ≡ negsuc second → first ≡ second
  negative_injective refl = refl

integer_dec_equal : (first second : Int) → Dec (first ≡ second)
integer_dec_equal (pos first) (pos second) with natural_dec_equal first second
... | yes proof = yes (cong pos proof)
... | no refute = no (λ proof → refute (positive_injective proof))
integer_dec_equal (negsuc first) (negsuc second) with natural_dec_equal first second
... | yes proof = yes (cong negsuc proof)
... | no refute = no (λ proof → refute (negative_injective proof))
integer_dec_equal (pos _) (negsuc _) = no (λ ())
integer_dec_equal (negsuc _) (pos _) = no (λ ())

negative : Nat → Int
negative zero = pos zero
negative (suc magnitude) = negsuc magnitude

negate : Int → Int
negate (pos magnitude) = negative magnitude
negate (negsuc magnitude) = pos (suc magnitude)

absolute : Int → Nat
absolute (pos magnitude) = magnitude
absolute (negsuc magnitude) = suc magnitude

natural_difference : Nat → Nat → Int
natural_difference zero zero = pos zero
natural_difference zero (suc second) = negsuc second
natural_difference (suc first) zero = pos (suc first)
natural_difference (suc first) (suc second) = natural_difference first second

add : Int → Int → Int
add (pos first) (pos second) = pos (first + second)
add (pos first) (negsuc second) = natural_difference first (suc second)
add (negsuc first) (pos second) = natural_difference second (suc first)
add (negsuc first) (negsuc second) = negsuc (suc (first + second))

subtract : Int → Int → Int
subtract first second = add first (negate second)

multiply : Int → Int → Int
multiply (pos first) (pos second) = pos (first * second)
multiply (pos first) (negsuc second) = negative (first * suc second)
multiply (negsuc first) (pos second) = negative (suc first * second)
multiply (negsuc first) (negsuc second) = pos (suc first * suc second)

sum : List Int → Int
sum = fold_right add (pos zero)

natural_less : Nat → Nat → Bool
natural_less zero zero = false
natural_less zero (suc second) = true
natural_less (suc first) zero = false
natural_less (suc first) (suc second) = natural_less first second

record Division : Set where
  constructor division
  field
    quotient remainder : Int
open Division public

-- Structural long division: after reading one more unit of dividend,
-- advance the remainder or carry one unit into the quotient.
natural_division : Nat → Nat → Division
natural_division zero divisor = division (pos zero) (pos zero)
natural_division (suc dividend) divisor
  with natural_division dividend divisor
... | division (pos quotientValue) (pos remainderValue)
  with nat_equal (suc remainderValue) divisor
... | true = division (pos (suc quotientValue)) (pos zero)
... | false = division (pos quotientValue) (pos (suc remainderValue))
natural_division (suc dividend) divisor | _ = division (pos zero) (pos zero)

-- Quotient truncates toward zero, matching Integer::operator/().
-- The public operation rejects zero divisors explicitly.
divide : Int → Int → Maybe Division
divide dividend (pos zero) = nothing
divide (pos dividend) (pos (suc divisor)) =
  just (natural_division dividend (suc divisor))
divide (pos dividend) (negsuc divisor)
  with natural_division dividend (suc divisor)
... | division quotientValue remainderValue =
  just (division (negate quotientValue) remainderValue)
divide (negsuc dividend) (pos (suc divisor))
  with natural_division (suc dividend) (suc divisor)
... | division quotientValue remainderValue =
  just (division (negate quotientValue) (negate remainderValue))
divide (negsuc dividend) (negsuc divisor)
  with natural_division (suc dividend) (suc divisor)
... | division quotientValue remainderValue =
  just (division quotientValue (negate remainderValue))

divides : Int → Int → Bool
divides divisor dividend with divide dividend divisor
... | nothing = integer_equal dividend (pos zero)
... | just result = integer_equal (remainder result) (pos zero)

-- Integer::divisionAlg() uses the unique nonnegative remainder. Its
-- documented zero-divisor case returns (0, dividend).
divisionAlgorithm : Int → Int → Division
divisionAlgorithm dividend divisor with divide dividend divisor
... | nothing = division (pos zero) dividend
... | just (division quotientValue (pos remainderValue)) =
  division quotientValue (pos remainderValue)
... | just (division quotientValue (negsuc remainderValue))
  with divisor
... | pos magnitude = division (subtract quotientValue (pos 1))
  (natural_difference magnitude (suc remainderValue))
... | negsuc magnitude = division (add quotientValue (pos 1))
  (natural_difference (suc magnitude) (suc remainderValue))
