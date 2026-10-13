{-# OPTIONS --safe --without-K #-}
module Regina.SmithNormalFormTests where

open import Regina.Foundation
open import Regina.IntegerMatrix
open import Regina.SmithNormalForm
open import Regina.Integer using (Int; pos; negsuc)
import Regina.Integer as Integer

private
  matrix2 : Int → Int → Int → Int → Matrix 2 2
  matrix2 first second third fourth = matrix
    (vector_cons (vector_cons first (vector_cons second empty_vector))
      (vector_cons (vector_cons third (vector_cons fourth empty_vector)) empty_vector))

  diagonal : {rows columns : Nat} → Nat → Matrix rows columns → Maybe (List Nat)
  diagonal fuel original with smithNormalForm fuel original
  ... | nothing = nothing
  ... | just smithResult = just (smithDiagonal (reduced_matrix (smith_state smithResult)))

negative_division_truncates_toward_zero :
  Integer.divide (negsuc 6) (pos 3) ≡
    just (Integer.division (negsuc 1) (negsuc 0))
negative_division_truncates_toward_zero = refl

euclidean_division_has_nonnegative_remainder :
  Integer.divisionAlgorithm (negsuc 6) (pos 3) ≡
    Integer.division (negsuc 2) (pos 2)
euclidean_division_has_nonnegative_remainder = refl

negative_divisor_euclidean_division :
  Integer.divisionAlgorithm (negsuc 6) (negsuc 2) ≡
    Integer.division (pos 3) (pos 2)
negative_divisor_euclidean_division = refl

zero_divisor_special_case :
  Integer.divisionAlgorithm (negsuc 6) (pos zero) ≡
    Integer.division (pos zero) (negsuc 6)
zero_divisor_special_case = refl

zero_matrix_has_no_nonzero_invariant_factors :
  diagonal 1 (zeroMatrix 2 3) ≡ just []
zero_matrix_has_no_nonzero_invariant_factors = refl

identity_has_unit_invariant_factors :
  diagonal 4 (identityMatrix 2) ≡ just (1 ∷ 1 ∷ [])
identity_has_unit_invariant_factors = refl

coprime_diagonal_is_repaired :
  diagonal 30 (matrix2 (pos 2) (pos 0) (pos 0) (pos 3)) ≡ just (1 ∷ 6 ∷ [])
coprime_diagonal_is_repaired = refl

dense_matrix_retains_torsion :
  diagonal 30 (matrix2 (pos 2) (pos 4) (pos 6) (pos 8)) ≡ just (2 ∷ 4 ∷ [])
dense_matrix_retains_torsion = refl

negative_entries_and_unit_pivot :
  diagonal 30 (matrix2 (negsuc 3) (pos 6) (pos 3) (negsuc 8)) ≡ just (1 ∷ 18 ∷ [])
negative_entries_and_unit_pivot = refl

rank_deficient_matrix :
  diagonal 30 (matrix2 (pos 2) (pos 4) (pos 4) (pos 8)) ≡ just (2 ∷ [])
rank_deficient_matrix = refl

rectangular_presentation :
  diagonal 30 (matrix
    (vector_cons (vector_cons (pos 6)
      (vector_cons (pos 10) (vector_cons (pos 14) empty_vector))) empty_vector)) ≡
    just (2 ∷ [])
rectangular_presentation = refl

empty_rows_are_preserved : diagonal 1 (zeroMatrix 0 3) ≡ just []
empty_rows_are_preserved = refl

empty_columns_are_preserved : diagonal 1 (zeroMatrix 3 0) ≡ just []
empty_columns_are_preserved = refl

exhaustion_is_not_success : diagonal 0 (identityMatrix 2) ≡ nothing
exhaustion_is_not_success = refl

false_basis_certificate_is_rejected :
  stateCertifies (identityMatrix 2)
    (reduction_state (zeroMatrix 2 2)
      (identityMatrix 2) (identityMatrix 2) (identityMatrix 2) (identityMatrix 2)) ≡ false
false_basis_certificate_is_rejected = refl

nondividing_diagonal_is_not_smith_form :
  isSmithForm (matrix2 (pos 2) (pos 0) (pos 0) (pos 3)) ≡ false
nondividing_diagonal_is_not_smith_form = refl

off_diagonal_entry_is_not_smith_form :
  isSmithForm (matrix2 (pos 1) (pos 1) (pos 0) (pos 2)) ≡ false
off_diagonal_entry_is_not_smith_form = refl

negative_diagonal_is_not_smith_form :
  isSmithForm (matrix2 (negsuc 0) (pos 0) (pos 0) (pos 2)) ≡ false
negative_diagonal_is_not_smith_form = refl
