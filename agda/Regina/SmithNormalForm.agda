{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- Smith reduction semantics from engine/maths/matrix.cpp (smithNormalForm
-- and smithNormalFormCoB). Elementary Euclidean row/column operations replace
-- the mutable two-row gcd combinations; every result is checked independently.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.SmithNormalForm where

open import Regina.Foundation
open import Regina.IntegerMatrix
open import Regina.Integer using (Int; pos; negsuc)
import Regina.Integer as Integer
open import Agda.Builtin.Nat using (_-_)

private
  variable
    rows columns : Nat

record ReductionState (rows columns : Nat) : Set where
  constructor reduction_state
  field
    reduced_matrix : Matrix rows columns
    left_basis left_basis_inverse : Matrix rows rows
    right_basis right_basis_inverse : Matrix columns columns
open ReductionState public

initialState : Matrix rows columns → ReductionState rows columns
initialState {rows} {columns} original = reduction_state original
  (identityMatrix rows) (identityMatrix rows)
  (identityMatrix columns) (identityMatrix columns)

swapStateRows : Fin rows → Fin rows → ReductionState rows columns →
  ReductionState rows columns
swapStateRows first second currentState = reduction_state
  (swapRows first second (reduced_matrix currentState))
  (swapRows first second (left_basis currentState))
  (swapColumns first second (left_basis_inverse currentState))
  (right_basis currentState) (right_basis_inverse currentState)

swapStateColumns : Fin columns → Fin columns → ReductionState rows columns →
  ReductionState rows columns
swapStateColumns first second currentState = reduction_state
  (swapColumns first second (reduced_matrix currentState))
  (left_basis currentState) (left_basis_inverse currentState)
  (swapColumns first second (right_basis currentState))
  (swapRows first second (right_basis_inverse currentState))

addStateRow : Fin rows → Fin rows → Int → ReductionState rows columns →
  ReductionState rows columns
addStateRow source target coefficient currentState = reduction_state
  (addRow source target coefficient (reduced_matrix currentState))
  (addRow source target coefficient (left_basis currentState))
  (addColumn target source (Integer.negate coefficient) (left_basis_inverse currentState))
  (right_basis currentState) (right_basis_inverse currentState)

addStateColumn : Fin columns → Fin columns → Int → ReductionState rows columns →
  ReductionState rows columns
addStateColumn source target coefficient currentState = reduction_state
  (addColumn source target coefficient (reduced_matrix currentState))
  (left_basis currentState) (left_basis_inverse currentState)
  (addColumn source target coefficient (right_basis currentState))
  (addRow target source (Integer.negate coefficient) (right_basis_inverse currentState))

negateStateRow : Fin rows → ReductionState rows columns → ReductionState rows columns
negateStateRow currentRow currentState = reduction_state
  (negateRow currentRow (reduced_matrix currentState))
  (negateRow currentRow (left_basis currentState))
  (transpose (negateRow currentRow (transpose (left_basis_inverse currentState))))
  (right_basis currentState) (right_basis_inverse currentState)

record Position (rows columns : Nat) : Set where
  constructor position
  field
    row_number : Fin rows
    column_number : Fin columns
open Position public

positions : (rows columns : Nat) → List (Position rows columns)
positions rows columns = fold_right
  (λ currentRow tail → map (position currentRow) (all_fin columns) ++ tail) [] (all_fin rows)

atOrAfter : Nat → Nat → Bool
atOrAfter stage index = not (Integer.natural_less index stage)

nonzeroPosition : Nat → Matrix rows columns → Position rows columns → Bool
nonzeroPosition stage currentMatrix currentPosition =
  atOrAfter stage (fin_to_nat (row_number currentPosition)) and
  atOrAfter stage (fin_to_nat (column_number currentPosition)) and
  not (Integer.integer_equal
    (entry currentMatrix (row_number currentPosition) (column_number currentPosition))
    (pos zero))

data ReductionStep (rows columns : Nat) : Set where
  reduction_complete : ReductionState rows columns → ReductionStep rows columns
  reduction_continue : Nat → ReductionState rows columns → ReductionStep rows columns

clearColumnEntry : Nat → Fin rows → Fin columns → Fin rows →
  ReductionState rows columns → ReductionStep rows columns
clearColumnEntry stage pivotRow pivotColumn otherRow currentState
  with Integer.divide (entry (reduced_matrix currentState) otherRow pivotColumn)
    (entry (reduced_matrix currentState) pivotRow pivotColumn)
... | nothing = reduction_continue stage currentState
... | just result with Integer.integer_equal (Integer.remainder result) (pos zero)
... | true = reduction_continue stage (addStateRow pivotRow otherRow
    (Integer.negate (Integer.quotient result)) currentState)
... | false = reduction_continue stage (swapStateRows pivotRow otherRow
    (addStateRow pivotRow otherRow (Integer.negate (Integer.quotient result)) currentState))

clearRowEntry : Nat → Fin rows → Fin columns → Fin columns →
  ReductionState rows columns → ReductionStep rows columns
clearRowEntry stage pivotRow pivotColumn otherColumn currentState
  with Integer.divide (entry (reduced_matrix currentState) pivotRow otherColumn)
    (entry (reduced_matrix currentState) pivotRow pivotColumn)
... | nothing = reduction_continue stage currentState
... | just result with Integer.integer_equal (Integer.remainder result) (pos zero)
... | true = reduction_continue stage (addStateColumn pivotColumn otherColumn
    (Integer.negate (Integer.quotient result)) currentState)
... | false = reduction_continue stage (swapStateColumns pivotColumn otherColumn
    (addStateColumn pivotColumn otherColumn (Integer.negate (Integer.quotient result)) currentState))

finishPivot : Nat → Fin rows → Fin columns → ReductionState rows columns →
  ReductionStep rows columns
finishPivot stage pivotRow pivotColumn currentState
  with entry (reduced_matrix currentState) pivotRow pivotColumn
... | pos magnitude = reduction_continue (suc stage) currentState
... | negsuc magnitude = reduction_continue (suc stage) (negateStateRow pivotRow currentState)

checkDivisibility : Nat → Fin rows → Fin columns → ReductionState rows columns →
  ReductionStep rows columns
checkDivisibility {rows} {columns} stage pivotRow pivotColumn currentState
  with find offending (positions rows columns)
  where
  offending : Position rows columns → Bool
  offending candidatePosition =
    Integer.natural_less stage (fin_to_nat (row_number candidatePosition)) and
    Integer.natural_less stage (fin_to_nat (column_number candidatePosition)) and
    not (Integer.divides (entry (reduced_matrix currentState) pivotRow pivotColumn)
      (entry (reduced_matrix currentState) (row_number candidatePosition)
        (column_number candidatePosition)))
... | nothing = finishPivot stage pivotRow pivotColumn currentState
... | just offendingPosition = reduction_continue stage
  (addStateRow (row_number offendingPosition) pivotRow (pos 1) currentState)

clearPivotRow : Nat → Fin rows → Fin columns → ReductionState rows columns →
  ReductionStep rows columns
clearPivotRow {columns = columns} stage pivotRow pivotColumn currentState
  with find nonzeroColumn (all_fin columns)
  where
  nonzeroColumn : Fin columns → Bool
  nonzeroColumn currentColumn = Integer.natural_less stage (fin_to_nat currentColumn) and
    not (Integer.integer_equal (entry (reduced_matrix currentState) pivotRow currentColumn) (pos zero))
... | nothing = checkDivisibility stage pivotRow pivotColumn currentState
... | just otherColumn = clearRowEntry stage pivotRow pivotColumn otherColumn currentState

clearPivotColumn : Nat → Fin rows → Fin columns → ReductionState rows columns →
  ReductionStep rows columns
clearPivotColumn {rows = rows} stage pivotRow pivotColumn currentState
  with find nonzeroRow (all_fin rows)
  where
  nonzeroRow : Fin rows → Bool
  nonzeroRow currentRow = Integer.natural_less stage (fin_to_nat currentRow) and
    not (Integer.integer_equal (entry (reduced_matrix currentState) currentRow pivotColumn) (pos zero))
... | nothing = clearPivotRow stage pivotRow pivotColumn currentState
... | just otherRow = clearColumnEntry stage pivotRow pivotColumn otherRow currentState

choosePivot : Nat → Fin rows → Fin columns → ReductionState rows columns →
  ReductionStep rows columns
choosePivot {rows} {columns} stage pivotRow pivotColumn currentState
  with Integer.integer_equal (entry (reduced_matrix currentState) pivotRow pivotColumn) (pos zero)
... | false = clearPivotColumn stage pivotRow pivotColumn currentState
... | true with find (nonzeroPosition stage (reduced_matrix currentState)) (positions rows columns)
... | nothing = reduction_complete currentState
... | just pivotPosition = reduction_continue stage
  (swapStateColumns pivotColumn (column_number pivotPosition)
    (swapStateRows pivotRow (row_number pivotPosition) currentState))

nextStep : Nat → ReductionState rows columns → ReductionStep rows columns
nextStep {rows} {columns} stage currentState
  with fin_from_nat rows stage | fin_from_nat columns stage
... | nothing | _ = reduction_complete currentState
... | just _ | nothing = reduction_complete currentState
... | just pivotRow | just pivotColumn = choosePivot stage pivotRow pivotColumn currentState

-- Fuel bounds work, never correctness. Exhaustion has a separate failure
-- result; a partial diagonal is never returned as a Smith normal form.
reduce : Nat → Nat → ReductionState rows columns → Maybe (ReductionState rows columns)
reduce zero stage currentState = nothing
reduce (suc fuel) stage currentState with nextStep stage currentState
... | reduction_complete result = just result
... | reduction_continue nextStage result = reduce fuel nextStage result

diagonalEntry : Matrix rows columns → Nat → Int
diagonalEntry {rows} {columns} currentMatrix index
  with fin_from_nat rows index | fin_from_nat columns index
... | just currentRow | just currentColumn = entry currentMatrix currentRow currentColumn
... | nothing | _ = pos zero
... | just _ | nothing = pos zero

minimum : Nat → Nat → Nat
minimum zero second = zero
minimum (suc first) zero = zero
minimum (suc first) (suc second) = suc (minimum first second)

isSmithForm : Matrix rows columns → Bool
isSmithForm {rows} {columns} currentMatrix =
  all validPosition (positions rows columns) and
  all (λ index → Integer.divides (diagonalEntry currentMatrix (fin_to_nat index))
    (diagonalEntry currentMatrix (suc (fin_to_nat index))))
    (all_fin (minimum rows columns))
  where
  validPosition : Position rows columns → Bool
  validPosition currentPosition
    with nat_equal (fin_to_nat (row_number currentPosition))
      (fin_to_nat (column_number currentPosition)) |
      entry currentMatrix (row_number currentPosition) (column_number currentPosition)
  ... | true | pos magnitude = true
  ... | true | negsuc magnitude = false
  ... | false | value = Integer.integer_equal value (pos zero)

stateCertifies : Matrix rows columns → ReductionState rows columns → Bool
stateCertifies {rows} {columns} original currentState =
  isSmithForm (reduced_matrix currentState) and
  matrix_equal (product (product (left_basis currentState) original) (right_basis currentState))
    (reduced_matrix currentState) and
  matrix_equal (product (left_basis currentState) (left_basis_inverse currentState)) (identityMatrix rows) and
  matrix_equal (product (left_basis_inverse currentState) (left_basis currentState)) (identityMatrix rows) and
  matrix_equal (product (right_basis currentState) (right_basis_inverse currentState)) (identityMatrix columns) and
  matrix_equal (product (right_basis_inverse currentState) (right_basis currentState)) (identityMatrix columns)

record SmithCertificate (original : Matrix rows columns) : Set where
  constructor smith_certificate
  field
    smith_state : ReductionState rows columns
    smith_certificate_checked : stateCertifies original smith_state ≡ true
    smith_equivalence : SameEntries
      (product (product (left_basis smith_state) original) (right_basis smith_state))
      (reduced_matrix smith_state)
    smith_left_inverse : SameEntries
      (product (left_basis smith_state) (left_basis_inverse smith_state)) (identityMatrix rows)
    smith_left_reverse_inverse : SameEntries
      (product (left_basis_inverse smith_state) (left_basis smith_state)) (identityMatrix rows)
    smith_right_inverse : SameEntries
      (product (right_basis smith_state) (right_basis_inverse smith_state)) (identityMatrix columns)
    smith_right_reverse_inverse : SameEntries
      (product (right_basis_inverse smith_state) (right_basis smith_state)) (identityMatrix columns)
open SmithCertificate public

certifySmith : (original : Matrix rows columns) → ReductionState rows columns →
  Maybe (SmithCertificate original)
certifySmith {rows} {columns} original currentState
  with bool_dec_equal (stateCertifies original currentState) true
  where
  open import Regina.Triangulation using (bool_dec_equal)
... | no _ = nothing
... | yes checkedProof with
  matrix_dec_equal (product (product (left_basis currentState) original) (right_basis currentState))
    (reduced_matrix currentState) |
  matrix_dec_equal (product (left_basis currentState) (left_basis_inverse currentState))
    (identityMatrix rows) |
  matrix_dec_equal (product (left_basis_inverse currentState) (left_basis currentState))
    (identityMatrix rows) |
  matrix_dec_equal (product (right_basis currentState) (right_basis_inverse currentState))
    (identityMatrix columns) |
  matrix_dec_equal (product (right_basis_inverse currentState) (right_basis currentState))
    (identityMatrix columns)
... | yes equivalentProof | yes leftProof | yes reverseLeftProof | yes rightProof | yes reverseRightProof =
  just (smith_certificate currentState checkedProof equivalentProof leftProof reverseLeftProof
    rightProof reverseRightProof)
... | no _ | _ | _ | _ | _ = nothing
... | yes _ | no _ | _ | _ | _ = nothing
... | yes _ | yes _ | no _ | _ | _ = nothing
... | yes _ | yes _ | yes _ | no _ | _ = nothing
... | yes _ | yes _ | yes _ | yes _ | no _ = nothing

smithNormalForm : Nat → (original : Matrix rows columns) → Maybe (SmithCertificate original)
smithNormalForm fuel original with reduce fuel zero (initialState original)
... | nothing = nothing
... | just currentState = certifySmith original currentState

smithDiagonal : Matrix rows columns → List Nat
smithDiagonal {rows} {columns} currentMatrix = fold_right collect []
  (map (diagonalEntry currentMatrix) (map fin_to_nat (all_fin (minimum rows columns))))
  where
  collect : Int → List Nat → List Nat
  collect (pos zero) tail = tail
  collect (pos (suc magnitude)) tail = suc magnitude ∷ tail
  collect (negsuc magnitude) tail = tail
