{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- Exact, dimension-indexed Matrix<Integer> operations (engine/maths/matrix.h).
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.IntegerMatrix where

open import Regina.Foundation
import Regina.Integer as Integer
open import Regina.Integer using (Int; pos; negsuc)
open import Regina.Skeleton using (tabulate_vector)

record Matrix (rows columns : Nat) : Set where
  constructor matrix
  field
    entries : Vector (Vector Int columns) rows
open Matrix public

entry : {rows columns : Nat} → Matrix rows columns → Fin rows → Fin columns → Int
entry currentMatrix row column = lookup_vector
  (lookup_vector (entries currentMatrix) row) column

tabulate : (rows columns : Nat) → (Fin rows → Fin columns → Int) → Matrix rows columns
tabulate rows columns function = matrix (tabulate_vector rows
  (λ row → tabulate_vector columns (function row)))

zeroMatrix : (rows columns : Nat) → Matrix rows columns
zeroMatrix rows columns = tabulate rows columns (λ _ _ → pos zero)

identityMatrix : (size : Nat) → Matrix size size
identityMatrix size = tabulate size size (λ row column → diagonal row column)
  where
  diagonal : Fin size → Fin size → Int
  diagonal row column with fin_equal row column
  ... | true = pos 1
  ... | false = pos zero

matrix_equal : {rows columns : Nat} → Matrix rows columns → Matrix rows columns → Bool
matrix_equal {rows} {columns} first second = all
  (λ row → all (λ column → Integer.integer_equal
    (entry first row column) (entry second row column)) (all_fin columns))
  (all_fin rows)

SameEntries : {rows columns : Nat} → Matrix rows columns → Matrix rows columns → Set
SameEntries {rows} {columns} first second =
  (currentRow : Fin rows) (currentColumn : Fin columns) →
    entry first currentRow currentColumn ≡ entry second currentRow currentColumn

matrix_dec_equal : {rows columns : Nat} → (first second : Matrix rows columns) →
  Dec (SameEntries first second)
matrix_dec_equal first second = universal_fin_dec
  (λ currentRow → universal_fin_dec
    (λ currentColumn → Integer.integer_dec_equal
      (entry first currentRow currentColumn) (entry second currentRow currentColumn)))

product : {rows inner columns : Nat} → Matrix rows inner → Matrix inner columns →
  Matrix rows columns
product {rows} {inner} {columns} first second = tabulate rows columns
  (λ row column → Integer.sum (map
    (λ middle → Integer.multiply (entry first row middle) (entry second middle column))
    (all_fin inner)))

transpose : {rows columns : Nat} → Matrix rows columns → Matrix columns rows
transpose {rows} {columns} original = tabulate columns rows
  (λ row column → entry original column row)

swapRows : {rows columns : Nat} → Fin rows → Fin rows → Matrix rows columns →
  Matrix rows columns
swapRows {rows} {columns} first second original = tabulate rows columns
  (λ row column → entry original (swap row) column)
  where
  swap : Fin rows → Fin rows
  swap row with fin_equal row first
  ... | true = second
  ... | false with fin_equal row second
  ... | true = first
  ... | false = row

swapColumns : {rows columns : Nat} → Fin columns → Fin columns → Matrix rows columns →
  Matrix rows columns
swapColumns first second original = transpose (swapRows first second (transpose original))

addRow : {rows columns : Nat} → Fin rows → Fin rows → Int → Matrix rows columns →
  Matrix rows columns
addRow {rows} {columns} source target coefficient original = tabulate rows columns combine
  where
  combine : Fin rows → Fin columns → Int
  combine row column with fin_equal row target
  ... | true = Integer.add (entry original row column)
    (Integer.multiply coefficient (entry original source column))
  ... | false = entry original row column

addColumn : {rows columns : Nat} → Fin columns → Fin columns → Int → Matrix rows columns →
  Matrix rows columns
addColumn source target coefficient original =
  transpose (addRow source target coefficient (transpose original))

negateRow : {rows columns : Nat} → Fin rows → Matrix rows columns → Matrix rows columns
negateRow {rows} {columns} target original = tabulate rows columns combine
  where
  combine : Fin rows → Fin columns → Int
  combine row column with fin_equal row target
  ... | true = Integer.negate (entry original row column)
  ... | false = entry original row column

toRows : {rows columns : Nat} → Matrix rows columns → List (List Int)
toRows {rows} {columns} original = map
  (λ row → map (entry original row) (all_fin columns)) (all_fin rows)
