{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-13. License: ../../LICENSE.txt.
-- The component-appending semantics used by TriangulationBase::fromSig().
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.DisjointUnion where

open import Regina.Foundation
open import Regina.Triangulation

data SumIndex (firstCount secondCount : Nat) : Set where
  first_index : Fin firstCount → SumIndex firstCount secondCount
  second_index : Fin secondCount → SumIndex firstCount secondCount

split_index : (firstCount secondCount : Nat) → Fin (firstCount + secondCount) →
  SumIndex firstCount secondCount
split_index zero secondCount currentIndex = second_index currentIndex
split_index (suc firstCount) secondCount fzero = first_index fzero
split_index (suc firstCount) secondCount (fsuc currentIndex)
  with split_index firstCount secondCount currentIndex
... | first_index originalIndex = first_index (fsuc originalIndex)
... | second_index originalIndex = second_index originalIndex

include_first : {firstCount secondCount : Nat} → Fin firstCount → Fin (firstCount + secondCount)
include_first {suc _} fzero = fzero
include_first {suc _} (fsuc currentIndex) = fsuc (include_first currentIndex)

include_second : (firstCount : Nat) → {secondCount : Nat} → Fin secondCount →
  Fin (firstCount + secondCount)
include_second zero currentIndex = currentIndex
include_second (suc firstCount) currentIndex = fsuc (include_second firstCount currentIndex)

union_adjacency : {dimension firstCount secondCount : Nat} →
  Triangulation dimension firstCount → Triangulation dimension secondCount →
  Facet dimension (firstCount + secondCount) → Maybe (Gluing dimension (firstCount + secondCount))
union_adjacency {firstCount = firstCount} {secondCount = secondCount}
  firstTriangulation secondTriangulation currentFacet
  with split_index firstCount secondCount (simplex_number currentFacet)
... | first_index originalIndex with adjacency (raw_state firstTriangulation)
    (facet originalIndex (opposite_vertex currentFacet))
... | nothing = nothing
... | just outward = just (gluing (include_first (adjacent_simplex outward)) (vertex_permutation outward))
union_adjacency {firstCount = firstCount} {secondCount = secondCount}
  firstTriangulation secondTriangulation currentFacet | second_index originalIndex
  with adjacency (raw_state secondTriangulation) (facet originalIndex (opposite_vertex currentFacet))
... | nothing = nothing
... | just outward = just (gluing (include_second firstCount (adjacent_simplex outward)) (vertex_permutation outward))

union_facet_lock : {dimension firstCount secondCount : Nat} →
  Triangulation dimension firstCount → Triangulation dimension secondCount →
  Facet dimension (firstCount + secondCount) → Bool
union_facet_lock {firstCount = firstCount} {secondCount = secondCount}
  firstTriangulation secondTriangulation currentFacet
  with split_index firstCount secondCount (simplex_number currentFacet)
... | first_index originalIndex = facet_is_locked (raw_state firstTriangulation)
    (facet originalIndex (opposite_vertex currentFacet))
... | second_index originalIndex = facet_is_locked (raw_state secondTriangulation)
    (facet originalIndex (opposite_vertex currentFacet))

union_simplex_lock : {dimension firstCount secondCount : Nat} →
  Triangulation dimension firstCount → Triangulation dimension secondCount →
  Fin (firstCount + secondCount) → Bool
union_simplex_lock {firstCount = firstCount} {secondCount = secondCount}
  firstTriangulation secondTriangulation currentIndex with split_index firstCount secondCount currentIndex
... | first_index originalIndex = simplex_is_locked (raw_state firstTriangulation) originalIndex
... | second_index originalIndex = simplex_is_locked (raw_state secondTriangulation) originalIndex

disjoint_union : {dimension firstCount secondCount : Nat} →
  Triangulation dimension firstCount → Triangulation dimension secondCount →
  Outcome (Triangulation dimension (firstCount + secondCount))
disjoint_union firstTriangulation secondTriangulation = certify (raw_triangulation
  (union_adjacency firstTriangulation secondTriangulation)
  (union_facet_lock firstTriangulation secondTriangulation)
  (union_simplex_lock firstTriangulation secondTriangulation))
