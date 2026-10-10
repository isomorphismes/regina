{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-09. License: ../../LICENSE.txt.

-- Regina's deterministic dual spanning forest.
-- Derived from engine/triangulation/detail/skeleton-impl.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.DualForest where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation

private
  variable
    dimension simplex_count : Nat

appendOne : {element : Set} → List element → element → List element
appendOne existing newElement = existing ++ (newElement ∷ [])

memberIndex : Fin simplex_count → List (Fin simplex_count) → Bool
memberIndex target [] = false
memberIndex target (candidate ∷ remaining) =
  fin_equal target candidate or memberIndex target remaining

record DualForestEdge (dimension simplex_count : Nat) : Set where
  constructor dual_forest_edge
  field
    parent_facet : Facet dimension simplex_count
    child_facet : Facet dimension simplex_count
open DualForestEdge public

record ForestState (dimension simplex_count : Nat) : Set where
  constructor forest_state
  field
    discovered_simplices : List (Fin simplex_count)
    pending_simplices : List (Fin simplex_count)
    forest_edges : List (DualForestEdge dimension simplex_count)
open ForestState public

processForestFacet : Triangulation dimension simplex_count →
  Fin simplex_count → Fin (suc dimension) → ForestState dimension simplex_count →
  ForestState dimension simplex_count
processForestFacet current source localFacet state
  with adjacency (raw_state current) (facet source localFacet)
... | nothing = state
... | just outward
  with memberIndex (adjacent_simplex outward) (discovered_simplices state)
... | true = state
... | false = forest_state
  (appendOne (discovered_simplices state) (adjacent_simplex outward))
  (appendOne (pending_simplices state) (adjacent_simplex outward))
  (appendOne (forest_edges state)
    (dual_forest_edge (facet source localFacet)
      (destination (facet source localFacet) outward)))

processForestFacets : Triangulation dimension simplex_count →
  Fin simplex_count → List (Fin (suc dimension)) →
  ForestState dimension simplex_count → ForestState dimension simplex_count
processForestFacets current source [] state = state
processForestFacets current source (localFacet ∷ remaining) state =
  processForestFacets current source remaining
    (processForestFacet current source localFacet state)

walkForestQueue : (simplexDimension numberOfSimplices : Nat) → Nat →
  Triangulation simplexDimension numberOfSimplices →
  ForestState simplexDimension numberOfSimplices →
  ForestState simplexDimension numberOfSimplices
walkForestQueue simplexDimension numberOfSimplices zero current state = state
walkForestQueue simplexDimension numberOfSimplices (suc fuel) current state
  with pending_simplices state
... | [] = state
... | source ∷ remaining = walkForestQueue simplexDimension numberOfSimplices fuel current
  (processForestFacets current source (all_fin (suc simplexDimension))
    (forest_state (discovered_simplices state) remaining (forest_edges state)))

startForestRoot : (simplexDimension numberOfSimplices : Nat) →
  Triangulation simplexDimension numberOfSimplices → Nat →
  ForestState simplexDimension numberOfSimplices → Fin numberOfSimplices →
  ForestState simplexDimension numberOfSimplices
startForestRoot simplexDimension numberOfSimplices current fuel state root
  with memberIndex root (discovered_simplices state)
... | true = state
... | false = walkForestQueue simplexDimension numberOfSimplices fuel current
  (forest_state
    (appendOne (discovered_simplices state) root)
    (appendOne (pending_simplices state) root)
    (forest_edges state))

processForestRoots : (simplexDimension numberOfSimplices : Nat) →
  Triangulation simplexDimension numberOfSimplices → Nat →
  ForestState simplexDimension numberOfSimplices → List (Fin numberOfSimplices) →
  ForestState simplexDimension numberOfSimplices
processForestRoots simplexDimension numberOfSimplices current fuel state [] = state
processForestRoots simplexDimension numberOfSimplices current fuel state (root ∷ remaining) =
  processForestRoots simplexDimension numberOfSimplices current fuel
    (startForestRoot simplexDimension numberOfSimplices current fuel state root)
    remaining

dualForestState : Triangulation dimension simplex_count → ForestState dimension simplex_count
dualForestState {dimension} {simplex_count} current =
  processForestRoots dimension simplex_count current simplex_count
    (forest_state [] [] []) (all_fin simplex_count)

dualForestEdges : Triangulation dimension simplex_count →
  List (DualForestEdge dimension simplex_count)
dualForestEdges current = forest_edges (dualForestState current)

dualForestEdgeCount : Triangulation dimension simplex_count → Nat
dualForestEdgeCount current = length (dualForestEdges current)

facetMember : Facet dimension simplex_count → List (Facet dimension simplex_count) → Bool
facetMember target [] = false
facetMember target (candidate ∷ remaining) =
  facet_equal target candidate or facetMember target remaining

dualForestFacets : Triangulation dimension simplex_count →
  List (Facet dimension simplex_count)
dualForestFacets current = fold_right
  (λ edge remaining → parent_facet edge ∷ child_facet edge ∷ remaining)
  [] (dualForestEdges current)

facetInDualForest : Triangulation dimension simplex_count →
  Facet dimension simplex_count → Bool
facetInDualForest current queriedFacet =
  facetMember queriedFacet (dualForestFacets current)

parentFacetOf : Triangulation dimension simplex_count →
  Fin simplex_count → Maybe (Facet dimension simplex_count)
parentFacetOf current target = findParent (dualForestEdges current)
  where
  findParent : List (DualForestEdge dimension simplex_count) →
    Maybe (Facet dimension simplex_count)
  findParent [] = nothing
  findParent (edge ∷ remaining)
    with fin_equal target (simplex_number (child_facet edge))
  ... | true = just (parent_facet edge)
  ... | false = findParent remaining

childFacetOf : Triangulation dimension simplex_count →
  Fin simplex_count → Maybe (Facet dimension simplex_count)
childFacetOf current target = findChild (dualForestEdges current)
  where
  findChild : List (DualForestEdge dimension simplex_count) →
    Maybe (Facet dimension simplex_count)
  findChild [] = nothing
  findChild (edge ∷ remaining)
    with fin_equal target (simplex_number (child_facet edge))
  ... | true = just (child_facet edge)
  ... | false = findChild remaining
