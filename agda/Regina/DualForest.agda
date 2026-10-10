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

processForestFacetAfterDiscovery :
  Triangulation dimension simplex_count →
  Fin simplex_count → Fin (suc dimension) →
  ForestState dimension simplex_count → Gluing dimension simplex_count → Bool →
  ForestState dimension simplex_count
processForestFacetAfterDiscovery current sourceSimplex localFacetNumber currentForest outward true =
  currentForest
processForestFacetAfterDiscovery current sourceSimplex localFacetNumber currentForest outward false =
  forest_state
    (appendOne (discovered_simplices currentForest) (adjacent_simplex outward))
    (appendOne (pending_simplices currentForest) (adjacent_simplex outward))
    (appendOne (forest_edges currentForest)
      (dual_forest_edge (facet sourceSimplex localFacetNumber)
        (destination (facet sourceSimplex localFacetNumber) outward)))

processForestFacetAfterLookup :
  Triangulation dimension simplex_count →
  Fin simplex_count → Fin (suc dimension) →
  ForestState dimension simplex_count → Maybe (Gluing dimension simplex_count) →
  ForestState dimension simplex_count
processForestFacetAfterLookup current sourceSimplex localFacetNumber currentForest nothing =
  currentForest
processForestFacetAfterLookup current sourceSimplex localFacetNumber currentForest
  (just outward) = processForestFacetAfterDiscovery current sourceSimplex
    localFacetNumber currentForest outward
    (memberIndex (adjacent_simplex outward) (discovered_simplices currentForest))

processForestFacet : Triangulation dimension simplex_count →
  Fin simplex_count → Fin (suc dimension) → ForestState dimension simplex_count →
  ForestState dimension simplex_count
processForestFacet current sourceSimplex localFacetNumber currentForest =
  processForestFacetAfterLookup current sourceSimplex localFacetNumber currentForest
    (adjacency (raw_state current) (facet sourceSimplex localFacetNumber))

processForestFacets : Triangulation dimension simplex_count →
  Fin simplex_count → List (Fin (suc dimension)) →
  ForestState dimension simplex_count → ForestState dimension simplex_count
processForestFacets current sourceSimplex [] currentForest = currentForest
processForestFacets current sourceSimplex (localFacetNumber ∷ remaining) currentForest =
  processForestFacets current sourceSimplex remaining
    (processForestFacet current sourceSimplex localFacetNumber currentForest)

walkForestQueue : (simplexDimension numberOfSimplices : Nat) → Nat →
  Triangulation simplexDimension numberOfSimplices →
  ForestState simplexDimension numberOfSimplices →
  ForestState simplexDimension numberOfSimplices
walkForestQueue simplexDimension numberOfSimplices zero current currentForest = currentForest
walkForestQueue simplexDimension numberOfSimplices (suc fuel) current currentForest
  with pending_simplices currentForest
... | [] = currentForest
... | sourceSimplex ∷ remaining =
  walkForestQueue simplexDimension numberOfSimplices fuel current
    (processForestFacets current sourceSimplex (all_fin (suc simplexDimension))
      (forest_state (discovered_simplices currentForest) remaining
        (forest_edges currentForest)))

startForestRootAfterMembership :
  (simplexDimension numberOfSimplices : Nat) →
  Triangulation simplexDimension numberOfSimplices → Nat →
  ForestState simplexDimension numberOfSimplices → Fin numberOfSimplices → Bool →
  ForestState simplexDimension numberOfSimplices
startForestRootAfterMembership simplexDimension numberOfSimplices current fuel
  currentForest root true = currentForest
startForestRootAfterMembership simplexDimension numberOfSimplices current fuel
  currentForest root false =
  walkForestQueue simplexDimension numberOfSimplices fuel current
    (forest_state
      (appendOne (discovered_simplices currentForest) root)
      (appendOne (pending_simplices currentForest) root)
      (forest_edges currentForest))

startForestRoot : (simplexDimension numberOfSimplices : Nat) →
  Triangulation simplexDimension numberOfSimplices → Nat →
  ForestState simplexDimension numberOfSimplices → Fin numberOfSimplices →
  ForestState simplexDimension numberOfSimplices
startForestRoot simplexDimension numberOfSimplices current fuel currentForest root =
  startForestRootAfterMembership simplexDimension numberOfSimplices current fuel
    currentForest root (memberIndex root (discovered_simplices currentForest))

processForestRoots : (simplexDimension numberOfSimplices : Nat) →
  Triangulation simplexDimension numberOfSimplices → Nat →
  ForestState simplexDimension numberOfSimplices → List (Fin numberOfSimplices) →
  ForestState simplexDimension numberOfSimplices
processForestRoots simplexDimension numberOfSimplices current fuel currentForest [] =
  currentForest
processForestRoots simplexDimension numberOfSimplices current fuel currentForest
  (root ∷ remaining) =
  processForestRoots simplexDimension numberOfSimplices current fuel
    (startForestRoot simplexDimension numberOfSimplices current fuel currentForest root)
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
  findParent (edge ∷ remaining) with
    fin_equal target (simplex_number (child_facet edge))
  ... | true = just (parent_facet edge)
  ... | false = findParent remaining

childFacetOf : Triangulation dimension simplex_count →
  Fin simplex_count → Maybe (Facet dimension simplex_count)
childFacetOf current target = findChild (dualForestEdges current)
  where
  findChild : List (DualForestEdge dimension simplex_count) →
    Maybe (Facet dimension simplex_count)
  findChild [] = nothing
  findChild (edge ∷ remaining) with
    fin_equal target (simplex_number (child_facet edge))
  ... | true = just (child_facet edge)
  ... | false = findChild remaining
