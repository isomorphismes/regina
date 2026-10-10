{-# OPTIONS --safe --without-K #-}

-- Reduction tests for exact dimension-three codimension-two ordering.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-10.

module Regina.ExactEdgeLinkTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Input
open import Regina.Examples
import Regina.Components as Components
open import Regina.ExactEdgeLinks3

private
  orientationObservation : {simplex_count : Nat} →
    SimplexOrientationLabel3 simplex_count → List Nat
  orientationObservation currentLabel =
    fin_to_nat (labelled_simplex currentLabel) ∷
    orientationNumber (labelled_simplex_orientation currentLabel) ∷ []
    where
    orientationNumber : Components.Orientation → Nat
    orientationNumber Components.positive = 1
    orientationNumber Components.negative = 0

  mapMaybeFinList : Maybe (List (Fin 4)) → Maybe (List Nat)
  mapMaybeFinList nothing = nothing
  mapMaybeFinList (just vertices) = just (map fin_to_nat vertices)

  evenOrderingTables : List (Maybe (List Nat))
  evenOrderingTables = map
    (λ edgeNumber → mapMaybeFinList (evenEdgeOrdering edgeNumber))
    (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])

  shapeIsPath : EdgeLinkShape3 → Bool
  shapeIsPath edge_link_path = true
  shapeIsPath edge_link_cycle = false
  shapeIsPath edge_link_incomplete = false

  allPathShapes : List EdgeLinkShape3 → Bool
  allPathShapes = all shapeIsPath

  shapeIsCycle : EdgeLinkShape3 → Bool
  shapeIsCycle edge_link_path = false
  shapeIsCycle edge_link_cycle = true
  shapeIsCycle edge_link_incomplete = false

  allCycleShapes : List EdgeLinkShape3 → Bool
  allCycleShapes = all shapeIsCycle

  exactLayerComplete : {simplex_count : Nat} →
    Triangulation 3 simplex_count → Bool
  exactLayerComplete currentTriangulation =
    allOrderedEdgeWalksComplete currentTriangulation and
    orderedEdgeOccurrencesComplete currentTriangulation and
    allOrderedEdgeStructuresValid currentTriangulation and
    allOrderedMappingsMatchSimplexOrientations currentTriangulation and
    allOrderedEdgeClassesMatchGeneric currentTriangulation

  record BoundaryEndpointObservation : Set where
    constructor boundary_endpoint_observation
    field
      observed_first_boundaries : List (Maybe Nat)
      observed_last_boundaries : List (Maybe Nat)

  observeBoundaryEndpoints : {simplex_count : Nat} →
    Triangulation 3 simplex_count → BoundaryEndpointObservation
  observeBoundaryEndpoints currentTriangulation =
    boundary_endpoint_observation
      (orderedEdgeFirstBoundaryNumbers currentTriangulation)
      (orderedEdgeLastBoundaryNumbers currentTriangulation)

  record DegreeShapeObservation : Set where
    constructor degree_shape_observation
    field
      observed_edge_degrees : List Nat
      observed_shape_test : Bool

  observePaths : {simplex_count : Nat} →
    Triangulation 3 simplex_count → DegreeShapeObservation
  observePaths currentTriangulation = degree_shape_observation
    (orderedEdgeDegrees currentTriangulation)
    (allPathShapes (orderedEdgeShapes currentTriangulation))

  observeCycles : {simplex_count : Nat} →
    Triangulation 3 simplex_count → DegreeShapeObservation
  observeCycles currentTriangulation = degree_shape_observation
    (orderedEdgeDegrees currentTriangulation)
    (allCycleShapes (orderedEdgeShapes currentTriangulation))

  positiveNatural : Nat → Bool
  positiveNatural zero = false
  positiveNatural (suc remaining) = true

  reversedEdgePair : Outcome (Triangulation 3 1)
  reversedEdgePair = from_input_gluings false 3 1
    (input_gluing 0 0 0 (1 ∷ 0 ∷ 3 ∷ 2 ∷ []) ∷ [])

source_edge_ordering_tables_checked :
  evenOrderingTables ≡
    (just (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ∷
     just (0 ∷ 2 ∷ 3 ∷ 1 ∷ []) ∷
     just (0 ∷ 3 ∷ 1 ∷ 2 ∷ []) ∷
     just (1 ∷ 2 ∷ 0 ∷ 3 ∷ []) ∷
     just (1 ∷ 3 ∷ 2 ∷ 0 ∷ []) ∷
     just (2 ∷ 3 ∷ 0 ∷ 1 ∷ []) ∷ [])
source_edge_ordering_tables_checked = refl

ball_simplex_orientation_is_positive :
  map orientationObservation (simplexOrientationLabels3 (ball 3)) ≡
    ((0 ∷ 1 ∷ []) ∷ [])
ball_simplex_orientation_is_positive = refl

sphere_simplex_orientations_follow_identity_gluing :
  map_outcome
    (λ currentTriangulation → map orientationObservation
      (simplexOrientationLabels3 currentTriangulation))
    (sphere 3) ≡ accepted
      ((0 ∷ 1 ∷ []) ∷ (1 ∷ 0 ∷ []) ∷ [])
sphere_simplex_orientations_follow_identity_gluing = refl

ball_edge_classes_follow_regina_seed_order :
  orderedEdgeSeedNumbers (ball 3) ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
ball_edge_classes_follow_regina_seed_order = refl

ball_edge_links_are_single_embedding_paths :
  orderedEdgeDegrees (ball 3) ≡ (1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ [])
ball_edge_links_are_single_embedding_paths = refl

ball_edge_link_shapes_are_paths :
  allPathShapes (orderedEdgeShapes (ball 3)) ≡ true
ball_edge_link_shapes_are_paths = refl

ball_edge_embedding_tables_match_source_ordering :
  map orderedEdgeEmbeddingTables (orderedEdgeLinks3 (ball 3)) ≡
    (((0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ∷ []) ∷
     ((0 ∷ 2 ∷ 3 ∷ 1 ∷ []) ∷ []) ∷
     ((0 ∷ 3 ∷ 1 ∷ 2 ∷ []) ∷ []) ∷
     ((1 ∷ 2 ∷ 0 ∷ 3 ∷ []) ∷ []) ∷
     ((1 ∷ 3 ∷ 2 ∷ 0 ∷ []) ∷ []) ∷
     ((2 ∷ 3 ∷ 0 ∷ 1 ∷ []) ∷ []) ∷ [])
ball_edge_embedding_tables_match_source_ordering = refl

ball_edge_path_end_facets_are_directed :
  observeBoundaryEndpoints (ball 3) ≡ boundary_endpoint_observation
    (just 3 ∷ just 1 ∷ just 2 ∷ just 3 ∷ just 0 ∷ just 1 ∷ [])
    (just 2 ∷ just 3 ∷ just 1 ∷ just 0 ∷ just 2 ∷ just 0 ∷ [])
ball_edge_path_end_facets_are_directed = refl

ball_exact_edge_layer_is_complete :
  exactLayerComplete (ball 3) ≡ true
ball_exact_edge_layer_is_complete = refl

sphere_edge_links_are_two_embedding_cycles :
  map_outcome orderedEdgeDegrees (sphere 3) ≡
    accepted (2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ [])
sphere_edge_links_are_two_embedding_cycles = refl

sphere_edge_link_shapes_are_cycles :
  map_outcome
    (λ currentTriangulation → allCycleShapes
      (orderedEdgeShapes currentTriangulation))
    (sphere 3) ≡ accepted true
sphere_edge_link_shapes_are_cycles = refl

sphere_edge_embeddings_run_from_simplex_zero_to_one :
  map_outcome
    (λ currentTriangulation → map orderedEdgeEmbeddingSimplexNumbers
      (orderedEdgeLinks3 currentTriangulation))
    (sphere 3) ≡ accepted
      ((0 ∷ 1 ∷ []) ∷
       (0 ∷ 1 ∷ []) ∷
       (0 ∷ 1 ∷ []) ∷
       (0 ∷ 1 ∷ []) ∷
       (0 ∷ 1 ∷ []) ∷
       (0 ∷ 1 ∷ []) ∷ [])
sphere_edge_embeddings_run_from_simplex_zero_to_one = refl

sphere_exact_edge_layer_is_complete :
  map_outcome exactLayerComplete (sphere 3) ≡ accepted true
sphere_exact_edge_layer_is_complete = refl

ball_bundle_has_directed_edge_paths_of_degrees_three_two_one :
  map_outcome observePaths three_dimensional_ball_bundle ≡
    accepted (degree_shape_observation (3 ∷ 2 ∷ 1 ∷ []) true)
ball_bundle_has_directed_edge_paths_of_degrees_three_two_one = refl

ball_bundle_exact_edge_layer_is_complete :
  map_outcome exactLayerComplete three_dimensional_ball_bundle ≡ accepted true
ball_bundle_exact_edge_layer_is_complete = refl

figure_eight_has_two_degree_six_edge_cycles :
  map_outcome observeCycles figure_eight_knot_complement ≡
    accepted (degree_shape_observation (6 ∷ 6 ∷ []) true)
figure_eight_has_two_degree_six_edge_cycles = refl

figure_eight_exact_edge_layer_is_complete :
  map_outcome exactLayerComplete figure_eight_knot_complement ≡ accepted true
figure_eight_exact_edge_layer_is_complete = refl

reversed_edge_identification_is_preserved_by_exact_walk :
  map_outcome
    (λ currentTriangulation → positiveNatural
      (orderedEdgeBadIdentificationCount currentTriangulation))
    reversedEdgePair ≡ accepted true
reversed_edge_identification_is_preserved_by_exact_walk = refl
