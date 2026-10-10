{-# OPTIONS --safe --without-K #-}

-- Reduction tests for dimension-three Face API properties.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-10.

module Regina.FacePropertyTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Input
open import Regina.Examples
open import Regina.Link3
open import Regina.FaceProperties3

private
  record VertexObservation : Set where
    constructor vertex_observation
    field
      observed_invalidity_code : Nat
      observed_vertex_flags_code : Nat
      observed_boundary : Bool
      observed_internal : Bool
      observed_link_closed : Bool
      observed_ideal : Bool
      observed_standard : Bool
      observed_link_orientable : Bool
      observed_link_euler : SignedInteger

  observeVertex : VertexProperties3 → VertexObservation
  observeVertex currentVertex = vertex_observation
    (coreWhyInvalidCode (vertex_core currentVertex))
    (vertex_flags_code currentVertex)
    (core_is_boundary (vertex_core currentVertex))
    (core_is_internal (vertex_core currentVertex))
    (vertex_link_closed currentVertex)
    (vertex_is_ideal currentVertex)
    (vertex_is_standard currentVertex)
    (core_link_orientable (vertex_core currentVertex))
    (vertex_link_euler_characteristic currentVertex)

  observeVertices : {simplex_count : Nat} →
    Triangulation 3 simplex_count → List VertexObservation
  observeVertices currentTriangulation =
    map observeVertex (vertexProperties currentTriangulation)

  record EdgeObservation : Set where
    constructor edge_observation
    field
      observed_edge_degree : Nat
      observed_edge_invalidity_code : Nat
      observed_edge_boundary : Bool
      observed_edge_internal : Bool
      observed_edge_link_closed : Bool
      observed_edge_valid : Bool

  observeEdge : EdgeProperties3 → EdgeObservation
  observeEdge currentEdge = edge_observation
    (core_face_degree (edge_core currentEdge))
    (coreWhyInvalidCode (edge_core currentEdge))
    (core_is_boundary (edge_core currentEdge))
    (core_is_internal (edge_core currentEdge))
    (edge_link_closed currentEdge)
    (coreIsValid (edge_core currentEdge))

  observeEdges : {simplex_count : Nat} →
    Triangulation 3 simplex_count → List EdgeObservation
  observeEdges currentTriangulation =
    map observeEdge (edgeProperties currentTriangulation)

  countTrue : List Bool → Nat
  countTrue [] = zero
  countTrue (false ∷ remainingValues) = countTrue remainingValues
  countTrue (true ∷ remainingValues) = suc (countTrue remainingValues)

  countForestTriangles : {simplex_count : Nat} →
    Triangulation 3 simplex_count → Nat
  countForestTriangles currentTriangulation = countTrue
    (map triangle_maximal_forest_member
      (triangleProperties currentTriangulation))

  countBoundaryTriangles : {simplex_count : Nat} →
    Triangulation 3 simplex_count → Nat
  countBoundaryTriangles currentTriangulation = countTrue
    (map (λ currentTriangle → core_is_boundary
      (triangle_core currentTriangle))
      (triangleProperties currentTriangulation))

  reversedEdgePair : Outcome (Triangulation 3 1)
  reversedEdgePair = from_input_gluings false 3 1
    (input_gluing 0 0 0 (1 ∷ 0 ∷ 3 ∷ 2 ∷ []) ∷ [])

  invalidBoundaryVertexPair : Outcome (Triangulation 3 1)
  invalidBoundaryVertexPair = from_input_gluings false 3 1
    (input_gluing 0 0 0 (1 ∷ 3 ∷ 2 ∷ 0 ∷ []) ∷ [])

invalidity_codes_match_regina :
  map faceInvalidityCode
    (face_invalidity_bits false false ∷
     face_invalidity_bits true false ∷
     face_invalidity_bits false true ∷
     face_invalidity_bits true true ∷ []) ≡
    (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
invalidity_codes_match_regina = refl

vertex_flag_codes_match_regina :
  (vertexFlagsCode false false ∷
   vertexFlagsCode true false ∷
   vertexFlagsCode false true ∷
   vertexFlagsCode true true ∷ []) ≡
    (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
vertex_flag_codes_match_regina = refl

ball_vertices_have_real_boundary_disc_links :
  observeVertices (ball 3) ≡
    (vertex_observation 0 2 true false false false true true
      (signed_positive 0) ∷
     vertex_observation 0 2 true false false false true true
      (signed_positive 0) ∷
     vertex_observation 0 2 true false false false true true
      (signed_positive 0) ∷
     vertex_observation 0 2 true false false false true true
      (signed_positive 0) ∷ [])
ball_vertices_have_real_boundary_disc_links = refl

sphere_vertices_are_internal_and_have_sphere_links :
  map_outcome observeVertices (sphere 3) ≡
    accepted
      (vertex_observation 0 0 false true true false true true
        (signed_positive 1) ∷
       vertex_observation 0 0 false true true false true true
        (signed_positive 1) ∷
       vertex_observation 0 0 false true true false true true
        (signed_positive 1) ∷
       vertex_observation 0 0 false true true false true true
        (signed_positive 1) ∷ [])
sphere_vertices_are_internal_and_have_sphere_links = refl

ball_bundle_vertex_has_real_boundary_flag :
  map_outcome observeVertices three_dimensional_ball_bundle ≡
    accepted
      (vertex_observation 0 2 true false false false true true
        (signed_positive 0) ∷ [])
ball_bundle_vertex_has_real_boundary_flag = refl

figure_eight_vertex_is_closed_ideal_and_standard :
  map_outcome observeVertices figure_eight_knot_complement ≡
    accepted
      (vertex_observation 0 1 true false true true true true
        signed_zero ∷ [])
figure_eight_vertex_is_closed_ideal_and_standard = refl

ball_edges_are_boundary_degree_one_faces :
  observeEdges (ball 3) ≡
    (edge_observation 1 0 true false false true ∷
     edge_observation 1 0 true false false true ∷
     edge_observation 1 0 true false false true ∷
     edge_observation 1 0 true false false true ∷
     edge_observation 1 0 true false false true ∷
     edge_observation 1 0 true false false true ∷ [])
ball_edges_are_boundary_degree_one_faces = refl

sphere_edges_are_internal_degree_two_faces :
  map_outcome observeEdges (sphere 3) ≡
    accepted
      (edge_observation 2 0 false true true true ∷
       edge_observation 2 0 false true true true ∷
       edge_observation 2 0 false true true true ∷
       edge_observation 2 0 false true true true ∷
       edge_observation 2 0 false true true true ∷
       edge_observation 2 0 false true true true ∷ [])
sphere_edges_are_internal_degree_two_faces = refl

reversed_edge_uses_invalid_identification_bit :
  map_outcome
    (λ currentTriangulation → any
      (λ currentEdge → nat_equal
        (coreWhyInvalidCode (edge_core currentEdge)) 1)
      (edgeProperties currentTriangulation))
    reversedEdgePair ≡ accepted true
reversed_edge_uses_invalid_identification_bit = refl

invalid_boundary_vertex_uses_invalid_link_bit :
  map_outcome
    (λ currentTriangulation → any
      (λ currentVertex → coreHasBadLink (vertex_core currentVertex))
      (vertexProperties currentTriangulation))
    invalidBoundaryVertexPair ≡ accepted true
invalid_boundary_vertex_uses_invalid_link_bit = refl

ball_triangles_are_boundary_and_not_forest_edges :
  (countBoundaryTriangles (ball 3) ∷
   countForestTriangles (ball 3) ∷ []) ≡ (4 ∷ 0 ∷ [])
ball_triangles_are_boundary_and_not_forest_edges = refl

sphere_has_one_triangle_in_the_dual_forest :
  map_outcome
    (λ currentTriangulation →
      countBoundaryTriangles currentTriangulation ∷
      countForestTriangles currentTriangulation ∷ [])
    (sphere 3) ≡ accepted (0 ∷ 1 ∷ [])
sphere_has_one_triangle_in_the_dual_forest = refl

figure_eight_has_one_triangle_in_the_dual_forest :
  map_outcome countForestTriangles figure_eight_knot_complement ≡ accepted 1
figure_eight_has_one_triangle_in_the_dual_forest = refl
