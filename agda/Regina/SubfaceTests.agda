{-# OPTIONS --safe --without-K #-}

-- Reduction tests for dimension-three subface lookup and mappings.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-10.

module Regina.SubfaceTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.SubfaceIncidence3

private
  record ResolutionSummary : Set where
    constructor resolution_summary
    field
      edge_vertices_resolved : Bool
      triangle_vertices_resolved : Bool
      triangle_edges_resolved : Bool
      edge_vertex_numbering_valid : Bool
      triangle_vertex_numbering_valid : Bool
      triangle_edge_numbering_valid : Bool

  observeResolution : {simplex_count : Nat} →
    Triangulation 3 simplex_count → ResolutionSummary
  observeResolution currentTriangulation = resolution_summary
    (edgeVertexReferencesResolved currentTriangulation)
    (triangleVertexReferencesResolved currentTriangulation)
    (triangleEdgeReferencesResolved currentTriangulation)
    (allEdgeVertexNumberingValid currentTriangulation)
    (allTriangleVertexNumberingValid currentTriangulation)
    (allTriangleEdgeNumberingValid currentTriangulation)

  triangleContainsReportedVertex : {simplex_count : Nat} →
    Triangulation 3 simplex_count → Nat → Maybe SubfaceReference3 → Bool
  triangleContainsReportedVertex currentTriangulation triangleClassNumber
    nothing = false
  triangleContainsReportedVertex currentTriangulation triangleClassNumber
    (just currentReference) = triangleContainsVertexClass currentTriangulation
    triangleClassNumber (referenced_face_class_number currentReference)

  triangleContainsReportedEdge : {simplex_count : Nat} →
    Triangulation 3 simplex_count → Nat → Maybe SubfaceReference3 → Bool
  triangleContainsReportedEdge currentTriangulation triangleClassNumber
    nothing = false
  triangleContainsReportedEdge currentTriangulation triangleClassNumber
    (just currentReference) = triangleContainsEdgeClass currentTriangulation
    triangleClassNumber (referenced_face_class_number currentReference)

ball_subfaces_and_mappings_resolve :
  observeResolution (ball 3) ≡
    resolution_summary true true true true true true
ball_subfaces_and_mappings_resolve = refl

sphere_subfaces_and_mappings_resolve :
  map_outcome observeResolution (sphere 3) ≡
    accepted (resolution_summary true true true true true true)
sphere_subfaces_and_mappings_resolve = refl

ball_bundle_subfaces_and_mappings_resolve :
  map_outcome observeResolution three_dimensional_ball_bundle ≡
    accepted (resolution_summary true true true true true true)
ball_bundle_subfaces_and_mappings_resolve = refl

figure_eight_subfaces_and_mappings_resolve :
  map_outcome observeResolution figure_eight_knot_complement ≡
    accepted (resolution_summary true true true true true true)
figure_eight_subfaces_and_mappings_resolve = refl

ball_edge_vertex_incidences_are_tetrahedral :
  edgeVertexIncidenceCounts (ball 3) ≡ (3 ∷ 3 ∷ 3 ∷ 3 ∷ [])
ball_edge_vertex_incidences_are_tetrahedral = refl

ball_triangle_vertex_incidences_are_tetrahedral :
  triangleVertexIncidenceCounts (ball 3) ≡ (3 ∷ 3 ∷ 3 ∷ 3 ∷ [])
ball_triangle_vertex_incidences_are_tetrahedral = refl

ball_triangle_edge_incidences_are_tetrahedral :
  triangleEdgeIncidenceCounts (ball 3) ≡
    (2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ [])
ball_triangle_edge_incidences_are_tetrahedral = refl

sphere_has_the_same_global_face_incidences :
  map_outcome
    (λ currentTriangulation →
      edgeVertexIncidenceCounts currentTriangulation ∷
      triangleVertexIncidenceCounts currentTriangulation ∷
      triangleEdgeIncidenceCounts currentTriangulation ∷ [])
    (sphere 3) ≡ accepted
      ((3 ∷ 3 ∷ 3 ∷ 3 ∷ []) ∷
       (3 ∷ 3 ∷ 3 ∷ 3 ∷ []) ∷
       (2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ []) ∷ [])
sphere_has_the_same_global_face_incidences = refl

ball_edges_are_not_loops :
  edgeLoopFlags (ball 3) ≡
    (false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ [])
ball_edges_are_not_loops = refl

sphere_edges_are_not_loops :
  map_outcome edgeLoopFlags (sphere 3) ≡
    accepted (false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ [])
sphere_edges_are_not_loops = refl

figure_eight_edges_are_loops :
  map_outcome edgeLoopFlags figure_eight_knot_complement ≡
    accepted (true ∷ true ∷ [])
figure_eight_edges_are_loops = refl

figure_eight_loop_endpoints_keep_distinct_face_mappings :
  map_outcome
    (λ currentTriangulation →
      edgeEndpointReport currentTriangulation 0 ∷
      edgeEndpointReport currentTriangulation 1 ∷ [])
    figure_eight_knot_complement ≡ accepted
      (just (edge_endpoint_report_three 0 0 0 1) ∷
       just (edge_endpoint_report_three 0 0 0 1) ∷ [])
figure_eight_loop_endpoints_keep_distinct_face_mappings = refl

figure_eight_vertex_incidences_count_endpoint_roles :
  map_outcome
    (λ currentTriangulation →
      edgeVertexIncidenceCounts currentTriangulation ∷
      triangleVertexIncidenceCounts currentTriangulation ∷ [])
    figure_eight_knot_complement ≡ accepted
      ((4 ∷ []) ∷ (12 ∷ []) ∷ [])
figure_eight_vertex_incidences_count_endpoint_roles = refl

figure_eight_edge_incidences_match_edge_degrees :
  map_outcome triangleEdgeIncidenceCounts figure_eight_knot_complement ≡
    accepted (6 ∷ 6 ∷ [])
figure_eight_edge_incidences_match_edge_degrees = refl

ball_first_triangle_contains_its_reported_subfaces :
  triangleContainsReportedVertex (ball 3) 0
    (triangleVertexReference (ball 3) 0 0) and
  triangleContainsReportedEdge (ball 3) 0
    (triangleEdgeReference (ball 3) 0 0) ≡ true
ball_first_triangle_contains_its_reported_subfaces = refl
