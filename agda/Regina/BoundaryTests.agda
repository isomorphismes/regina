{-# OPTIONS --safe --without-K #-}

-- Reduction tests for three-dimensional boundary components.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-10.

module Regina.BoundaryTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.Link3
open import Regina.Boundary3

private
  record BoundaryShape : Set where
    constructor boundary_shape
    field
      observed_kind : BoundaryComponentKind
      observed_vertices : Nat
      observed_edges : Nat
      observed_triangles : Nat
      observed_euler : SignedInteger
      observed_orientation_computed : Bool
      observed_orientable : Bool

  observeBoundary : BoundaryComponent3 → BoundaryShape
  observeBoundary currentComponent = boundary_shape
    (boundary_component_kind currentComponent)
    (boundary_vertex_count currentComponent)
    (boundary_edge_count currentComponent)
    (boundary_triangle_count currentComponent)
    (boundary_euler_characteristic currentComponent)
    (boundary_orientation_computed currentComponent)
    (boundary_is_orientable currentComponent)

  observeBoundaries : {simplex_count : Nat} →
    Triangulation 3 simplex_count → List BoundaryShape
  observeBoundaries currentTriangulation =
    map observeBoundary (boundaryComponents currentTriangulation)

  record BoundaryCounts : Set where
    constructor boundary_counts
    field
      total_boundaries : Nat
      real_boundaries : Nat
      ideal_boundaries : Nat

  observeCounts : {simplex_count : Nat} →
    Triangulation 3 simplex_count → BoundaryCounts
  observeCounts currentTriangulation = boundary_counts
    (boundaryComponentCount currentTriangulation)
    (realBoundaryComponentCount currentTriangulation)
    (idealBoundaryComponentCount currentTriangulation)

ball_boundary_is_one_four_triangle_sphere :
  observeBoundaries (ball 3) ≡
    (boundary_shape real_boundary_component 4 6 4
      (signed_positive 1) false false ∷ [])
ball_boundary_is_one_four_triangle_sphere = refl

sphere_has_no_boundary_components :
  map_outcome observeBoundaries (sphere 3) ≡ accepted []
sphere_has_no_boundary_components = refl

ball_bundle_boundary_is_two_triangle_torus :
  map_outcome observeBoundaries three_dimensional_ball_bundle ≡
    accepted
      (boundary_shape real_boundary_component 1 3 2
        signed_zero false false ∷ [])
ball_bundle_boundary_is_two_triangle_torus = refl

figure_eight_has_one_ideal_torus_boundary :
  map_outcome observeBoundaries figure_eight_knot_complement ≡
    accepted
      (boundary_shape ideal_boundary_component 4 12 8
        signed_zero true true ∷ [])
figure_eight_has_one_ideal_torus_boundary = refl

ball_boundary_counts_checked :
  observeCounts (ball 3) ≡ boundary_counts 1 1 0
ball_boundary_counts_checked = refl

sphere_boundary_counts_checked :
  map_outcome observeCounts (sphere 3) ≡
    accepted (boundary_counts 0 0 0)
sphere_boundary_counts_checked = refl

figure_eight_boundary_counts_checked :
  map_outcome observeCounts figure_eight_knot_complement ≡
    accepted (boundary_counts 1 0 1)
figure_eight_boundary_counts_checked = refl
