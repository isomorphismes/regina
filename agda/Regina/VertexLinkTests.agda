{-# OPTIONS --safe --without-K #-}

-- Reduction tests for explicit three-dimensional vertex-link surfaces.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-10.

module Regina.VertexLinkTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.Link3
open import Regina.VertexLinkSurface3

private
  record ExplicitLinkShape : Set where
    constructor explicit_link_shape
    field
      observed_triangles : Nat
      observed_vertices : Nat
      observed_edges : Nat
      observed_boundary_edges : Nat
      observed_paired_sides : Nat
      observed_euler_characteristic : SignedInteger
      observed_corners_resolved : Bool
      observed_pairings_resolved : Bool
      observed_pairings_reciprocal : Bool
      observed_bad_identification : Bool
      observed_orientable : Bool

  observeExplicitLink : {simplex_count : Nat} →
    ExplicitVertexLink simplex_count → ExplicitLinkShape
  observeExplicitLink currentLink = explicit_link_shape
    (explicitLinkTriangleCount currentLink)
    (explicitLinkVertexCount currentLink)
    (explicitLinkEdgeCount currentLink)
    (explicitLinkBoundaryEdgeCount currentLink)
    (explicitLinkPairedSideCount currentLink)
    (explicitLinkEulerCharacteristic currentLink)
    (explicitLinkCornersResolved currentLink)
    (explicitLinkPairingsResolved currentLink)
    (explicitLinkPairingsReciprocal currentLink)
    (explicit_link_has_bad_identification currentLink)
    (explicit_link_is_orientable currentLink)

  observeExplicitLinks : {simplex_count : Nat} →
    Triangulation 3 simplex_count → List ExplicitLinkShape
  observeExplicitLinks currentTriangulation =
    map observeExplicitLink (explicitVertexLinks currentTriangulation)

ball_has_four_single_triangle_disc_links :
  observeExplicitLinks (ball 3) ≡
    (explicit_link_shape 1 3 3 3 0 (signed_positive 0)
      true true true false true ∷
     explicit_link_shape 1 3 3 3 0 (signed_positive 0)
      true true true false true ∷
     explicit_link_shape 1 3 3 3 0 (signed_positive 0)
      true true true false true ∷
     explicit_link_shape 1 3 3 3 0 (signed_positive 0)
      true true true false true ∷ [])
ball_has_four_single_triangle_disc_links = refl

sphere_has_four_two_triangle_sphere_links :
  map_outcome observeExplicitLinks (sphere 3) ≡
    accepted
      (explicit_link_shape 2 3 3 0 6 (signed_positive 1)
        true true true false true ∷
       explicit_link_shape 2 3 3 0 6 (signed_positive 1)
        true true true false true ∷
       explicit_link_shape 2 3 3 0 6 (signed_positive 1)
        true true true false true ∷
       explicit_link_shape 2 3 3 0 6 (signed_positive 1)
        true true true false true ∷ [])
sphere_has_four_two_triangle_sphere_links = refl

ball_bundle_link_has_four_triangles_and_six_boundary_edges :
  map_outcome observeExplicitLinks three_dimensional_ball_bundle ≡
    accepted
      (explicit_link_shape 4 6 9 6 6 (signed_positive 0)
        true true true false true ∷ [])
ball_bundle_link_has_four_triangles_and_six_boundary_edges = refl

figure_eight_link_has_eight_triangles_and_euler_zero :
  map_outcome observeExplicitLinks figure_eight_knot_complement ≡
    accepted
      (explicit_link_shape 8 4 12 0 24 signed_zero
        true true true false true ∷ [])
figure_eight_link_has_eight_triangles_and_euler_zero = refl

ball_link_side_count_is_three_per_triangle :
  map
    (λ currentLink → length (triangle_sides currentLink))
    (explicitVertexLinks (ball 3)) ≡ (3 ∷ 3 ∷ 3 ∷ 3 ∷ [])
ball_link_side_count_is_three_per_triangle = refl

sphere_link_side_count_is_three_per_triangle :
  map_outcome
    (λ currentTriangulation → map
      (λ currentLink → length (triangle_sides currentLink))
      (explicitVertexLinks currentTriangulation))
    (sphere 3) ≡ accepted (6 ∷ 6 ∷ 6 ∷ 6 ∷ [])
sphere_link_side_count_is_three_per_triangle = refl

figure_eight_all_link_sides_are_paired :
  map_outcome
    (λ currentTriangulation → map explicitLinkBoundaryEdgeCount
      (explicitVertexLinks currentTriangulation))
    figure_eight_knot_complement ≡ accepted (0 ∷ [])
figure_eight_all_link_sides_are_paired = refl

explicit_euler_matches_previous_figure_eight_result :
  map_outcome
    (λ currentTriangulation → map explicitLinkEulerCharacteristic
      (explicitVertexLinks currentTriangulation))
    figure_eight_knot_complement ≡ accepted (signed_zero ∷ [])
explicit_euler_matches_previous_figure_eight_result = refl
