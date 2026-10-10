{-# OPTIONS --safe --without-K #-}

-- Reduction tests for three-dimensional vertex-link Euler data.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-10.

module Regina.Link3Tests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Input
open import Regina.Examples
open import Regina.Link3

private
  record LinkObservation : Set where
    constructor link_observation
    field
      observed_degree : Nat
      observed_boundary : Bool
      observed_orientable : Bool
      observed_even_numerator : Bool
      observed_euler : SignedInteger
      observed_kind : VertexLinkKind

  observeLink : VertexLinkSummary → LinkObservation
  observeLink currentSummary = link_observation
    (vertex_embedding_degree currentSummary)
    (vertex_touches_boundary currentSummary)
    (vertex_link_orientable currentSummary)
    (vertex_link_numerator_even currentSummary)
    (vertex_link_euler_characteristic currentSummary)
    (vertex_link_kind currentSummary)

  observeLinks : {simplex_count : Nat} → Triangulation 3 simplex_count →
    List LinkObservation
  observeLinks currentTriangulation =
    map observeLink (threeDimensionalVertexLinkSummaries currentTriangulation)

  record ThreeDimensionalFlags : Set where
    constructor three_dimensional_flags
    field
      locally_valid : Bool
      ideal : Bool
      standard : Bool

  observeFlags : {simplex_count : Nat} → Triangulation 3 simplex_count →
    ThreeDimensionalFlags
  observeFlags currentTriangulation = three_dimensional_flags
    (threeDimensionalLocallyValid currentTriangulation)
    (threeDimensionalIsIdeal currentTriangulation)
    (threeDimensionalIsStandard currentTriangulation)

  reversedEdgePair : Outcome (Triangulation 3 1)
  reversedEdgePair = from_input_gluings false 3 1
    (input_gluing 0 0 0 (1 ∷ 0 ∷ 3 ∷ 2 ∷ []) ∷ [])

subtraction_and_halving_positive_checked :
  subtractThenHalf 6 4 ≡ signed_positive 0
subtraction_and_halving_positive_checked = refl

subtraction_and_halving_zero_checked :
  subtractThenHalf 8 8 ≡ signed_zero
subtraction_and_halving_zero_checked = refl

subtraction_and_halving_negative_checked :
  subtractThenHalf 2 4 ≡ signed_negative 0
subtraction_and_halving_negative_checked = refl

ball_vertex_links_are_discs :
  observeLinks (ball 3) ≡
    (link_observation 1 true true true (signed_positive 0)
      real_boundary_link ∷
     link_observation 1 true true true (signed_positive 0)
      real_boundary_link ∷
     link_observation 1 true true true (signed_positive 0)
      real_boundary_link ∷
     link_observation 1 true true true (signed_positive 0)
      real_boundary_link ∷ [])
ball_vertex_links_are_discs = refl

sphere_vertex_links_are_two_spheres :
  map_outcome observeLinks (sphere 3) ≡
    accepted
      (link_observation 2 false true true (signed_positive 1)
        finite_interior_link ∷
       link_observation 2 false true true (signed_positive 1)
        finite_interior_link ∷
       link_observation 2 false true true (signed_positive 1)
        finite_interior_link ∷
       link_observation 2 false true true (signed_positive 1)
        finite_interior_link ∷ [])
sphere_vertex_links_are_two_spheres = refl

ball_bundle_vertex_link_is_a_disc :
  map_outcome observeLinks three_dimensional_ball_bundle ≡
    accepted
      (link_observation 4 true true true (signed_positive 0)
        real_boundary_link ∷ [])
ball_bundle_vertex_link_is_a_disc = refl

figure_eight_vertex_link_has_euler_zero :
  map_outcome observeLinks figure_eight_knot_complement ≡
    accepted
      (link_observation 8 false true true signed_zero ideal_link ∷ [])
figure_eight_vertex_link_has_euler_zero = refl

ball_flags_checked :
  observeFlags (ball 3) ≡ three_dimensional_flags true false true
ball_flags_checked = refl

sphere_flags_checked :
  map_outcome observeFlags (sphere 3) ≡
    accepted (three_dimensional_flags true false true)
sphere_flags_checked = refl

ball_bundle_flags_checked :
  map_outcome observeFlags three_dimensional_ball_bundle ≡
    accepted (three_dimensional_flags true false true)
ball_bundle_flags_checked = refl

figure_eight_is_standard_and_ideal :
  map_outcome observeFlags figure_eight_knot_complement ≡
    accepted (three_dimensional_flags true true true)
figure_eight_is_standard_and_ideal = refl

reversed_edge_identification_fails_local_validity :
  map_outcome threeDimensionalLocallyValid reversedEdgePair ≡ accepted false
reversed_edge_identification_fails_local_validity = refl
