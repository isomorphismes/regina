{-# OPTIONS --safe --without-K #-}

-- Reduction tests for the lower-dimensional Regina face quotient.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-09.

module Regina.SkeletonTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.Skeleton

private
  record DegreeProfile : Set where
    constructor degree_profile
    field
      degree_one : Nat
      degree_two : Nat
      degree_three : Nat
      degree_four : Nat
      degree_six : Nat
      degree_eight : Nat

  profile : {simplex_dimension number_of_simplices : Nat} →
    Triangulation simplex_dimension number_of_simplices → Nat → DegreeProfile
  profile current requested_face_dimension = degree_profile
    (face_classes_of_degree current requested_face_dimension 1)
    (face_classes_of_degree current requested_face_dimension 2)
    (face_classes_of_degree current requested_face_dimension 3)
    (face_classes_of_degree current requested_face_dimension 4)
    (face_classes_of_degree current requested_face_dimension 6)
    (face_classes_of_degree current requested_face_dimension 8)

ball_three_skeleton_counts : skeleton_face_counts (ball 3) ≡
  (4 ∷ 6 ∷ 4 ∷ [])
ball_three_skeleton_counts = refl

ball_three_vertices_are_unidentified :
  profile (ball 3) 0 ≡ degree_profile 4 0 0 0 0 0
ball_three_vertices_are_unidentified = refl

ball_three_edges_are_unidentified :
  profile (ball 3) 1 ≡ degree_profile 6 0 0 0 0 0
ball_three_edges_are_unidentified = refl

sphere_three_skeleton_counts :
  map_outcome skeleton_face_counts (sphere 3) ≡ accepted (4 ∷ 6 ∷ 4 ∷ [])
sphere_three_skeleton_counts = refl

sphere_three_every_local_vertex_is_paired_once :
  map_outcome (λ current → profile current 0) (sphere 3) ≡
    accepted (degree_profile 0 4 0 0 0 0)
sphere_three_every_local_vertex_is_paired_once = refl

sphere_three_every_local_edge_is_paired_once :
  map_outcome (λ current → profile current 1) (sphere 3) ≡
    accepted (degree_profile 0 6 0 0 0 0)
sphere_three_every_local_edge_is_paired_once = refl

ball_bundle_three_skeleton_counts :
  map_outcome skeleton_face_counts three_dimensional_ball_bundle ≡
    accepted (1 ∷ 3 ∷ 3 ∷ [])
ball_bundle_three_skeleton_counts = refl

ball_bundle_three_has_one_fourfold_vertex_class :
  map_outcome (λ current → profile current 0) three_dimensional_ball_bundle ≡
    accepted (degree_profile 0 0 0 1 0 0)
ball_bundle_three_has_one_fourfold_vertex_class = refl

ball_bundle_three_edge_degrees :
  map_outcome (λ current → profile current 1) three_dimensional_ball_bundle ≡
    accepted (degree_profile 1 1 1 0 0 0)
ball_bundle_three_edge_degrees = refl

ball_bundle_three_facet_degrees :
  map_outcome (λ current → profile current 2) three_dimensional_ball_bundle ≡
    accepted (degree_profile 2 1 0 0 0 0)
ball_bundle_three_facet_degrees = refl

figure_eight_skeleton_counts :
  map_outcome skeleton_face_counts figure_eight_knot_complement ≡
    accepted (1 ∷ 2 ∷ 4 ∷ [])
figure_eight_skeleton_counts = refl

figure_eight_has_one_ideal_vertex_class :
  map_outcome (λ current → profile current 0) figure_eight_knot_complement ≡
    accepted (degree_profile 0 0 0 0 0 1)
figure_eight_has_one_ideal_vertex_class = refl

figure_eight_has_two_degree_six_edge_classes :
  map_outcome (λ current → profile current 1) figure_eight_knot_complement ≡
    accepted (degree_profile 0 0 0 0 2 0)
figure_eight_has_two_degree_six_edge_classes = refl

figure_eight_has_four_paired_facet_classes :
  map_outcome (λ current → profile current 2) figure_eight_knot_complement ≡
    accepted (degree_profile 0 4 0 0 0 0)
figure_eight_has_four_paired_facet_classes = refl

face_dimension_must_be_below_simplex_dimension :
  face_class_count (ball 3) 3 ≡ 0
face_dimension_must_be_below_simplex_dimension = refl
