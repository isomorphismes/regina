{-# OPTIONS --safe --without-K #-}

-- Reduction tests for canonical real-boundary facet orientation labels.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-10.

module Regina.BoundaryLabelTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.BoundaryLabels3

private
  record AssignmentObservation : Set where
    constructor assignment_observation
    field
      observed_facet_count : Nat
      observed_complete : Bool
      observed_root_positive : Bool
      observed_orientable : Bool
      observed_conflict : Bool

  observeAssignment : RealBoundaryOrientationAssignment →
    AssignmentObservation
  observeAssignment currentAssignment = assignment_observation
    (assignmentFacetCount currentAssignment)
    (orientation_assignment_complete currentAssignment)
    (assignmentRootPositive currentAssignment)
    (orientation_assignment_value currentAssignment)
    (assignmentHasConflict currentAssignment)

  observeAssignments : {simplex_count : Nat} →
    Triangulation 3 simplex_count → List AssignmentObservation
  observeAssignments currentTriangulation = map observeAssignment
    (realBoundaryOrientationAssignments currentTriangulation)

ball_assigns_four_consistent_boundary_facets :
  observeAssignments (ball 3) ≡
    (assignment_observation 4 true true true false ∷ [])
ball_assigns_four_consistent_boundary_facets = refl

sphere_has_no_real_boundary_orientation_assignment :
  map_outcome observeAssignments (sphere 3) ≡ accepted []
sphere_has_no_real_boundary_orientation_assignment = refl

ball_bundle_assigns_two_consistent_boundary_facets :
  map_outcome observeAssignments three_dimensional_ball_bundle ≡
    accepted
      (assignment_observation 2 true true true false ∷ [])
ball_bundle_assigns_two_consistent_boundary_facets = refl

figure_eight_has_no_real_boundary_orientation_assignment :
  map_outcome observeAssignments figure_eight_knot_complement ≡ accepted []
figure_eight_has_no_real_boundary_orientation_assignment = refl
