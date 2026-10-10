{-# OPTIONS --safe --without-K #-}

-- Reduction tests for source-shaped three-dimensional validity reports.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-10.

module Regina.ValidityTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Input
open import Regina.Examples
open import Regina.Validity3

private
  record ValidityObservation : Set where
    constructor validity_observation
    field
      observed_valid : Bool
      observed_orientable : Bool
      observed_ideal : Bool
      observed_standard : Bool
      observed_tetrahedron_faces_complete : Bool
      observed_explicit_links_complete : Bool
      observed_boundary_orientations_complete : Bool
      observed_reason_count : Nat

  observeValidity : ThreeDimensionalValidityReport → ValidityObservation
  observeValidity currentReport = validity_observation
    (report_validity_value currentReport)
    (report_triangulation_orientable currentReport)
    (report_triangulation_ideal currentReport)
    (report_triangulation_standard currentReport)
    (report_tetrahedron_face_mappings_complete currentReport)
    (report_explicit_vertex_links_complete currentReport)
    (report_real_boundary_orientations_complete currentReport)
    (length (report_invalidity_reasons currentReport))

  observeTriangulation : {simplex_count : Nat} →
    Triangulation 3 simplex_count → ValidityObservation
  observeTriangulation currentTriangulation =
    observeValidity (threeDimensionalValidityReport currentTriangulation)

  reversedEdgePair : Outcome (Triangulation 3 1)
  reversedEdgePair = from_input_gluings false 3 1
    (input_gluing 0 0 0 (1 ∷ 0 ∷ 3 ∷ 2 ∷ []) ∷ [])

ball_validity_report_checked :
  observeTriangulation (ball 3) ≡
    validity_observation true true false true true true true 0
ball_validity_report_checked = refl

sphere_validity_report_checked :
  map_outcome observeTriangulation (sphere 3) ≡
    accepted
      (validity_observation true true false true true true true 0)
sphere_validity_report_checked = refl

ball_bundle_validity_report_checked :
  map_outcome observeTriangulation three_dimensional_ball_bundle ≡
    accepted
      (validity_observation true true false true true true true 0)
ball_bundle_validity_report_checked = refl

figure_eight_validity_report_checked :
  map_outcome observeTriangulation figure_eight_knot_complement ≡
    accepted
      (validity_observation true true true true true true true 0)
figure_eight_validity_report_checked = refl

reversed_edge_fixture_is_invalid :
  map_outcome
    (λ currentTriangulation → report_validity_value
      (threeDimensionalValidityReport currentTriangulation))
    reversedEdgePair ≡ accepted false
reversed_edge_fixture_is_invalid = refl

reversed_edge_reason_is_reported :
  map_outcome
    (λ currentTriangulation → reasonMember reversed_edge_identification
      (report_invalidity_reasons
        (threeDimensionalValidityReport currentTriangulation)))
    reversedEdgePair ≡ accepted true
reversed_edge_reason_is_reported = refl
