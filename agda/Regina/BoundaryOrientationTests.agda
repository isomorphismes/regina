{-# OPTIONS --safe --without-K #-}

-- Reduction tests for real-boundary orientation and surface classification.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-10.

module Regina.BoundaryOrientationTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.Link3
open import Regina.Boundary3
open import Regina.BoundarySurface3

private
  record SurfaceObservation : Set where
    constructor surface_observation
    field
      observed_boundary_kind : BoundaryComponentKind
      observed_euler_characteristic : SignedInteger
      observed_orientation_computed : Bool
      observed_orientable : Bool
      observed_surface_type : ClosedSurfaceType

  observeSurface : ClassifiedBoundarySurface → SurfaceObservation
  observeSurface currentSurface = surface_observation
    (classified_boundary_kind currentSurface)
    (classified_euler_characteristic currentSurface)
    (classified_orientation_computed currentSurface)
    (classified_is_orientable currentSurface)
    (classified_surface_type currentSurface)

  observeSurfaces : {simplex_count : Nat} →
    Triangulation 3 simplex_count → List SurfaceObservation
  observeSurfaces currentTriangulation =
    map observeSurface (classifiedBoundarySurfaces currentTriangulation)

sphere_classification_from_euler_two :
  classifyClosedSurface true true (signed_positive 1) ≡
    orientable_genus 0
sphere_classification_from_euler_two = refl

torus_classification_from_euler_zero :
  classifyClosedSurface true true signed_zero ≡ orientable_genus 1
torus_classification_from_euler_zero = refl

klein_bottle_classification_from_euler_zero :
  classifyClosedSurface true false signed_zero ≡ nonorientable_genus 2
klein_bottle_classification_from_euler_zero = refl

uncomputed_orientation_stays_unclassified :
  classifyClosedSurface false true signed_zero ≡ unclassified_surface
uncomputed_orientation_stays_unclassified = refl

ball_boundary_is_derived_as_an_orientable_sphere :
  observeSurfaces (ball 3) ≡
    (surface_observation real_boundary_component
      (signed_positive 1) true true (orientable_genus 0) ∷ [])
ball_boundary_is_derived_as_an_orientable_sphere = refl

sphere_has_no_boundary_surface :
  map_outcome observeSurfaces (sphere 3) ≡ accepted []
sphere_has_no_boundary_surface = refl

ball_bundle_boundary_is_derived_as_an_orientable_torus :
  map_outcome observeSurfaces three_dimensional_ball_bundle ≡
    accepted
      (surface_observation real_boundary_component signed_zero
        true true (orientable_genus 1) ∷ [])
ball_bundle_boundary_is_derived_as_an_orientable_torus = refl

figure_eight_ideal_boundary_is_an_orientable_torus :
  map_outcome observeSurfaces figure_eight_knot_complement ≡
    accepted
      (surface_observation ideal_boundary_component signed_zero
        true true (orientable_genus 1) ∷ [])
figure_eight_ideal_boundary_is_an_orientable_torus = refl
