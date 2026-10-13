{-# OPTIONS --safe --without-K #-}
module Regina.BoundaryTriangulationTests where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.PermutationExtension
open import Regina.PermutationContraction
open import Regina.Triangulation
open import Regina.Examples
open import Regina.FaceLinks
open import Regina.Components
open import Regina.BoundaryTriangulation3

private
  contractionImages : {degree : Nat} → Permutation (suc degree) → Maybe (List Nat)
  contractionImages original with contractPermutation original
  ... | nothing = nothing
  ... | just result = just (image_table (contracted_permutation result))

  record SurfaceObservation : Set where
    constructor observed_surface
    field
      triangles vertices edges boundary_edges : Nat
      orientable consistent : Bool

  observe : Maybe BuiltRealBoundary3 → Maybe SurfaceObservation
  observe nothing = nothing
  observe (just result) = just (observed_surface
    (boundary_triangle_count result)
    (length (faceLinkClasses surface 0))
    (length (faceLinkClasses surface 1))
    (unpaired_facet_count surface)
    (triangulationOrientable surface)
    (pairings_pass (raw_state surface)))
    where
    surface : Triangulation 2 (boundary_triangle_count result)
    surface = boundary_triangulation result

  observeBoundaries : {count : Nat} → Triangulation 3 count →
    List (Maybe SurfaceObservation)
  observeBoundaries currentTriangulation = map observe
    (buildRealBoundaryComponents currentTriangulation)

identity_contracts_to_three_vertices :
  contractionImages {3} identity ≡ just (0 ∷ 1 ∷ 2 ∷ [])
identity_contracts_to_three_vertices = refl

moving_the_deleted_vertex_is_rejected :
  contractionImages swapLinkDirections ≡ nothing
moving_the_deleted_vertex_is_rejected = refl

extension_and_contraction_round_trip :
  contractionImages (extendPermutation (inverse swapLinkDirections)) ≡
    just (0 ∷ 1 ∷ 3 ∷ 2 ∷ [])
extension_and_contraction_round_trip = refl

zero_degree_contraction : contractionImages {0} identity ≡ just []
zero_degree_contraction = refl

ball_builds_a_closed_four_triangle_sphere :
  observeBoundaries (ball 3) ≡
    (just (observed_surface 4 4 6 0 true true) ∷ [])
ball_builds_a_closed_four_triangle_sphere = refl

sphere_has_no_real_boundary_to_build :
  map_outcome observeBoundaries (sphere 3) ≡ accepted []
sphere_has_no_real_boundary_to_build = refl

ball_bundle_builds_a_closed_two_triangle_torus :
  map_outcome observeBoundaries three_dimensional_ball_bundle ≡
    accepted (just (observed_surface 2 1 3 0 true true) ∷ [])
ball_bundle_builds_a_closed_two_triangle_torus = refl

ideal_cusp_is_not_a_real_boundary :
  map_outcome observeBoundaries figure_eight_knot_complement ≡ accepted []
ideal_cusp_is_not_a_real_boundary = refl

empty_triangulation_has_no_real_boundary :
  observeBoundaries (unpaired_simplices 3 0) ≡ []
empty_triangulation_has_no_real_boundary = refl
