{-# OPTIONS --safe --without-K #-}
module Regina.NormalTriangleReconstructionTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.Skeleton using (concat_map)
open import Regina.NormalCoordinates3
open import Regina.NormalMatching3
open import Regina.NormalTriangleReconstruction3
open import Regina.Integer using (Int; pos)

private
  reconstructed_values : {tetrahedra : Nat} → (encoding : NormalCoords) →
    Triangulation 3 tetrahedra → List Nat → Maybe (List DiscCount)
  reconstructed_values encoding currentTriangulation values with readSurface encoding _ values
  ... | nothing = nothing
  ... | just sourceSurface with reconstruct_triangles currentTriangulation sourceSurface
  ... | nothing = nothing
  ... | just reconstructionResult = just (disc_counts_to_list (reconstructed_coordinates reconstructionResult))

  certifies : {tetrahedra : Nat} → (encoding : NormalCoords) →
    Triangulation 3 tetrahedra → List Nat → Bool
  certifies encoding currentTriangulation values with readSurface encoding _ values
  ... | nothing = false
  ... | just sourceSurface with certify_reconstruction currentTriangulation sourceSurface
  ... | nothing = false
  ... | just reconstructionResult = true

  compact_reconstruction : {tetrahedra : Nat} → (encoding : NormalCoords) →
    Triangulation 3 tetrahedra → List Nat → Bool
  compact_reconstruction encoding currentTriangulation values with readSurface encoding _ values
  ... | nothing = false
  ... | just sourceSurface with reconstruct_triangles currentTriangulation sourceSurface
  ... | nothing = false
  ... | just reconstructionResult with finite_surface reconstructionResult
  ... | nothing = false
  ... | just finiteResult = true

  reduced_euler : {tetrahedra : Nat} → (encoding : NormalCoords) →
    Triangulation 3 tetrahedra → List Nat → Maybe Int
  reduced_euler encoding currentTriangulation values with readSurface encoding _ values
  ... | nothing = nothing
  ... | just sourceSurface = reconstructed_euler_characteristic currentTriangulation sourceSurface

  quad_disc : List Nat
  quad_disc = 1 ∷ 0 ∷ 0 ∷ []
  zero_quads : List Nat
  zero_quads = 0 ∷ 0 ∷ 0 ∷ []
  full_quad_disc : List DiscCount
  full_quad_disc = finite 0 ∷ finite 0 ∷ finite 0 ∷ finite 0 ∷
    finite 1 ∷ finite 0 ∷ finite 0 ∷ []

  small_one_tetrahedron_quads : List (List Nat)
  small_one_tetrahedron_quads =
    (1 ∷ 0 ∷ 0 ∷ []) ∷ (0 ∷ 1 ∷ 0 ∷ []) ∷ (0 ∷ 0 ∷ 1 ∷ []) ∷
    (2 ∷ 0 ∷ 0 ∷ []) ∷ (0 ∷ 2 ∷ 0 ∷ []) ∷ (0 ∷ 0 ∷ 2 ∷ []) ∷ []

  valid_spun_input : Triangulation 3 2 → List Nat → Bool
  valid_spun_input currentTriangulation values with readSurface quadrilateral 2 values |
    makeMatchingEquations quadrilateral currentTriangulation
  ... | just sourceSurface | just matchingEquations = satisfiesMatching matchingEquations sourceSurface and
    embedded sourceSurface and certifies quadrilateral currentTriangulation values and
    not (compact_reconstruction quadrilateral currentTriangulation values)
  ... | _ | _ = false

  finds_spun_surface : Triangulation 3 2 → Bool
  finds_spun_surface currentTriangulation = any (valid_spun_input currentTriangulation)
    (concat_map (λ first → map (λ second → first ++ second) small_one_tetrahedron_quads)
      small_one_tetrahedron_quads)

quad_encoding_gains_four_triangle_coordinates :
  include_triangles quadrilateral ≡ standard
quad_encoding_gains_four_triangle_coordinates = refl

quad_octagon_encoding_gains_four_triangle_coordinates :
  include_triangles quadrilateral_octagon ≡ almost_normal
quad_octagon_encoding_gains_four_triangle_coordinates = refl

unpaired_quad_disc_needs_no_triangles :
  reconstructed_values quadrilateral (ball 3) quad_disc ≡ just full_quad_disc
unpaired_quad_disc_needs_no_triangles = refl

reconstructed_quad_disc_has_euler_characteristic_one :
  reduced_euler quadrilateral (ball 3) quad_disc ≡ just (pos 1)
reconstructed_quad_disc_has_euler_characteristic_one = refl

unpaired_octagon_disc_needs_no_triangles :
  reconstructed_values quadrilateral_octagon (ball 3)
    (0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ []) ≡ just
    (finite 0 ∷ finite 0 ∷ finite 0 ∷ finite 0 ∷ finite 0 ∷ finite 0 ∷ finite 0 ∷
     finite 1 ∷ finite 0 ∷ finite 0 ∷ [])
unpaired_octagon_disc_needs_no_triangles = refl

reconstructed_octagon_disc_has_euler_characteristic_one :
  reduced_euler quadrilateral_octagon (ball 3)
    (0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ []) ≡ just (pos 1)
reconstructed_octagon_disc_has_euler_characteristic_one = refl

existing_triangle_coordinates_are_not_normalised_away :
  reconstructed_values standard (ball 3) (3 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []) ≡ just
    (finite 3 ∷ finite 0 ∷ finite 0 ∷ finite 0 ∷ finite 0 ∷ finite 0 ∷ finite 0 ∷ [])
existing_triangle_coordinates_are_not_normalised_away = refl

paired_sphere_quads_have_finite_matching_triangles :
  map_outcome (λ currentTriangulation → reconstructed_values quadrilateral
    currentTriangulation (quad_disc ++ quad_disc)) (sphere 3) ≡
    accepted (just (full_quad_disc ++ full_quad_disc))
paired_sphere_quads_have_finite_matching_triangles = refl

paired_sphere_reconstruction_is_certified :
  map_outcome (λ currentTriangulation → certifies quadrilateral currentTriangulation
    (quad_disc ++ quad_disc)) (sphere 3) ≡ accepted true
paired_sphere_reconstruction_is_certified = refl

solid_torus_quad_needs_two_triangles :
  map_outcome (λ currentTriangulation → reconstructed_values quadrilateral
    currentTriangulation quad_disc) three_dimensional_ball_bundle ≡ accepted (just
    (finite 1 ∷ finite 0 ∷ finite 0 ∷ finite 1 ∷ finite 1 ∷ finite 0 ∷ finite 0 ∷ []))
solid_torus_quad_needs_two_triangles = refl

solid_torus_reconstruction_is_certified :
  map_outcome (λ currentTriangulation → certifies quadrilateral currentTriangulation
    quad_disc) three_dimensional_ball_bundle ≡ accepted true
solid_torus_reconstruction_is_certified = refl

doubling_quad_counts_doubles_the_minimal_triangles :
  map_outcome (λ currentTriangulation → reconstructed_values quadrilateral
    currentTriangulation (2 ∷ 0 ∷ 0 ∷ [])) three_dimensional_ball_bundle ≡ accepted (just
    (finite 2 ∷ finite 0 ∷ finite 0 ∷ finite 2 ∷ finite 2 ∷ finite 0 ∷ finite 0 ∷ []))
doubling_quad_counts_doubles_the_minimal_triangles = refl

conflicting_triangle_cycles_are_not_zero_filled :
  map_outcome (λ currentTriangulation → reconstructed_values quadrilateral
    currentTriangulation (quad_disc ++ zero_quads)) (sphere 3) ≡ accepted (just
    (infinite ∷ infinite ∷ infinite ∷ infinite ∷ finite 1 ∷ finite 0 ∷ finite 0 ∷
     infinite ∷ infinite ∷ infinite ∷ infinite ∷ finite 0 ∷ finite 0 ∷ finite 0 ∷ []))
conflicting_triangle_cycles_are_not_zero_filled = refl

infinite_triangle_coordinates_cannot_become_a_finite_surface :
  map_outcome (λ currentTriangulation → compact_reconstruction quadrilateral
    currentTriangulation (quad_disc ++ zero_quads)) (sphere 3) ≡ accepted false
infinite_triangle_coordinates_cannot_become_a_finite_surface = refl

infinite_triangle_coordinates_have_no_finite_euler_result :
  map_outcome (λ currentTriangulation → reduced_euler quadrilateral
    currentTriangulation (quad_disc ++ zero_quads)) (sphere 3) ≡ accepted nothing
infinite_triangle_coordinates_have_no_finite_euler_result = refl

already_full_but_nonmatching_coordinates_fail_certification :
  map_outcome (λ currentTriangulation → certifies standard currentTriangulation
    (1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []))
    (sphere 3) ≡ accepted false
already_full_but_nonmatching_coordinates_fail_certification = refl

empty_triangulation_has_an_empty_reconstruction :
  reconstructed_values quadrilateral (unpaired_simplices 3 0) [] ≡ just []
empty_triangulation_has_an_empty_reconstruction = refl

malformed_reduced_coordinate_count_is_rejected :
  reconstructed_values quadrilateral (ball 3) (1 ∷ []) ≡ nothing
malformed_reduced_coordinate_count_is_rejected = refl

matching_embedded_figure_eight_quads_can_be_spun :
  map_outcome finds_spun_surface figure_eight_knot_complement ≡ accepted true
matching_embedded_figure_eight_quads_can_be_spun = refl

zero_quad_input_does_not_add_a_vertex_link :
  map_outcome (λ currentTriangulation → reconstructed_values quadrilateral
    currentTriangulation (zero_quads ++ zero_quads)) figure_eight_knot_complement ≡
    accepted (just (map finite (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷
                               0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])))
zero_quad_input_does_not_add_a_vertex_link = refl
