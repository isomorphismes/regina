{-# OPTIONS --safe --without-K #-}
module Regina.NormalSurfaceTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.NormalCoordinates3
open import Regina.NormalMatching3
open import Regina.NormalSurface3
open import Regina.Integer using (Int; pos)

private
  rowCount : {numberOfTetrahedra : Nat} → NormalCoords → Triangulation 3 numberOfTetrahedra → Maybe Nat
  rowCount encodingValue currentTriangulation
    with makeMatchingEquations encodingValue currentTriangulation
  ... | nothing = nothing
  ... | just systemValue = just (matching_row_count systemValue)

  matches : {numberOfTetrahedra : Nat} → (encodingValue : NormalCoords) →
    Triangulation 3 numberOfTetrahedra → List Nat → Maybe Bool
  matches encodingValue currentTriangulation values
    with makeMatchingEquations encodingValue currentTriangulation |
      readSurface encodingValue _ values
  ... | just systemValue | just surfaceValue = just (satisfiesMatching systemValue surfaceValue)
  ... | _ | _ = nothing

  isEmbedded : NormalCoords → Nat → List Nat → Maybe Bool
  isEmbedded encodingValue numberOfTetrahedra values with readSurface encodingValue numberOfTetrahedra values
  ... | nothing = nothing
  ... | just surfaceValue = just (embedded surfaceValue)

  isAdmissible : NormalCoords → Nat → List Nat → Maybe Bool
  isAdmissible encodingValue numberOfTetrahedra values with readSurface encodingValue numberOfTetrahedra values
  ... | nothing = nothing
  ... | just surfaceValue = just (enumerationAdmissible surfaceValue)

  euler : {numberOfTetrahedra : Nat} → (encodingValue : NormalCoords) →
    Triangulation 3 numberOfTetrahedra → List Nat → Maybe Int
  euler encodingValue currentTriangulation values with readSurface encodingValue _ values
  ... | nothing = nothing
  ... | just surfaceValue = eulerCharacteristic currentTriangulation surfaceValue

  cornerLink : List Nat
  cornerLink = 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
  allCorners : List Nat
  allCorners = 1 ∷ 1 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ []

ball_has_no_standard_matching_equations : rowCount standard (ball 3) ≡ just 0
ball_has_no_standard_matching_equations = refl

sphere_has_twelve_standard_equations :
  map_outcome (rowCount standard) (sphere 3) ≡ accepted (just 12)
sphere_has_twelve_standard_equations = refl

sphere_has_six_quad_equations :
  map_outcome (rowCount quadrilateral) (sphere 3) ≡ accepted (just 6)
sphere_has_six_quad_equations = refl

solid_torus_has_three_standard_equations :
  map_outcome (rowCount standard) three_dimensional_ball_bundle ≡ accepted (just 3)
solid_torus_has_three_standard_equations = refl

solid_torus_has_no_internal_edge_equations :
  map_outcome (rowCount quadrilateral) three_dimensional_ball_bundle ≡ accepted (just 0)
solid_torus_has_no_internal_edge_equations = refl

figure_eight_has_two_quad_equations :
  map_outcome (rowCount quadrilateral) figure_eight_knot_complement ≡ accepted (just 2)
figure_eight_has_two_quad_equations = refl

vertex_link_matches_across_sphere_faces :
  map_outcome (λ currentTriangulation → matches standard currentTriangulation
    (cornerLink ++ cornerLink)) (sphere 3) ≡ accepted (just true)
vertex_link_matches_across_sphere_faces = refl

unmatched_vertex_link_is_rejected :
  map_outcome (λ currentTriangulation → matches standard currentTriangulation
    (cornerLink ++ (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []))) (sphere 3) ≡ accepted (just false)
unmatched_vertex_link_is_rejected = refl

two_quad_types_within_one_tetrahedron_are_not_embedded :
  isEmbedded quadrilateral 1 (1 ∷ 1 ∷ 0 ∷ []) ≡ just false
two_quad_types_within_one_tetrahedron_are_not_embedded = refl

multiple_copies_of_one_quad_type_are_embedded :
  isEmbedded quadrilateral 1 (3 ∷ 0 ∷ 0 ∷ []) ≡ just true
multiple_copies_of_one_quad_type_are_embedded = refl

quad_and_octagon_within_one_tetrahedron_conflict :
  isEmbedded quadrilateral_octagon 1 (1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ []) ≡ just false
quad_and_octagon_within_one_tetrahedron_conflict = refl

octagons_within_different_tetrahedra_are_locally_embedded :
  isEmbedded quadrilateral_octagon 2
    (0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ []) ≡ just true
octagons_within_different_tetrahedra_are_locally_embedded = refl

enumeration_applies_the_global_octagon_constraint :
  isAdmissible quadrilateral_octagon 2
    (0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ []) ≡ just false
enumeration_applies_the_global_octagon_constraint = refl

malformed_vector_length_is_rejected : isEmbedded standard 1 (1 ∷ []) ≡ nothing
malformed_vector_length_is_rejected = refl

triangle_disc_euler_characteristic : euler standard (ball 3) cornerLink ≡ just (pos 1)
triangle_disc_euler_characteristic = refl

sphere_vertex_link_euler_characteristic :
  map_outcome (λ currentTriangulation → euler standard currentTriangulation
    (cornerLink ++ cornerLink)) (sphere 3) ≡ accepted (just (pos 2))
sphere_vertex_link_euler_characteristic = refl

solid_torus_vertex_link_is_a_disc :
  map_outcome (λ currentTriangulation → euler standard currentTriangulation allCorners)
    three_dimensional_ball_bundle ≡ accepted (just (pos 1))
solid_torus_vertex_link_is_a_disc = refl

figure_eight_vertex_link_is_a_torus :
  map_outcome (λ currentTriangulation → euler standard currentTriangulation
    (allCorners ++ allCorners)) figure_eight_knot_complement ≡ accepted (just (pos 0))
figure_eight_vertex_link_is_a_torus = refl

quad_only_euler_needs_triangle_reconstruction :
  euler quadrilateral (ball 3) (1 ∷ 0 ∷ 0 ∷ []) ≡ nothing
quad_only_euler_needs_triangle_reconstruction = refl
