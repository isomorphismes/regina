{-# OPTIONS --safe --without-K #-}
module Regina.NormalVertexTests where

open import Regina.Foundation
open import Regina.Skeleton using (tabulate_vector)
open import Regina.Triangulation
open import Regina.Examples
open import Regina.Integer using (pos; negsuc)
open import Regina.IntegerMatrix
open import Regina.NormalCoordinates3
open import Regina.NormalMatching3
open import Regina.NormalSurface3
open import Regina.NormalVertices3

private
  vertexCount : Nat → NormalCoords → Triangulation 3 1 → Maybe Nat
  vertexCount fuel encodingValue currentTriangulation
    with vertexSurfaces fuel encodingValue currentTriangulation
  ... | nothing = nothing
  ... | just result = just (length (vertex_surface_list result))

  coupledTriangleSystem : MatchingSystem standard 1
  coupledTriangleSystem = matching_system 1 (tabulate 1 7 coefficients)
    where
    coefficients : Fin 1 → Fin 7 → _
    coefficients _ fzero = pos 1
    coefficients _ (fsuc fzero) = negsuc zero
    coefficients _ (fsuc (fsuc remaining)) = pos zero

  hasCoupledRay : Maybe (List (AdmissibleSurface coupledTriangleSystem)) → Bool
  hasCoupledRay nothing = false
  hasCoupledRay (just values) = any isCoupled values
    where
    isCoupled : AdmissibleSurface coupledTriangleSystem → Bool
    isCoupled result = all (λ index → nat_equal
      (lookup_vector (coordinates (admissible_vector result)) index)
      (expected index)) (all_fin 7)
      where
      expected : Fin 7 → Nat
      expected fzero = 1
      expected (fsuc fzero) = 1
      expected (fsuc (fsuc remaining)) = zero

single_tetrahedron_has_seven_standard_vertex_rays : vertexCount 10 standard (ball 3) ≡ just 7
single_tetrahedron_has_seven_standard_vertex_rays = refl

single_tetrahedron_has_three_quad_vertex_rays : vertexCount 10 quadrilateral (ball 3) ≡ just 3
single_tetrahedron_has_three_quad_vertex_rays = refl

single_tetrahedron_has_ten_almost_normal_vertex_rays :
  vertexCount 10 almost_normal (ball 3) ≡ just 10
single_tetrahedron_has_ten_almost_normal_vertex_rays = refl

single_tetrahedron_has_six_quad_octagon_vertex_rays :
  vertexCount 10 quadrilateral_octagon (ball 3) ≡ just 6
single_tetrahedron_has_six_quad_octagon_vertex_rays = refl

matching_couples_two_triangle_coordinates :
  hasCoupledRay (enumerateSystem 20 coupledTriangleSystem) ≡ true
matching_couples_two_triangle_coordinates = refl

exhausted_reduction_cannot_claim_complete_enumeration :
  vertexCount 0 quadrilateral (ball 3) ≡ nothing
exhausted_reduction_cannot_claim_complete_enumeration = refl
