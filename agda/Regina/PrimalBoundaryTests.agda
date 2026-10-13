{-# OPTIONS --safe --without-K #-}
module Regina.PrimalBoundaryTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.IntegerMatrix
open import Regina.Integer using (pos; negsuc)
open import Regina.AbelianGroup
open import Regina.PrimalBoundary

private
  boundaryRows : {dimension numberOfSimplices : Nat} →
    Triangulation dimension numberOfSimplices → Nat → Maybe (List (List _))
  boundaryRows currentTriangulation cellDimension with boundaryMap currentTriangulation cellDimension
  ... | nothing = nothing
  ... | just result = just (toRows result)

segment_boundary_has_opposite_endpoint_signs : boundaryRows (ball 1) 1 ≡
  just ((pos 1 ∷ []) ∷ (negsuc zero ∷ []) ∷ [])
segment_boundary_has_opposite_endpoint_signs = refl

ball_homology_zero_is_one_free_component :
  primalHomology 40 (ball 3) 0 ≡ just (abelian_group 1 [])
ball_homology_zero_is_one_free_component = refl

ball_first_homology_is_trivial : primalHomology 60 (ball 3) 1 ≡ just (abelian_group 0 [])
ball_first_homology_is_trivial = refl

ball_second_homology_is_trivial : primalHomology 60 (ball 3) 2 ≡ just (abelian_group 0 [])
ball_second_homology_is_trivial = refl

circle_first_homology_is_one_free_generator :
  map_outcome (λ currentTriangulation → primalHomology 30 currentTriangulation 1)
    (sphere 1) ≡ accepted (just (abelian_group 1 []))
circle_first_homology_is_one_free_generator = refl

two_sphere_second_homology_is_one_free_generator :
  map_outcome (λ currentTriangulation → primalHomology 40 currentTriangulation 2)
    (sphere 2) ≡ accepted (just (abelian_group 1 []))
two_sphere_second_homology_is_one_free_generator = refl

three_sphere_third_homology_is_one_free_generator :
  map_outcome (λ currentTriangulation → primalHomology 60 currentTriangulation 3)
    (sphere 3) ≡ accepted (just (abelian_group 1 []))
three_sphere_third_homology_is_one_free_generator = refl

four_sphere_fourth_homology_is_one_free_generator :
  map_outcome (λ currentTriangulation → primalHomology 60 currentTriangulation 4)
    (sphere 4) ≡ accepted (just (abelian_group 1 []))
four_sphere_fourth_homology_is_one_free_generator = refl

solid_torus_primal_first_homology_is_one_free_generator :
  map_outcome (λ currentTriangulation → primalHomology 60 currentTriangulation 1)
    three_dimensional_ball_bundle ≡ accepted (just (abelian_group 1 []))
solid_torus_primal_first_homology_is_one_free_generator = refl

empty_has_no_components : primalHomology 1 (unpaired_simplices 3 0) 0 ≡
  just (abelian_group 0 [])
empty_has_no_components = refl
