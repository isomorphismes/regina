{-# OPTIONS --safe --without-K #-}
module Regina.HomologyTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.Input
open import Regina.IntegerMatrix
open import Regina.Integer using (pos; negsuc)
open import Regina.AbelianGroup
open import Regina.ChainHomology
open import Regina.DualPresentation3

private
  matrix2 : Matrix 1 1
  matrix2 = matrix (vector_cons (vector_cons (pos 2) empty_vector) empty_vector)

  nontrivialKernelBoundary : Matrix 1 2
  nontrivialKernelBoundary = matrix
    (vector_cons (vector_cons (pos 1) (vector_cons (pos 1) empty_vector)) empty_vector)

  relationInKernel : Matrix 2 1
  relationInKernel = matrix
    (vector_cons (vector_cons (pos 2) empty_vector)
      (vector_cons (vector_cons (negsuc 1) empty_vector) empty_vector))

presentation_retains_two_torsion :
  groupFromPresentation 8 matrix2 ≡ just (abelian_group 0 (2 ∷ []))
presentation_retains_two_torsion = refl

no_relations_gives_free_group :
  groupFromPresentation 1 (zeroMatrix 0 3) ≡ just (abelian_group 3 [])
no_relations_gives_free_group = refl

units_have_no_torsion :
  groupFromPresentation 8 (identityMatrix 2) ≡ just (abelian_group 0 [])
units_have_no_torsion = refl

kernel_basis_is_transformed_before_quotienting :
  chainHomology 20 nontrivialKernelBoundary relationInKernel ≡
    just (abelian_group 0 (2 ∷ []))
kernel_basis_is_transformed_before_quotienting = refl

nonchain_maps_are_rejected :
  chainHomology 20 (identityMatrix 1) matrix2 ≡ nothing
nonchain_maps_are_rejected = refl

empty_chain_is_trivial :
  chainHomology 1 (zeroMatrix 0 0) (zeroMatrix 0 0) ≡ just (abelian_group 0 [])
empty_chain_is_trivial = refl

ball_has_trivial_first_homology :
  firstHomology 20 (ball 3) ≡ just (abelian_group 0 [])
ball_has_trivial_first_homology = refl

sphere_has_trivial_first_homology :
  map_outcome (firstHomology 40) (sphere 3) ≡ accepted (just (abelian_group 0 []))
sphere_has_trivial_first_homology = refl

solid_torus_has_one_free_generator :
  map_outcome (firstHomology 20) three_dimensional_ball_bundle ≡
    accepted (just (abelian_group 1 []))
solid_torus_has_one_free_generator = refl

figure_eight_complement_has_one_free_generator :
  map_outcome (firstHomology 40) figure_eight_knot_complement ≡
    accepted (just (abelian_group 1 []))
figure_eight_complement_has_one_free_generator = refl

projective_plane_times_circle_retains_free_and_torsion_parts :
  map_outcome (firstHomology 60) projective_plane_times_circle ≡
    accepted (just (abelian_group 1 (2 ∷ [])))
projective_plane_times_circle_retains_free_and_torsion_parts = refl

empty_triangulation_first_homology :
  firstHomology 1 (unpaired_simplices 3 0) ≡ just (abelian_group 0 [])
empty_triangulation_first_homology = refl

disconnected_fundamental_group_is_rejected :
  fundamentalGroupPresentation (unpaired_simplices 3 2) ≡ nothing
disconnected_fundamental_group_is_rejected = refl

disconnected_balls_have_trivial_first_homology :
  firstHomology 1 (unpaired_simplices 3 2) ≡ just (abelian_group 0 [])
disconnected_balls_have_trivial_first_homology = refl
