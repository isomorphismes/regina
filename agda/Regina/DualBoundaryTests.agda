{-# OPTIONS --safe --without-K #-}
module Regina.DualBoundaryTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.AbelianGroup
open import Regina.DualBoundary3
import Regina.PrimalBoundary as Primal

private
  groups : {numberOfSimplices : Nat} → Triangulation 3 numberOfSimplices → List (Maybe AbelianGroup)
  groups currentTriangulation = map (dualHomology 100 currentTriangulation) (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])

ball_has_only_degree_zero_homology : groups (ball 3) ≡
  (just (abelian_group 1 []) ∷ just (abelian_group 0 []) ∷
   just (abelian_group 0 []) ∷ just (abelian_group 0 []) ∷ [])
ball_has_only_degree_zero_homology = refl

sphere_has_degree_zero_and_three_homology : map_outcome groups (sphere 3) ≡ accepted
  (just (abelian_group 1 []) ∷ just (abelian_group 0 []) ∷
   just (abelian_group 0 []) ∷ just (abelian_group 1 []) ∷ [])
sphere_has_degree_zero_and_three_homology = refl

solid_torus_has_degree_zero_and_one_homology : map_outcome groups three_dimensional_ball_bundle ≡ accepted
  (just (abelian_group 1 []) ∷ just (abelian_group 1 []) ∷
   just (abelian_group 0 []) ∷ just (abelian_group 0 []) ∷ [])
solid_torus_has_degree_zero_and_one_homology = refl

figure_eight_uses_the_truncated_dual_complex : map_outcome groups figure_eight_knot_complement ≡ accepted
  (just (abelian_group 1 []) ∷ just (abelian_group 1 []) ∷
   just (abelian_group 0 []) ∷ just (abelian_group 0 []) ∷ [])
figure_eight_uses_the_truncated_dual_complex = refl

projective_plane_times_circle_preserves_two_torsion :
  map_outcome groups projective_plane_times_circle ≡ accepted
  (just (abelian_group 1 []) ∷ just (abelian_group 1 (2 ∷ [])) ∷
   just (abelian_group 0 (2 ∷ [])) ∷ just (abelian_group 0 []) ∷ [])
projective_plane_times_circle_preserves_two_torsion = refl

empty_dual_complex_has_no_homology : groups (unpaired_simplices 3 0) ≡
  (just (abelian_group 0 []) ∷ just (abelian_group 0 []) ∷
   just (abelian_group 0 []) ∷ just (abelian_group 0 []) ∷ [])
empty_dual_complex_has_no_homology = refl

disconnected_components_survive_degree_zero : dualHomology 10 (unpaired_simplices 3 2) 0 ≡
  just (abelian_group 2 [])
disconnected_components_survive_degree_zero = refl

ideal_compactification_is_distinct_from_the_manifold :
  map_outcome (λ currentTriangulation → Primal.primalHomology 100 currentTriangulation 1)
    figure_eight_knot_complement ≡ accepted (just (abelian_group 0 []))
ideal_compactification_is_distinct_from_the_manifold = refl
