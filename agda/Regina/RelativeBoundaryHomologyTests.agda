{-# OPTIONS --safe --without-K #-}

-- Reduction tests for Regina's relative and boundary first homology.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-18.

module Regina.RelativeBoundaryHomologyTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Input
open import Regina.Examples
open import Regina.AbelianGroup
open import Regina.BoundaryHomology3
open import Regina.RelativeHomology3
import Regina.BoundaryClassification3 as Classification

private
  reversedEdgePair : Outcome (Triangulation 3 1)
  reversedEdgePair = from_input_gluings false 3 1
    (input_gluing 0 0 0 (1 ∷ 0 ∷ 3 ∷ 2 ∷ []) ∷ [])

orientable_genus_two_has_four_free_boundary_generators :
  homologyOfClosedSurface (Classification.orientable_genus 2) ≡
    just (abelian_group 4 [])
orientable_genus_two_has_four_free_boundary_generators = refl

nonorientable_genus_two_has_one_free_and_one_two_torsion_generator :
  homologyOfClosedSurface (Classification.nonorientable_genus 2) ≡
    just (abelian_group 1 (2 ∷ []))
nonorientable_genus_two_has_one_free_and_one_two_torsion_generator = refl

unclassified_surface_blocks_boundary_homology :
  homologyOfClosedSurface Classification.unclassified_surface ≡ nothing
unclassified_surface_blocks_boundary_homology = refl

ball_boundary_sphere_has_trivial_first_homology :
  boundaryFirstHomology (ball 3) ≡ just (abelian_group 0 [])
ball_boundary_sphere_has_trivial_first_homology = refl

closed_sphere_has_empty_boundary_homology :
  map_outcome boundaryFirstHomology (sphere 3) ≡
    accepted (just (abelian_group 0 []))
closed_sphere_has_empty_boundary_homology = refl

solid_torus_boundary_has_two_free_generators :
  map_outcome boundaryFirstHomology three_dimensional_ball_bundle ≡
    accepted (just (abelian_group 2 []))
solid_torus_boundary_has_two_free_generators = refl

figure_eight_cusp_has_two_free_boundary_generators :
  map_outcome boundaryFirstHomology figure_eight_knot_complement ≡
    accepted (just (abelian_group 2 []))
figure_eight_cusp_has_two_free_boundary_generators = refl

invalid_triangulation_has_no_boundary_homology_result :
  map_outcome boundaryFirstHomology reversedEdgePair ≡ accepted nothing
invalid_triangulation_has_no_boundary_homology_result = refl

ball_relative_first_homology_is_trivial :
  relativeFirstHomology 20 (ball 3) ≡ just (abelian_group 0 [])
ball_relative_first_homology_is_trivial = refl

sphere_relative_first_homology_uses_closed_shortcut :
  map_outcome (relativeFirstHomology 40) (sphere 3) ≡
    accepted (just (abelian_group 0 []))
sphere_relative_first_homology_uses_closed_shortcut = refl

solid_torus_relative_first_homology_is_trivial :
  map_outcome (relativeFirstHomology 40) three_dimensional_ball_bundle ≡
    accepted (just (abelian_group 0 []))
solid_torus_relative_first_homology_is_trivial = refl

figure_eight_relative_first_homology_is_trivial :
  map_outcome (relativeFirstHomology 80) figure_eight_knot_complement ≡
    accepted (just (abelian_group 0 []))
figure_eight_relative_first_homology_is_trivial = refl

closed_projective_plane_times_circle_keeps_absolute_group :
  map_outcome (relativeFirstHomology 60) projective_plane_times_circle ≡
    accepted (just (abelian_group 1 (2 ∷ [])))
closed_projective_plane_times_circle_keeps_absolute_group = refl

invalid_triangulation_has_no_relative_homology_result :
  map_outcome (relativeFirstHomology 20) reversedEdgePair ≡ accepted nothing
invalid_triangulation_has_no_relative_homology_result = refl

empty_relative_first_homology_is_trivial :
  relativeFirstHomology 1 (unpaired_simplices 3 0) ≡
    just (abelian_group 0 [])
empty_relative_first_homology_is_trivial = refl

ball_second_homology_mod_two_is_trivial :
  secondHomologyModTwoRank 20 (ball 3) ≡ just 0
ball_second_homology_mod_two_is_trivial = refl

sphere_second_homology_mod_two_is_trivial :
  map_outcome (secondHomologyModTwoRank 40) (sphere 3) ≡ accepted (just 0)
sphere_second_homology_mod_two_is_trivial = refl

solid_torus_second_homology_mod_two_is_trivial :
  map_outcome (secondHomologyModTwoRank 40) three_dimensional_ball_bundle ≡
    accepted (just 0)
solid_torus_second_homology_mod_two_is_trivial = refl

figure_eight_second_homology_mod_two_is_trivial :
  map_outcome (secondHomologyModTwoRank 80) figure_eight_knot_complement ≡
    accepted (just 0)
figure_eight_second_homology_mod_two_is_trivial = refl

projective_plane_times_circle_has_two_mod_two_two_cycles :
  map_outcome (secondHomologyModTwoRank 60) projective_plane_times_circle ≡
    accepted (just 2)
projective_plane_times_circle_has_two_mod_two_two_cycles = refl
