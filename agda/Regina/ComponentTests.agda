{-# OPTIONS --safe --without-K #-}

-- Reduction tests for connected components and orientation propagation.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-09.

module Regina.ComponentTests where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Input
open import Regina.Examples
open import Regina.Components

private
  record ComponentSummary : Set where
    constructor component_summary
    field
      number_of_components : Nat
      simplex_counts : List Nat
      boundary_facet_counts : List Nat
      orientable_components : List Bool
      all_components_orientable : Bool

  componentSummary : {simplexDimension numberOfSimplices : Nat} →
    Triangulation simplexDimension numberOfSimplices → ComponentSummary
  componentSummary current = component_summary
    (componentCount current)
    (componentSizes current)
    (componentBoundaryFacetCounts current)
    (componentOrientabilities current)
    (triangulationOrientable current)

  candidateParity : {numberOfVertices : Nat} →
    Maybe (Permutation numberOfVertices) → Maybe Bool
  candidateParity nothing = nothing
  candidateParity (just mapping) = just (permutationEven mapping)

  identityImages : List Nat
  identityImages = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

  twoJoinedAndOneIsolated : Outcome (Triangulation 3 3)
  twoJoinedAndOneIsolated = from_input_gluings false 3 3
    (input_gluing 0 0 1 identityImages ∷ [])

  -- [1,2,0,3] is an even 3-cycle. Joining facet 0 to facet 1 of the
  -- same tetrahedron therefore forces its propagated orientation to flip
  -- when it returns to the same simplex.
  nonorientableSelfPair : Outcome (Triangulation 3 1)
  nonorientableSelfPair = from_input_gluings false 3 1
    (input_gluing 0 0 0 (1 ∷ 2 ∷ 0 ∷ 3 ∷ []) ∷ [])

identity_permutation_is_even :
  candidateParity (from_image_list 4 identityImages) ≡ just true
identity_permutation_is_even = refl

single_transposition_is_odd :
  candidateParity (from_image_list 4 (1 ∷ 0 ∷ 2 ∷ 3 ∷ [])) ≡ just false
single_transposition_is_odd = refl

three_cycle_is_even :
  candidateParity (from_image_list 4 (1 ∷ 2 ∷ 0 ∷ 3 ∷ [])) ≡ just true
three_cycle_is_even = refl

three_unpaired_tetrahedra_are_three_components :
  componentSummary (unpaired_simplices 3 3) ≡
    component_summary 3 (1 ∷ 1 ∷ 1 ∷ []) (4 ∷ 4 ∷ 4 ∷ [])
      (true ∷ true ∷ true ∷ []) true
three_unpaired_tetrahedra_are_three_components = refl

two_joined_tetrahedra_and_one_isolated :
  map_outcome componentSummary twoJoinedAndOneIsolated ≡
    accepted (component_summary 2 (2 ∷ 1 ∷ []) (6 ∷ 4 ∷ [])
      (true ∷ true ∷ []) true)
two_joined_tetrahedra_and_one_isolated = refl

sphere_three_is_one_closed_orientable_component :
  map_outcome componentSummary (sphere 3) ≡
    accepted (component_summary 1 (2 ∷ []) (0 ∷ []) (true ∷ []) true)
sphere_three_is_one_closed_orientable_component = refl

ball_bundle_is_one_orientable_component_with_two_boundary_facets :
  map_outcome componentSummary three_dimensional_ball_bundle ≡
    accepted (component_summary 1 (1 ∷ []) (2 ∷ []) (true ∷ []) true)
ball_bundle_is_one_orientable_component_with_two_boundary_facets = refl

figure_eight_is_one_orientable_component :
  map_outcome componentSummary figure_eight_knot_complement ≡
    accepted (component_summary 1 (2 ∷ []) (0 ∷ []) (true ∷ []) true)
figure_eight_is_one_orientable_component = refl

even_self_return_detects_nonorientability :
  map_outcome componentSummary nonorientableSelfPair ≡
    accepted (component_summary 1 (1 ∷ []) (2 ∷ []) (false ∷ []) false)
even_self_return_detects_nonorientability = refl
