{-# OPTIONS --safe --without-K #-}

-- Reduction tests for Regina's deterministic dual spanning forest.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-09.

module Regina.DualForestTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Input
open import Regina.Examples
open import Regina.DualForest

private
  record EdgeAddress : Set where
    constructor edge_address
    field
      parent_simplex_number : Nat
      parent_facet_number : Nat
      child_simplex_number : Nat
      child_facet_number : Nat

  edgeAddress : {dimension simplex_count : Nat} →
    DualForestEdge dimension simplex_count → EdgeAddress
  edgeAddress currentForestEdge = edge_address
    (fin_to_nat (simplex_number (parent_facet currentForestEdge)))
    (fin_to_nat (opposite_vertex (parent_facet currentForestEdge)))
    (fin_to_nat (simplex_number (child_facet currentForestEdge)))
    (fin_to_nat (opposite_vertex (child_facet currentForestEdge)))

  forestAddresses : {dimension simplex_count : Nat} →
    Triangulation dimension simplex_count → List EdgeAddress
  forestAddresses currentTriangulation =
    map edgeAddress (dualForestEdges currentTriangulation)

  twoJoinedAndOneIsolated : Outcome (Triangulation 3 3)
  twoJoinedAndOneIsolated = from_input_gluings false 3 3
    (input_gluing 0 0 1 (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ∷ [])

one_tetrahedron_has_empty_dual_forest :
  dualForestEdgeCount (ball 3) ≡ 0
one_tetrahedron_has_empty_dual_forest = refl

three_unpaired_tetrahedra_have_empty_dual_forest :
  dualForestEdgeCount (unpaired_simplices 3 3) ≡ 0
three_unpaired_tetrahedra_have_empty_dual_forest = refl

sphere_uses_first_facet_to_discover_second_tetrahedron :
  map_outcome forestAddresses (sphere 3) ≡
    accepted (edge_address 0 0 1 0 ∷ [])
sphere_uses_first_facet_to_discover_second_tetrahedron = refl

figure_eight_uses_first_available_gluing :
  map_outcome forestAddresses figure_eight_knot_complement ≡
    accepted (edge_address 0 0 1 1 ∷ [])
figure_eight_uses_first_available_gluing = refl

four_dimensional_bundle_marks_opposite_facet_four :
  map_outcome forestAddresses four_dimensional_ball_bundle ≡
    accepted (edge_address 0 0 1 4 ∷ [])
four_dimensional_bundle_marks_opposite_facet_four = refl

same_simplex_pairing_is_not_a_forest_edge :
  map_outcome dualForestEdgeCount three_dimensional_ball_bundle ≡ accepted 0
same_simplex_pairing_is_not_a_forest_edge = refl

two_joined_and_one_isolated_have_one_forest_edge :
  map_outcome dualForestEdgeCount twoJoinedAndOneIsolated ≡ accepted 1
two_joined_and_one_isolated_have_one_forest_edge = refl

sphere_root_has_no_parent :
  map_outcome
    (λ currentTriangulation → parentFacetOf currentTriangulation fzero)
    (sphere 3) ≡ accepted nothing
sphere_root_has_no_parent = refl

sphere_second_simplex_parent_is_facet_zero :
  map_outcome
    (λ currentTriangulation →
      parentFacetOf currentTriangulation (fsuc fzero))
    (sphere 3) ≡ accepted (just (facet fzero fzero))
sphere_second_simplex_parent_is_facet_zero = refl

sphere_non_tree_gluing_is_not_marked :
  map_outcome
    (λ currentTriangulation → facetInDualForest currentTriangulation
      (facet fzero (fsuc fzero)))
    (sphere 3) ≡ accepted false
sphere_non_tree_gluing_is_not_marked = refl
