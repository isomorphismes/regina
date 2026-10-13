{-# OPTIONS --safe --without-K #-}

-- Triangle-classification checks against Regina's documented quotient types.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission.
-- Translation changes: 2026-10-12. See ../../LICENSE.txt.

module Regina.TriangleTypeTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Input
open import Regina.Examples
open import Regina.TriangleTypes3

private
  position_zero position_one position_two : Fin 3
  position_zero = fzero
  position_one = fsuc fzero
  position_two = fsuc (fsuc fzero)

  separate_classes identified_classes : ThreeEntries Nat
  separate_classes = three_entries 0 1 2
  identified_classes = three_entries 0 0 0

  even_mappings : ThreeEntries Bool
  even_mappings = three_entries true true true

  classify : ThreeEntries Nat → ThreeEntries Nat → ThreeEntries Bool →
    TriangleClassification
  classify vertices edges signs = classifyTriangleIncidence
    (triangle_incidence vertices edges signs)

  classificationResolved : Maybe TriangleClassification → Bool
  classificationResolved nothing = false
  classificationResolved (just _) = true

  reversed_edge_pair : Outcome (Triangulation 3 1)
  reversed_edge_pair = from_input_gluings false 3 1
    (input_gluing 0 0 0 (1 ∷ 0 ∷ 3 ∷ 2 ∷ []) ∷ [])

no_identifications_is_an_ordinary_triangle :
  classify separate_classes separate_classes even_mappings ≡ ordinary_triangle
no_identifications_is_an_ordinary_triangle = refl

scarf_special_vertex_is_opposite_the_identified_corners :
  (classify (three_entries 0 1 1) separate_classes even_mappings ∷
   classify (three_entries 1 0 1) separate_classes even_mappings ∷
   classify (three_entries 1 1 0) separate_classes even_mappings ∷ []) ≡
  (scarf position_zero ∷ scarf position_one ∷ scarf position_two ∷ [])
scarf_special_vertex_is_opposite_the_identified_corners = refl

all_corners_and_no_edges_identified_is_a_parachute :
  classify identified_classes separate_classes even_mappings ≡ parachute
all_corners_and_no_edges_identified_is_a_parachute = refl

all_edges_having_equal_signs_is_the_lens_space_spine :
  (classify identified_classes identified_classes even_mappings ∷
   classify identified_classes identified_classes
     (three_entries false false false) ∷ []) ≡
  (lens_space_three_one_spine ∷ lens_space_three_one_spine ∷ [])
all_edges_having_equal_signs_is_the_lens_space_spine = refl

dunce_hat_subtype_tracks_the_exceptional_edge_sign :
  (classify identified_classes identified_classes (three_entries true false false) ∷
   classify identified_classes identified_classes (three_entries false true true) ∷
   classify identified_classes identified_classes (three_entries false true false) ∷
   classify identified_classes identified_classes (three_entries true false true) ∷
   classify identified_classes identified_classes (three_entries false false true) ∷
   classify identified_classes identified_classes (three_entries true true false) ∷ []) ≡
  (dunce_hat position_zero ∷ dunce_hat position_zero ∷
   dunce_hat position_one ∷ dunce_hat position_one ∷
   dunce_hat position_two ∷ dunce_hat position_two ∷ [])
dunce_hat_subtype_tracks_the_exceptional_edge_sign = refl

equal_signs_on_two_identified_edges_give_a_mobius_band :
  (classify (three_entries 0 0 1) (three_entries 0 1 1) even_mappings ∷
   classify (three_entries 0 0 1) (three_entries 1 0 1) even_mappings ∷
   classify (three_entries 0 0 1) (three_entries 1 1 0) even_mappings ∷ []) ≡
  (mobius_band position_zero ∷ mobius_band position_one ∷ mobius_band position_two ∷ [])
equal_signs_on_two_identified_edges_give_a_mobius_band = refl

opposite_signs_and_a_separate_apex_give_a_cone :
  (classify (three_entries 0 1 1) (three_entries 0 1 1) (three_entries true true false) ∷
   classify (three_entries 1 0 1) (three_entries 1 0 1) (three_entries false true true) ∷
   classify (three_entries 1 1 0) (three_entries 1 1 0) (three_entries true false true) ∷ []) ≡
  (cone position_zero ∷ cone position_one ∷ cone position_two ∷ [])
opposite_signs_and_a_separate_apex_give_a_cone = refl

identifying_the_cone_apex_at_its_base_gives_a_horn :
  (classify identified_classes (three_entries 0 1 1) (three_entries true true false) ∷
   classify identified_classes (three_entries 1 0 1) (three_entries false true true) ∷
   classify identified_classes (three_entries 1 1 0) (three_entries true false true) ∷ []) ≡
  (horn position_zero ∷ horn position_one ∷ horn position_two ∷ [])
identifying_the_cone_apex_at_its_base_gives_a_horn = refl

dunce_hat_forms_both_a_mobius_band_and_a_cone :
  formsMobiusBand (dunce_hat position_one) and
  formsCone (dunce_hat position_one) ≡ true
dunce_hat_forms_both_a_mobius_band_and_a_cone = refl

regina_mobius_predicate_includes_exactly_three_types :
  map formsMobiusBand
    (ordinary_triangle ∷ scarf position_zero ∷ parachute ∷ cone position_zero ∷
     mobius_band position_zero ∷ horn position_zero ∷ dunce_hat position_zero ∷
     lens_space_three_one_spine ∷ []) ≡
  (false ∷ false ∷ false ∷ false ∷ true ∷ false ∷ true ∷ true ∷ [])
regina_mobius_predicate_includes_exactly_three_types = refl

regina_cone_predicate_includes_exactly_three_types :
  map formsCone
    (ordinary_triangle ∷ scarf position_zero ∷ parachute ∷ cone position_zero ∷
     mobius_band position_zero ∷ horn position_zero ∷ dunce_hat position_zero ∷
     lens_space_three_one_spine ∷ []) ≡
  (false ∷ false ∷ false ∷ true ∷ false ∷ true ∷ true ∷ false ∷ [])
regina_cone_predicate_includes_exactly_three_types = refl

type_codes_preserve_reginas_enumeration :
  map triangleTypeCode
    (ordinary_triangle ∷ scarf position_zero ∷ parachute ∷ cone position_zero ∷
     mobius_band position_zero ∷ horn position_zero ∷ dunce_hat position_zero ∷
     lens_space_three_one_spine ∷ []) ≡
  (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ [])
type_codes_preserve_reginas_enumeration = refl

subtypes_preserve_the_special_role_and_absent_sentinel :
  map triangleSubtype
    (ordinary_triangle ∷ scarf position_zero ∷ parachute ∷ cone position_one ∷
     mobius_band position_two ∷ horn position_one ∷ dunce_hat position_two ∷
     lens_space_three_one_spine ∷ []) ≡
  (nothing ∷ just position_zero ∷ nothing ∷ just position_one ∷
   just position_two ∷ just position_one ∷ just position_two ∷ nothing ∷ [])
subtypes_preserve_the_special_role_and_absent_sentinel = refl

ball_triangles_have_no_identifications :
  triangleClassifications (ball 3) ≡
  (just ordinary_triangle ∷ just ordinary_triangle ∷
   just ordinary_triangle ∷ just ordinary_triangle ∷ [])
ball_triangles_have_no_identifications = refl

sphere_triangles_have_no_identifications :
  map_outcome triangleClassifications (sphere 3) ≡ accepted
  (just ordinary_triangle ∷ just ordinary_triangle ∷
   just ordinary_triangle ∷ just ordinary_triangle ∷ [])
sphere_triangles_have_no_identifications = refl

absent_triangle_does_not_receive_a_default_type :
  triangleClassification (ball 3) 4 ≡ nothing
absent_triangle_does_not_receive_a_default_type = refl

empty_triangulation_has_no_triangle_types :
  triangleClassifications (unpaired_simplices 3 0) ≡ []
empty_triangulation_has_no_triangle_types = refl

ball_bundle_triangle_incidence_and_signs_resolve :
  map_outcome (λ current → all classificationResolved
    (triangleClassifications current)) three_dimensional_ball_bundle ≡ accepted true
ball_bundle_triangle_incidence_and_signs_resolve = refl

figure_eight_triangle_incidence_and_signs_resolve :
  map_outcome (λ current → all classificationResolved
    (triangleClassifications current)) figure_eight_knot_complement ≡ accepted true
figure_eight_triangle_incidence_and_signs_resolve = refl

ball_bundle_has_a_mobius_triangle_and_two_parachutes :
  map_outcome triangleClassifications three_dimensional_ball_bundle ≡ accepted
    (just (mobius_band position_one) ∷ just parachute ∷ just parachute ∷ [])
ball_bundle_has_a_mobius_triangle_and_two_parachutes = refl

figure_eight_triangles_are_horns_having_distinct_special_edges :
  map_outcome triangleClassifications figure_eight_knot_complement ≡ accepted
    (just (horn position_two) ∷ just (horn position_one) ∷
     just (horn position_zero) ∷ just (horn position_one) ∷ [])
figure_eight_triangles_are_horns_having_distinct_special_edges = refl

reversed_edge_blocks_recognition_of_incident_triangles :
  map_outcome (λ current → all classificationResolved
    (triangleClassifications current)) reversed_edge_pair ≡ accepted false
reversed_edge_blocks_recognition_of_incident_triangles = refl
