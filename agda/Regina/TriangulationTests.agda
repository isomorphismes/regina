{-# OPTIONS --safe --without-K #-}

-- Executable reduction tests for Regina's facet-gluing translation.
-- Source examples and semantics at e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-09.

module Regina.TriangulationTests where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Input
open import Regina.Examples

private
  variable
    current_dimension number_of_simplices : Nat

  -- Observations contain ordinary data, never functions or proof fields.
  record Both (first_type second_type : Set) : Set where
    constructor both
    field
      first_value : first_type
      second_value : second_type

  data DetachmentView : Set where
    detachment_view : Change → Nat → Maybe Nat → DetachmentView

  data StateView : Set where
    state_view : Nat → List Bool → StateView

  data IsolationView : Set where
    isolation_view : Change → Nat → Bool → Bool → IsolationView

  bind_outcome : {initial_result final_result : Set} →
    Outcome initial_result → (initial_result → Outcome final_result) → Outcome final_result
  bind_outcome (rejected reason) continuation = rejected reason
  bind_outcome (accepted value) continuation = continuation value

  state_after : Outcome (Transition current_dimension number_of_simplices) →
    Outcome (Triangulation current_dimension number_of_simplices)
  state_after = map_outcome resulting_triangulation

  state_after_unjoin : Outcome (UnjoinResult current_dimension number_of_simplices) →
    Outcome (Triangulation current_dimension number_of_simplices)
  state_after_unjoin = map_outcome (λ finished →
    resulting_triangulation (UnjoinResult.unjoin_transition finished))

  neighbor_as_nat : Maybe (Fin number_of_simplices) → Maybe Nat
  neighbor_as_nat nothing = nothing
  neighbor_as_nat (just neighbor) = just (fin_to_nat neighbor)

  observe_detachment : UnjoinResult current_dimension number_of_simplices → DetachmentView
  observe_detachment finished = detachment_view
    (change (UnjoinResult.unjoin_transition finished))
    (unpaired_facet_count (resulting_triangulation (UnjoinResult.unjoin_transition finished)))
    (neighbor_as_nat (UnjoinResult.previous_neighbor finished))

  observe_state : Triangulation current_dimension number_of_simplices → StateView
  observe_state {number_of_simplices = count} current = state_view
    (unpaired_facet_count current)
    (map (simplex_is_locked (raw_state current)) (all_fin count))

  tetrahedron_a tetrahedron_b : Fin 2
  tetrahedron_a = fzero
  tetrahedron_b = fsuc fzero

  label_zero label_one label_two label_three : Fin 4
  label_zero = fzero
  label_one = fsuc fzero
  label_two = fsuc (fsuc fzero)
  label_three = fsuc (fsuc (fsuc fzero))

  facet_a_zero facet_a_one facet_a_three facet_b_zero : Facet 3 2
  facet_a_zero = facet tetrahedron_a label_zero
  facet_a_one = facet tetrahedron_a label_one
  facet_a_three = facet tetrahedron_a label_three
  facet_b_zero = facet tetrahedron_b label_zero

  unpaired_tetrahedra : Triangulation 3 2
  unpaired_tetrahedra = unpaired_simplices 3 2

  paired_once paired_twice : Outcome (Triangulation 3 2)
  paired_once = state_after (join unpaired_tetrahedra facet_a_zero tetrahedron_b identity)
  paired_twice = bind_outcome paired_once (λ current →
    state_after (join current facet_a_one tetrahedron_b identity))

  locked_pair_result : Outcome (Transition 3 2)
  locked_pair_result = bind_outcome paired_once (λ current → lock_facet current facet_a_zero)

  paired_facets_locked locked_second_pair boundary_only_locked locked_boundary_pair :
    Outcome (Triangulation 3 2)
  paired_facets_locked = state_after locked_pair_result
  locked_second_pair = bind_outcome paired_twice (λ current →
    state_after (lock_facet current facet_a_one))
  boundary_only_locked = state_after (lock_facet unpaired_tetrahedra facet_a_three)
  locked_boundary_pair = bind_outcome paired_once (λ current →
    state_after (lock_facet current facet_a_three))

  locked_tetrahedron_once locked_tetrahedron_twice : Outcome (Triangulation 3 2)
  locked_tetrahedron_once = bind_outcome paired_once (λ current →
    state_after (lock_simplex current tetrahedron_a))
  locked_tetrahedron_twice = bind_outcome paired_twice (λ current →
    state_after (lock_simplex current tetrahedron_a))

  detached_forward detached_backward : Outcome (UnjoinResult 3 2)
  detached_forward = bind_outcome paired_once (λ current → unjoin current facet_a_zero)
  detached_backward = bind_outcome paired_once (λ current → unjoin current facet_b_zero)

  observe_pair_locks : Transition 3 2 → Both Change (Both Bool Bool)
  observe_pair_locks finished = both (change finished) (both
    (facet_is_locked (raw_state (resulting_triangulation finished)) facet_a_zero)
    (facet_is_locked (raw_state (resulting_triangulation finished)) facet_b_zero))

  observe_isolation : Transition 3 2 → IsolationView
  observe_isolation finished = isolation_view (change finished)
    (unpaired_facet_count (resulting_triangulation finished))
    (facet_is_locked (raw_state (resulting_triangulation finished)) facet_a_three)
    (simplex_is_locked (raw_state (resulting_triangulation finished)) tetrahedron_a)

  observe_locked_boundary_detachment : UnjoinResult 3 2 → Both DetachmentView Bool
  observe_locked_boundary_detachment finished = both (observe_detachment finished)
    (facet_is_locked
      (raw_state (resulting_triangulation (UnjoinResult.unjoin_transition finished)))
      facet_a_three)

  identity_images : List Nat
  identity_images = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

  first_pair_input : InputGluing
  first_pair_input = input_gluing 0 0 1 identity_images

  perform_input_join : Triangulation 3 2 → InputGluing → Outcome (Transition 3 2)
  perform_input_join current entry = bind_outcome (read_gluing 3 2 entry) (λ decoded →
    join current (GluingSpec.source_facet decoded) (GluingSpec.target_simplex decoded)
      (GluingSpec.gluing_permutation decoded))

  observed_image_table : Triangulation current_dimension number_of_simplices →
    Facet current_dimension number_of_simplices → Maybe (List Nat)
  observed_image_table current queried_facet with adjacency (raw_state current) queried_facet
  ... | nothing = nothing
  ... | just outward = just (image_table (vertex_permutation outward))

  -- This permutation fixes the opposite vertex 0 but changes two actual
  -- face vertices. Checking only the return facet would accept this fixture;
  -- checking the complete inverse must reject it.
  middle_swap_action : Fin 4 → Fin 4
  middle_swap_action fzero = label_zero
  middle_swap_action (fsuc fzero) = label_two
  middle_swap_action (fsuc (fsuc fzero)) = label_one
  middle_swap_action (fsuc (fsuc (fsuc fzero))) = label_three

  middle_swap_round_trip : (vertex_index : Fin 4) →
    middle_swap_action (middle_swap_action vertex_index) ≡ vertex_index
  middle_swap_round_trip fzero = refl
  middle_swap_round_trip (fsuc fzero) = refl
  middle_swap_round_trip (fsuc (fsuc fzero)) = refl
  middle_swap_round_trip (fsuc (fsuc (fsuc fzero))) = refl

  middle_swap : Permutation 4
  middle_swap = permutation middle_swap_action middle_swap_action
    middle_swap_round_trip middle_swap_round_trip

  raw_one_way raw_self_pair raw_identity_pair raw_wrong_inverse raw_asymmetric_locks :
    RawTriangulation 3 2
  raw_one_way = set_adjacency (raw_state unpaired_tetrahedra) facet_a_zero
    (just (gluing tetrahedron_b identity))
  raw_self_pair = set_adjacency (raw_state unpaired_tetrahedra) facet_a_zero
    (just (gluing tetrahedron_a identity))
  raw_identity_pair = set_adjacency raw_one_way facet_b_zero
    (just (gluing tetrahedron_a identity))
  raw_wrong_inverse = set_adjacency raw_one_way facet_b_zero
    (just (gluing tetrahedron_a middle_swap))
  raw_asymmetric_locks = set_facet_lock_raw raw_identity_pair facet_a_zero true

  bundle_crossing_round_trip : Triangulation 3 1 → Maybe (LocalVertex 3 1)
  bundle_crossing_round_trip current with cross_facet current (facet fzero label_zero) label_one
  ... | nothing = nothing
  ... | just crossed = cross_facet current
    (facet (containing_simplex crossed) label_three) (local_number crossed)

-- Original examples: these are boundary-facet counts, not recognition claims.

ball_two_has_three_unpaired_facets : unpaired_facet_count (ball 2) ≡ 3
ball_two_has_three_unpaired_facets = refl

ball_three_has_four_unpaired_facets : unpaired_facet_count (ball 3) ≡ 4
ball_three_has_four_unpaired_facets = refl

ball_four_has_five_unpaired_facets : unpaired_facet_count (ball 4) ≡ 5
ball_four_has_five_unpaired_facets = refl

sphere_two_has_no_unpaired_facets : map_outcome unpaired_facet_count (sphere 2) ≡ accepted 0
sphere_two_has_no_unpaired_facets = refl

sphere_three_has_no_unpaired_facets : map_outcome unpaired_facet_count (sphere 3) ≡ accepted 0
sphere_three_has_no_unpaired_facets = refl

sphere_four_has_no_unpaired_facets : map_outcome unpaired_facet_count (sphere 4) ≡ accepted 0
sphere_four_has_no_unpaired_facets = refl

different_facets_of_same_tetrahedron_can_join :
  map_outcome unpaired_facet_count three_dimensional_ball_bundle ≡ accepted 2
different_facets_of_same_tetrahedron_can_join = refl

ball_bundle_stores_noninvolutive_inverse :
  map_outcome (λ current → observed_image_table current (facet fzero label_three))
    three_dimensional_ball_bundle ≡ accepted (just (1 ∷ 2 ∷ 3 ∷ 0 ∷ []))
ball_bundle_stores_noninvolutive_inverse = refl

four_dimensional_bundle_has_six_unpaired_facets :
  map_outcome unpaired_facet_count four_dimensional_ball_bundle ≡ accepted 6
four_dimensional_bundle_has_six_unpaired_facets = refl

figure_eight_has_no_unpaired_facets :
  map_outcome unpaired_facet_count figure_eight_knot_complement ≡ accepted 0
figure_eight_has_no_unpaired_facets = refl

-- Join failure order, occupied facets, and the two directions of unjoin.

joining_one_facet_to_itself_rejected :
  map_outcome change (join unpaired_tetrahedra facet_a_zero tetrahedron_a identity) ≡
    rejected same_facet_gluing
joining_one_facet_to_itself_rejected = refl

occupied_source_rejected :
  map_outcome change (bind_outcome paired_once (λ current →
    join current facet_a_zero tetrahedron_b identity)) ≡ rejected facet_already_joined
occupied_source_rejected = refl

occupied_destination_rejected :
  map_outcome change (bind_outcome paired_once (λ current →
    perform_input_join current (input_gluing 0 1 1 (1 ∷ 0 ∷ 2 ∷ 3 ∷ [])))) ≡
      rejected facet_already_joined
occupied_destination_rejected = refl

forward_unjoin_clears_both_facets :
  map_outcome observe_detachment detached_forward ≡
    accepted (detachment_view topology_changed 8 (just 1))
forward_unjoin_clears_both_facets = refl

reverse_unjoin_clears_both_facets :
  map_outcome observe_detachment detached_backward ≡
    accepted (detachment_view topology_changed 8 (just 0))
reverse_unjoin_clears_both_facets = refl

repeated_unjoin_is_no_change :
  map_outcome observe_detachment (bind_outcome (state_after_unjoin detached_forward)
    (λ current → unjoin current facet_a_zero)) ≡
      accepted (detachment_view no_change 8 nothing)
repeated_unjoin_is_no_change = refl

locked_boundary_unjoin_preserves_lock_and_is_no_change :
  map_outcome observe_locked_boundary_detachment (bind_outcome boundary_only_locked
    (λ current → unjoin current facet_a_three)) ≡
      accepted (both (detachment_view no_change 8 nothing) true)
locked_boundary_unjoin_preserves_lock_and_is_no_change = refl

locked_source_prevents_join :
  map_outcome change (bind_outcome
    (state_after (lock_facet unpaired_tetrahedra facet_a_zero))
    (λ current → join current facet_a_zero tetrahedron_b identity)) ≡ rejected locked_facet
locked_source_prevents_join = refl

locked_destination_prevents_join :
  map_outcome change (bind_outcome
    (state_after (lock_facet unpaired_tetrahedra facet_b_zero))
    (λ current → join current facet_a_zero tetrahedron_b identity)) ≡ rejected locked_facet
locked_destination_prevents_join = refl

locking_propagates_to_other_facet :
  map_outcome observe_pair_locks locked_pair_result ≡
    accepted (both locks_changed (both true true))
locking_propagates_to_other_facet = refl

unlocking_propagates_from_other_facet :
  map_outcome observe_pair_locks (bind_outcome paired_facets_locked
    (λ current → unlock_facet current facet_b_zero)) ≡
      accepted (both locks_changed (both false false))
unlocking_propagates_from_other_facet = refl

simplex_lock_does_not_prevent_join :
  map_outcome observe_state (state_after (bind_outcome
    (state_after (lock_simplex unpaired_tetrahedra tetrahedron_a))
    (λ current → join current facet_a_zero tetrahedron_b identity))) ≡
      accepted (state_view 6 (true ∷ false ∷ []))
simplex_lock_does_not_prevent_join = refl

simplex_lock_survives_unjoin :
  map_outcome observe_state (state_after_unjoin (bind_outcome locked_tetrahedron_once
    (λ current → unjoin current facet_a_zero))) ≡
      accepted (state_view 8 (true ∷ false ∷ []))
simplex_lock_survives_unjoin = refl

simplex_lock_survives_isolation :
  map_outcome observe_isolation (bind_outcome locked_tetrahedron_twice
    (λ current → isolate current tetrahedron_a)) ≡
      accepted (isolation_view topology_changed 8 false true)
simplex_lock_survives_isolation = refl

isolation_checks_later_locked_facet_before_changing_anything :
  map_outcome change (bind_outcome locked_second_pair
    (λ current → isolate current tetrahedron_a)) ≡ rejected locked_facet
isolation_checks_later_locked_facet_before_changing_anything = refl

boundary_lock_does_not_prevent_isolation :
  map_outcome observe_isolation (bind_outcome locked_boundary_pair
    (λ current → isolate current tetrahedron_a)) ≡
      accepted (isolation_view topology_changed 8 true false)
boundary_lock_does_not_prevent_isolation = refl

-- Input import preserves the first actual error, including gluing errors.

duplicate_gluing_rejected :
  map_outcome unpaired_facet_count (from_input_gluings false 3 2
    (first_pair_input ∷ first_pair_input ∷ [])) ≡ rejected facet_already_joined
duplicate_gluing_rejected = refl

reverse_duplicate_gluing_rejected :
  map_outcome unpaired_facet_count (from_input_gluings false 3 2
    (first_pair_input ∷ input_gluing 1 0 0 identity_images ∷ [])) ≡
      rejected facet_already_joined
reverse_duplicate_gluing_rejected = refl

out_of_range_source_simplex_rejected :
  map_outcome unpaired_facet_count (from_input_gluings false 3 2
    (input_gluing 2 0 1 identity_images ∷ [])) ≡ rejected invalid_simplex_number
out_of_range_source_simplex_rejected = refl

out_of_range_destination_simplex_rejected :
  map_outcome unpaired_facet_count (from_input_gluings false 3 2
    (input_gluing 0 0 2 identity_images ∷ [])) ≡ rejected invalid_simplex_number
out_of_range_destination_simplex_rejected = refl

out_of_range_facet_rejected :
  map_outcome unpaired_facet_count (from_input_gluings false 3 2
    (input_gluing 0 4 1 identity_images ∷ [])) ≡ rejected invalid_facet_number
out_of_range_facet_rejected = refl

nonbijective_input_images_rejected :
  map_outcome unpaired_facet_count (from_input_gluings false 3 2
    (input_gluing 0 0 1 (0 ∷ 0 ∷ 2 ∷ 3 ∷ []) ∷ [])) ≡ rejected invalid_vertex_permutation
nonbijective_input_images_rejected = refl

earlier_self_gluing_error_precedes_later_bad_index :
  map_outcome unpaired_facet_count (from_input_gluings false 3 2
    (input_gluing 0 0 0 identity_images ∷ input_gluing 2 0 1 identity_images ∷ [])) ≡
      rejected same_facet_gluing
earlier_self_gluing_error_precedes_later_bad_index = refl

-- Deliberately malformed raw tables must fail the certificate checker.

one_way_pairing_cannot_be_certified :
  map_outcome unpaired_facet_count (certify raw_one_way) ≡ rejected inconsistent_pairing_table
one_way_pairing_cannot_be_certified = refl

self_pairing_fails_consistency : pairings_pass raw_self_pair ≡ false
self_pairing_fails_consistency = refl

facet_return_without_full_inverse_fails_consistency : pairings_pass raw_wrong_inverse ≡ false
facet_return_without_full_inverse_fails_consistency = refl

asymmetric_facet_locks_fail_consistency : pairings_pass raw_asymmetric_locks ≡ false
asymmetric_facet_locks_fail_consistency = refl

-- Cross only vertices lying in the chosen facet, using the full gluing map.

opposite_vertex_cannot_cross_its_facet :
  map_outcome (λ current → cross_facet current (facet fzero label_zero) label_zero)
    three_dimensional_ball_bundle ≡ accepted nothing
opposite_vertex_cannot_cross_its_facet = refl

face_vertex_crosses_by_noninvolutive_permutation :
  map_outcome (λ current → cross_facet current (facet fzero label_zero) label_one)
    three_dimensional_ball_bundle ≡ accepted (just (local_vertex fzero label_zero))
face_vertex_crosses_by_noninvolutive_permutation = refl

crossing_back_recovers_original_vertex :
  map_outcome bundle_crossing_round_trip three_dimensional_ball_bundle ≡
    accepted (just (local_vertex fzero label_one))
crossing_back_recovers_original_vertex = refl

boundary_facet_has_no_crossing : cross_facet unpaired_tetrahedra facet_a_zero label_one ≡ nothing
boundary_facet_has_no_crossing = refl

isolating_already_unpaired_simplex_is_no_change :
  map_outcome observe_isolation (bind_outcome boundary_only_locked
    (λ current → isolate current tetrahedron_a)) ≡
      accepted (isolation_view no_change 8 true false)
isolating_already_unpaired_simplex_is_no_change = refl

repeating_lock_is_no_change :
  map_outcome change (bind_outcome paired_facets_locked
    (λ current → lock_facet current facet_a_zero)) ≡ accepted no_change
repeating_lock_is_no_change = refl

joined_locked_facet_prevents_unjoin :
  map_outcome observe_detachment (bind_outcome paired_facets_locked
    (λ current → unjoin current facet_a_zero)) ≡ rejected locked_facet
joined_locked_facet_prevents_unjoin = refl

same_simplex_unjoin_clears_both_local_facets :
  map_outcome observe_detachment (bind_outcome three_dimensional_ball_bundle
    (λ current → unjoin current (facet fzero label_zero))) ≡
      accepted (detachment_view topology_changed 4 (just 0))
same_simplex_unjoin_clears_both_local_facets = refl

supported_dimension_guards_checked :
  (supported_dimension false 8 ∷ supported_dimension false 9 ∷
   supported_dimension true 15 ∷ supported_dimension true 16 ∷
   supported_dimension false 0 ∷ supported_dimension true 1 ∷ []) ≡
    (true ∷ false ∷ true ∷ false ∷ false ∷ false ∷ [])
supported_dimension_guards_checked = refl

same_simplex_reverse_unjoin_clears_both_local_facets :
  map_outcome observe_detachment (bind_outcome three_dimensional_ball_bundle
    (λ current → unjoin current (facet fzero label_three))) ≡
      accepted (detachment_view topology_changed 4 (just 0))
same_simplex_reverse_unjoin_clears_both_local_facets = refl

unjoining_first_pair_preserves_unrelated_second_pair :
  map_outcome (λ current → both (unpaired_facet_count current)
    (both (observed_image_table current facet_a_one)
          (observed_image_table current (facet tetrahedron_b label_one))))
    (state_after_unjoin (bind_outcome paired_twice
      (λ current → unjoin current facet_a_zero))) ≡
        accepted (both 6 (both (just identity_images) (just identity_images)))
unjoining_first_pair_preserves_unrelated_second_pair = refl
