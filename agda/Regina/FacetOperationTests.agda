{-# OPTIONS --safe --without-K #-}

-- Facet-frame conversions, face-level joins, and reciprocal locks.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission.
-- Translation changes: 2026-10-12. See ../../LICENSE.txt.

module Regina.FacetOperationTests where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.FaceLinks
open import Regina.FacetOperations3
open import Regina.TriangleTypes3

private
  fourth_vertex : Fin 4
  fourth_vertex = fsuc (fsuc (fsuc fzero))

  cycleImage : Fin 3 → Fin 3
  cycleImage fzero = fsuc fzero
  cycleImage (fsuc fzero) = fsuc (fsuc fzero)
  cycleImage (fsuc (fsuc fzero)) = fzero

  cyclePreimage : Fin 3 → Fin 3
  cyclePreimage fzero = fsuc (fsuc fzero)
  cyclePreimage (fsuc fzero) = fzero
  cyclePreimage (fsuc (fsuc fzero)) = fsuc fzero

  cyclePreimageImage : (currentVertex : Fin 3) →
    cyclePreimage (cycleImage currentVertex) ≡ currentVertex
  cyclePreimageImage fzero = refl
  cyclePreimageImage (fsuc fzero) = refl
  cyclePreimageImage (fsuc (fsuc fzero)) = refl

  cycleImagePreimage : (currentVertex : Fin 3) →
    cycleImage (cyclePreimage currentVertex) ≡ currentVertex
  cycleImagePreimage fzero = refl
  cycleImagePreimage (fsuc fzero) = refl
  cycleImagePreimage (fsuc (fsuc fzero)) = refl

  triangle_cycle : Permutation 3
  triangle_cycle = permutation cycleImage cyclePreimage
    cyclePreimageImage cycleImagePreimage

  stateAfter : {simplex_count : Nat} →
    Outcome (Transition 3 simplex_count) → Outcome (Triangulation 3 simplex_count)
  stateAfter = map_outcome resulting_triangulation

  applyToState : {simplex_count : Nat} {result : Set} →
    (Triangulation 3 simplex_count → Outcome result) →
    Outcome (Triangulation 3 simplex_count) → Outcome result
  applyToState operation (rejected failureReason) = rejected failureReason
  applyToState operation (accepted currentTriangulation) = operation currentTriangulation

  observedMapping : {simplex_count : Nat} → Triangulation 3 simplex_count →
    Facet 3 simplex_count → Maybe (List Nat)
  observedMapping currentTriangulation localFacet
    with adjacency (raw_state currentTriangulation) localFacet
  ... | nothing = nothing
  ... | just outward = just (image_table (vertex_permutation outward))

  observeAllMappings : {simplex_count : Nat} → Triangulation 3 simplex_count →
    Fin simplex_count → List (Maybe (List Nat))
  observeAllMappings currentTriangulation simplexIndex = map
    (λ localVertex → observedMapping currentTriangulation (facet simplexIndex localVertex))
    (all_fin 4)

  lockedFaceZero lockedFaceThree same_tetrahedron_join :
    Outcome (Triangulation 3 1)
  lockedFaceZero = stateAfter (lockFacetFace (ball 3) 0)
  lockedFaceThree = stateAfter (lockFacetFace (ball 3) 3)
  same_tetrahedron_join = stateAfter (joinBoundaryFacets (ball 3) 0 3 identity)

  pairedFaceLocked pairedFaceUnlocked : Outcome (Triangulation 3 1)
  pairedFaceLocked = stateAfter (applyToState
    (λ current → lockFacetFace current 0) same_tetrahedron_join)
  pairedFaceUnlocked = stateAfter (applyToState
    (λ current → unlockFacetFace current 0) pairedFaceLocked)

boundary_face_frames_use_their_own_ordered_vertices :
  map (λ classNumber → map_outcome
    (λ currentFrame → image_table (frame_vertex_mapping currentFrame))
    (facetFrame (ball 3) classNumber)) (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡
  (accepted (1 ∷ 2 ∷ 3 ∷ 0 ∷ []) ∷ accepted (0 ∷ 2 ∷ 3 ∷ 1 ∷ []) ∷
   accepted (0 ∷ 1 ∷ 3 ∷ 2 ∷ []) ∷ accepted (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ∷ [])
boundary_face_frames_use_their_own_ordered_vertices = refl

identity_inherent_gluing_can_be_nonidentity_under_tetrahedron_labels :
  map_outcome (λ current → observeAllMappings current fzero) same_tetrahedron_join ≡
  accepted (just (3 ∷ 0 ∷ 1 ∷ 2 ∷ []) ∷ nothing ∷ nothing ∷
    just (1 ∷ 2 ∷ 3 ∷ 0 ∷ []) ∷ [])
identity_inherent_gluing_can_be_nonidentity_under_tetrahedron_labels = refl

face_level_join_recovers_the_original_ball_bundle :
  map_outcome triangleClassifications same_tetrahedron_join ≡
  accepted (just (mobius_band (fsuc fzero)) ∷ just parachute ∷ just parachute ∷ [])
face_level_join_recovers_the_original_ball_bundle = refl

same_tetrahedron_join_leaves_two_boundary_facets :
  map_outcome unpaired_facet_count same_tetrahedron_join ≡ accepted 2
same_tetrahedron_join_leaves_two_boundary_facets = refl

joined_faces_merge_into_one_global_triangle_class :
  map_outcome (λ current → length (faceLinkClasses current 2))
    same_tetrahedron_join ≡ accepted 3
joined_faces_merge_into_one_global_triangle_class = refl

cycle_gluing_between_distinct_tetrahedra_uses_both_frames :
  map_outcome (λ completed → observedMapping
    (resulting_triangulation completed) (facet fzero fzero))
    (joinBoundaryFacets (unpaired_simplices 3 2) 0 4 triangle_cycle) ≡
  accepted (just (0 ∷ 2 ∷ 3 ∷ 1 ∷ []))
cycle_gluing_between_distinct_tetrahedra_uses_both_frames = refl

cycle_gluing_stores_the_inverse_on_the_other_tetrahedron :
  map_outcome (λ completed → observedMapping
    (resulting_triangulation completed) (facet (fsuc fzero) fzero))
    (joinBoundaryFacets (unpaired_simplices 3 2) 0 4 triangle_cycle) ≡
  accepted (just (0 ∷ 3 ∷ 1 ∷ 2 ∷ []))
cycle_gluing_stores_the_inverse_on_the_other_tetrahedron = refl

boundary_face_lock_is_observable :
  applyToState (λ current → facetFaceIsLocked current 0) lockedFaceZero ≡ accepted true
boundary_face_lock_is_observable = refl

source_facet_lock_blocks_join :
  applyToState (λ current → joinBoundaryFacets current 0 3 identity)
    lockedFaceZero ≡ rejected locked_facet
source_facet_lock_blocks_join = refl

destination_facet_lock_blocks_join :
  applyToState (λ current → joinBoundaryFacets current 0 3 identity)
    lockedFaceThree ≡ rejected locked_facet
destination_facet_lock_blocks_join = refl

locking_a_paired_face_locks_both_tetrahedron_facets :
  map_outcome (λ current →
    facet_is_locked (raw_state current) (facet fzero fzero) ∷
    facet_is_locked (raw_state current) (facet fzero fourth_vertex) ∷ [])
    pairedFaceLocked ≡ accepted (true ∷ true ∷ [])
locking_a_paired_face_locks_both_tetrahedron_facets = refl

unlocking_a_paired_face_clears_both_tetrahedron_locks :
  map_outcome (λ current →
    facet_is_locked (raw_state current) (facet fzero fzero) ∷
    facet_is_locked (raw_state current) (facet fzero fourth_vertex) ∷ [])
    pairedFaceUnlocked ≡ accepted (false ∷ false ∷ [])
unlocking_a_paired_face_clears_both_tetrahedron_locks = refl

repeating_a_face_lock_is_a_noop :
  map_outcome change (applyToState (λ current → lockFacetFace current 0)
    lockedFaceZero) ≡ accepted no_change
repeating_a_face_lock_is_a_noop = refl

unlocking_an_unlocked_face_is_a_noop :
  map_outcome change (unlockFacetFace (ball 3) 0) ≡ accepted no_change
unlocking_an_unlocked_face_is_a_noop = refl

same_boundary_face_cannot_be_joined_to_itself :
  joinBoundaryFacets (ball 3) 0 0 identity ≡ rejected same_facet_gluing
same_boundary_face_cannot_be_joined_to_itself = refl

same_face_error_precedes_the_boundary_lock_error :
  applyToState (λ current → joinBoundaryFacets current 0 0 identity)
    lockedFaceZero ≡ rejected same_facet_gluing
same_face_error_precedes_the_boundary_lock_error = refl

occupied_face_cannot_be_joined_again :
  applyToState (λ current → joinBoundaryFacets current 0 1 identity)
    same_tetrahedron_join ≡ rejected facet_already_joined
occupied_face_cannot_be_joined_again = refl

occupied_face_error_precedes_the_lock_error :
  applyToState (λ current → joinBoundaryFacets current 0 1 identity)
    pairedFaceLocked ≡ rejected facet_already_joined
occupied_face_error_precedes_the_lock_error = refl

an_absent_global_facet_does_not_become_a_default_face :
  joinBoundaryFacets (ball 3) 0 4 identity ≡ rejected invalid_facet_number
an_absent_global_facet_does_not_become_a_default_face = refl

an_absent_lock_query_reports_failure :
  facetFaceIsLocked (ball 3) 4 ≡ rejected invalid_facet_number
an_absent_lock_query_reports_failure = refl

an_absent_lock_update_reports_failure :
  lockFacetFace (ball 3) 4 ≡ rejected invalid_facet_number
an_absent_lock_update_reports_failure = refl

empty_triangulation_has_no_resolvable_facet :
  facetFrame (unpaired_simplices 3 0) 0 ≡ rejected invalid_facet_number
empty_triangulation_has_no_resolvable_facet = refl
