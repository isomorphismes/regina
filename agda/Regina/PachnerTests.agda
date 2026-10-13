{-# OPTIONS --safe --without-K #-}
module Regina.PachnerTests where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton using (LocalFace; local_face; tabulate_vector;
  face_class_count; count_matching; less_than)
open import Regina.Examples
open import Regina.PachnerRegion3
open import Agda.Builtin.Nat using (_-_)
import Regina.PachnerMoves3 as Moves
import Regina.Components as Components

private
  move_size : Maybe Moves.PachnerResult → Maybe Nat
  move_size nothing = nothing
  move_size (just resultValue) = just (Moves.resulting_tetrahedron_count resultValue)

  move_boundaries : Maybe Moves.PachnerResult → Maybe Nat
  move_boundaries nothing = nothing
  move_boundaries (just resultValue) = just
    (unpaired_facet_count (Moves.resulting_triangulation resultValue))

  move_faces : Maybe Moves.PachnerResult → Maybe (List Nat)
  move_faces nothing = nothing
  move_faces (just resultValue) = just
    (face_class_count (Moves.resulting_triangulation resultValue) 0 ∷
     face_class_count (Moves.resulting_triangulation resultValue) 1 ∷
     face_class_count (Moves.resulting_triangulation resultValue) 2 ∷
     Moves.resulting_tetrahedron_count resultValue ∷ [])

  inverse_move : Nat → Maybe Moves.PachnerResult → Maybe Moves.PachnerResult
  inverse_move requestedDimension nothing = nothing
  inverse_move requestedDimension (just resultValue) with fin_from_nat
    (Moves.resulting_tetrahedron_count resultValue)
    (Moves.resulting_tetrahedron_count resultValue - 1)
  ... | nothing = nothing
  ... | just lastTetrahedron = Moves.perform_pachner_move
      (Moves.resulting_triangulation resultValue)
      (local_face lastTetrahedron (tabulate_vector 4
        (λ vertexNumber → less_than (fin_to_nat vertexNumber) (suc requestedDimension))))

  pairing_table : {tetrahedra : Nat} → Triangulation 3 tetrahedra → List (Maybe (List Nat))
  pairing_table {tetrahedra} currentTriangulation = map entry (all_facets 3 tetrahedra)
    where
    entry : Facet 3 tetrahedra → Maybe (List Nat)
    entry currentFacet with adjacency (raw_state currentTriangulation) currentFacet
    ... | nothing = nothing
    ... | just outward = just
        (fin_to_nat (adjacent_simplex outward) ∷ image_table (vertex_permutation outward))

  move_table : Maybe Moves.PachnerResult → Maybe (List (Maybe (List Nat)))
  move_table nothing = nothing
  move_table (just resultValue) = just (pairing_table (Moves.resulting_triangulation resultValue))

  move_facet_locks : Maybe Moves.PachnerResult → Maybe Nat
  move_facet_locks nothing = nothing
  move_facet_locks (just resultValue) = just (count_matching
    (facet_is_locked (raw_state (Moves.resulting_triangulation resultValue)))
    (all_facets 3 (Moves.resulting_tetrahedron_count resultValue)))

  central_vertex : {tetrahedra : Nat} → Fin tetrahedra → LocalFace 3 tetrahedra
  central_vertex tetrahedronIndex = local_face tetrahedronIndex
    (tabulate_vector 4 (λ vertexNumber → fin_equal vertexNumber fzero))

  ball_refined : Maybe Moves.PachnerResult
  ball_refined = Moves.subdivide_tetrahedron (ball 3) fzero

  two_tetrahedron_ball : Outcome (Triangulation 3 2)
  two_tetrahedron_ball = from_gluings 3 2
    (glue (facet fzero fzero) (fsuc fzero) identity ∷ [])

  triangle_move : Triangulation 3 2 → Maybe Moves.PachnerResult
  triangle_move currentTriangulation = Moves.perform_pachner_move currentTriangulation
    (local_face fzero (tabulate_vector 4 (λ vertexNumber → not (fin_equal vertexNumber fzero))))

  refine_locked_simplex : Outcome (Transition 3 1) → Maybe Moves.PachnerResult
  refine_locked_simplex (rejected _) = nothing
  refine_locked_simplex (accepted transitionValue) = Moves.subdivide_tetrahedron
    (resulting_triangulation transitionValue) fzero

  lock_internal_then_collapse : Maybe Moves.PachnerResult → Bool
  lock_internal_then_collapse nothing = false
  lock_internal_then_collapse (just resultValue) with fin_from_nat
    (Moves.resulting_tetrahedron_count resultValue) 3
  ... | nothing = false
  ... | just lastTetrahedron with lock_facet (Moves.resulting_triangulation resultValue)
      (facet lastTetrahedron (fsuc fzero))
  ... | rejected _ = false
  ... | accepted transitionValue with Moves.perform_pachner_move
      (resulting_triangulation transitionValue) (central_vertex lastTetrahedron)
  ... | nothing = true
  ... | just _ = false

one_four_adds_three_tetrahedra : move_size ball_refined ≡ just 4
one_four_adds_three_tetrahedra = refl

one_four_keeps_four_boundary_facets : move_boundaries ball_refined ≡ just 4
one_four_keeps_four_boundary_facets = refl

one_four_has_the_subdivided_ball_face_counts :
  move_faces ball_refined ≡ just (5 ∷ 10 ∷ 10 ∷ 4 ∷ [])
one_four_has_the_subdivided_ball_face_counts = refl

four_one_removes_the_new_central_vertex :
  move_size (inverse_move 0 ball_refined) ≡ just 1
four_one_removes_the_new_central_vertex = refl

four_one_recovers_the_original_ball_pairings :
  move_table (inverse_move 0 ball_refined) ≡ just (pairing_table (ball 3))
four_one_recovers_the_original_ball_pairings = refl

two_three_adds_one_tetrahedron :
  map_outcome (λ currentTriangulation → move_size (triangle_move currentTriangulation))
    two_tetrahedron_ball ≡ accepted (just 3)
two_three_adds_one_tetrahedron = refl

two_three_keeps_six_boundary_triangles :
  map_outcome (λ currentTriangulation → move_boundaries (triangle_move currentTriangulation))
    two_tetrahedron_ball ≡ accepted (just 6)
two_three_keeps_six_boundary_triangles = refl

two_three_has_the_correct_new_internal_edge :
  map_outcome (λ currentTriangulation → move_faces (triangle_move currentTriangulation))
    two_tetrahedron_ball ≡ accepted (just (5 ∷ 10 ∷ 9 ∷ 3 ∷ []))
two_three_has_the_correct_new_internal_edge = refl

three_two_removes_the_new_edge :
  map_outcome (λ currentTriangulation → move_size (inverse_move 1
    (triangle_move currentTriangulation))) two_tetrahedron_ball ≡ accepted (just 2)
three_two_removes_the_new_edge = refl

three_two_recovers_ball_face_counts :
  map_outcome (λ currentTriangulation → move_faces (inverse_move 1
    (triangle_move currentTriangulation))) two_tetrahedron_ball ≡
    accepted (just (5 ∷ 9 ∷ 7 ∷ 2 ∷ []))
three_two_recovers_ball_face_counts = refl

boundary_edge_cannot_support_a_three_two_move :
  move_size (Moves.perform_pachner_move (ball 3) (local_face fzero
    (tabulate_vector 4 (λ vertexNumber → less_than (fin_to_nat vertexNumber) 2)))) ≡ nothing
boundary_edge_cannot_support_a_three_two_move = refl

boundary_vertex_cannot_support_a_four_one_move :
  move_size (Moves.perform_pachner_move (ball 3) (central_vertex fzero)) ≡ nothing
boundary_vertex_cannot_support_a_four_one_move = refl

empty_face_is_rejected : move_size (Moves.perform_pachner_move (ball 3)
  (local_face fzero (tabulate_vector 4 (λ _ → false)))) ≡ nothing
empty_face_is_rejected = refl

locked_tetrahedron_cannot_be_subdivided :
  move_size (refine_locked_simplex (lock_simplex (ball 3) fzero)) ≡ nothing
locked_tetrahedron_cannot_be_subdivided = refl

exterior_facet_lock_is_transferred_to_one_new_facet :
  move_facet_locks (refine_locked_simplex (lock_facet (ball 3) (facet fzero fzero))) ≡ just 1
exterior_facet_lock_is_transferred_to_one_new_facet = refl

locked_internal_facet_blocks_the_inverse_move :
  lock_internal_then_collapse ball_refined ≡ true
locked_internal_facet_blocks_the_inverse_move = refl

self_glued_solid_torus_keeps_its_boundary_facets :
  map_outcome (λ currentTriangulation → move_boundaries
    (Moves.subdivide_tetrahedron currentTriangulation fzero))
    three_dimensional_ball_bundle ≡ accepted (just 2)
self_glued_solid_torus_keeps_its_boundary_facets = refl

self_glued_solid_torus_round_trip_keeps_actual_pairings :
  map_outcome (λ currentTriangulation → move_table (inverse_move 0
    (Moves.subdivide_tetrahedron currentTriangulation fzero))) three_dimensional_ball_bundle ≡
  map_outcome (λ currentTriangulation → just (pairing_table currentTriangulation))
    three_dimensional_ball_bundle
self_glued_solid_torus_round_trip_keeps_actual_pairings = refl

refining_one_sphere_tetrahedron_keeps_the_external_neighbor :
  map_outcome (λ currentTriangulation → move_size
    (Moves.subdivide_tetrahedron currentTriangulation fzero)) (sphere 3) ≡ accepted (just 5)
refining_one_sphere_tetrahedron_keeps_the_external_neighbor = refl

refined_sphere_remains_without_boundary_facets :
  map_outcome (λ currentTriangulation → move_boundaries
    (Moves.subdivide_tetrahedron currentTriangulation fzero)) (sphere 3) ≡ accepted (just 0)
refined_sphere_remains_without_boundary_facets = refl
