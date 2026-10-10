{-# OPTIONS --safe --without-K #-}

-- Reduction tests for explicit ordered face embeddings.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-09.

module Regina.EmbeddingTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Input
open import Regina.Examples
open import Regina.Skeleton
open import Regina.Embeddings

private
  badEdgeSelfPair : Outcome (Triangulation 3 1)
  badEdgeSelfPair = from_input_gluings false 3 1
    (input_gluing 0 0 0 (1 ∷ 0 ∷ 3 ∷ 2 ∷ []) ∷ [])

  edgeMaskTwoThree : Vector Bool 4
  edgeMaskTwoThree = vector_cons false
    (vector_cons false (vector_cons true (vector_cons true empty_vector)))

  edgeTwoThree : LocalFace 3 1
  edgeTwoThree = local_face fzero edgeMaskTwoThree

  crossedBadEdgeTable : Triangulation 3 1 → Maybe (List Nat)
  crossedBadEdgeTable current
    with crossFaceEmbedding current (initialFaceEmbedding edgeTwoThree) fzero
  ... | nothing = nothing
  ... | just embedding = just (embeddingVertexTable embedding)

ball_vertex_embeddings_are_singletons :
  faceEmbeddingClassDegrees (ball 3) 0 ≡ (1 ∷ 1 ∷ 1 ∷ 1 ∷ [])
ball_vertex_embeddings_are_singletons = refl

sphere_vertex_embeddings_are_paired :
  map_outcome (λ current → faceEmbeddingClassDegrees current 0) (sphere 3) ≡
    accepted (2 ∷ 2 ∷ 2 ∷ 2 ∷ [])
sphere_vertex_embeddings_are_paired = refl

ball_bundle_has_one_degree_four_vertex_embedding_class :
  map_outcome (λ current → faceEmbeddingClassDegrees current 0)
    three_dimensional_ball_bundle ≡ accepted (4 ∷ [])
ball_bundle_has_one_degree_four_vertex_embedding_class = refl

figure_eight_vertex_embedding_degree :
  map_outcome (λ current → faceEmbeddingClassDegrees current 0)
    figure_eight_knot_complement ≡ accepted (8 ∷ [])
figure_eight_vertex_embedding_degree = refl

figure_eight_edge_embedding_degrees :
  map_outcome (λ current → faceEmbeddingClassDegrees current 1)
    figure_eight_knot_complement ≡ accepted (6 ∷ 6 ∷ [])
figure_eight_edge_embedding_degrees = refl

figure_eight_facet_embedding_degrees :
  map_outcome (λ current → faceEmbeddingClassDegrees current 2)
    figure_eight_knot_complement ≡ accepted (2 ∷ 2 ∷ 2 ∷ 2 ∷ [])
figure_eight_facet_embedding_degrees = refl

regina_examples_have_no_detected_bad_identifications :
  map_outcome (λ current →
    hasBadFaceIdentification current 0 ∷
    hasBadFaceIdentification current 1 ∷
    hasBadFaceIdentification current 2 ∷ [])
    figure_eight_knot_complement ≡ accepted (false ∷ false ∷ false ∷ [])
regina_examples_have_no_detected_bad_identifications = refl

canonical_edge_embedding_places_face_vertices_first :
  embeddingVertexTable (initialFaceEmbedding edgeTwoThree) ≡
    (2 ∷ 3 ∷ 1 ∷ 0 ∷ [])
canonical_edge_embedding_places_face_vertices_first = refl

crossing_bad_edge_reverses_its_selected_vertex_order :
  map_outcome crossedBadEdgeTable badEdgeSelfPair ≡
    accepted (just (3 ∷ 2 ∷ 0 ∷ 1 ∷ []))
crossing_bad_edge_reverses_its_selected_vertex_order = refl

reversed_edge_self_identification_is_detected :
  map_outcome (λ current → hasBadFaceIdentification current 1)
    badEdgeSelfPair ≡ accepted true
reversed_edge_self_identification_is_detected = refl

same_example_does_not_create_a_bad_vertex_identification :
  map_outcome (λ current → hasBadFaceIdentification current 0)
    badEdgeSelfPair ≡ accepted false
same_example_does_not_create_a_bad_vertex_identification = refl
