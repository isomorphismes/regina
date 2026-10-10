{-# OPTIONS --safe --without-K #-}

-- Reduction tests for orientation-normalised face-link traversal.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-10.

module Regina.FaceLinkTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Input
open import Regina.Examples
open import Regina.Skeleton
import Regina.Embeddings as Embeddings
open import Regina.FaceLinks

private
  reversedEdgePair : Outcome (Triangulation 3 1)
  reversedEdgePair = from_input_gluings false 3 1
    (input_gluing 0 0 0 (1 ∷ 0 ∷ 3 ∷ 2 ∷ []) ∷ [])

  -- This even 3-cycle pairs facets 0 and 1, fixes local vertex 2, and
  -- returns that vertex link with the complementary triangle reversed.
  nonorientableVertexLinkPair : Outcome (Triangulation 3 1)
  nonorientableVertexLinkPair = from_input_gluings false 3 1
    (input_gluing 0 0 0 (1 ∷ 3 ∷ 2 ∷ 0 ∷ []) ∷ [])

  edgeMaskTwoThree : Vector Bool 4
  edgeMaskTwoThree = vector_cons false
    (vector_cons false
      (vector_cons true (vector_cons true empty_vector)))

  edgeTwoThree : LocalFace 3 1
  edgeTwoThree = local_face fzero edgeMaskTwoThree

  vertexMaskTwo : Vector Bool 4
  vertexMaskTwo = vector_cons false
    (vector_cons false
      (vector_cons true (vector_cons false empty_vector)))

  vertexTwo : LocalFace 3 1
  vertexTwo = local_face fzero vertexMaskTwo

  crossedEdgeTable : Triangulation 3 1 → Maybe (List Nat)
  crossedEdgeTable currentTriangulation
    with crossFaceLinkEmbedding 3 1 currentTriangulation
      (Embeddings.initialFaceEmbedding edgeTwoThree) fzero
  ... | nothing = nothing
  ... | just crossedEmbedding =
    just (Embeddings.embeddingVertexTable crossedEmbedding)

  crossedVertexTable : Triangulation 3 1 → Maybe (List Nat)
  crossedVertexTable currentTriangulation
    with crossFaceLinkEmbedding 3 0 currentTriangulation
      (Embeddings.initialFaceEmbedding vertexTwo) fzero
  ... | nothing = nothing
  ... | just crossedEmbedding =
    just (Embeddings.embeddingVertexTable crossedEmbedding)

codimension_classification_checked :
  faceCodimensionKind 3 2 ≡ codimension_one
codimension_classification_checked = refl

codimension_two_classification_checked :
  faceCodimensionKind 3 1 ≡ codimension_two
codimension_two_classification_checked = refl

larger_codimension_classification_checked :
  faceCodimensionKind 3 0 ≡ codimension_greater_than_two
larger_codimension_classification_checked = refl

ball_vertex_links_are_orientable :
  allFaceLinksOrientable (ball 3) 0 ≡ true
ball_vertex_links_are_orientable = refl

sphere_vertex_links_are_orientable :
  map_outcome
    (λ currentTriangulation → allFaceLinksOrientable currentTriangulation 0)
    (sphere 3) ≡ accepted true
sphere_vertex_links_are_orientable = refl

ball_bundle_vertex_link_is_orientable :
  map_outcome
    (λ currentTriangulation → allFaceLinksOrientable currentTriangulation 0)
    three_dimensional_ball_bundle ≡ accepted true
ball_bundle_vertex_link_is_orientable = refl

figure_eight_vertex_link_is_orientable :
  map_outcome
    (λ currentTriangulation → allFaceLinksOrientable currentTriangulation 0)
    figure_eight_knot_complement ≡ accepted true
figure_eight_vertex_link_is_orientable = refl

figure_eight_link_embedding_degrees :
  map_outcome
    (λ currentTriangulation →
      faceLinkClassDegrees currentTriangulation 0 ∷
      faceLinkClassDegrees currentTriangulation 1 ∷
      faceLinkClassDegrees currentTriangulation 2 ∷ [])
    figure_eight_knot_complement ≡
      accepted
        ((8 ∷ []) ∷
         (6 ∷ 6 ∷ []) ∷
         (2 ∷ 2 ∷ 2 ∷ 2 ∷ []) ∷ [])
figure_eight_link_embedding_degrees = refl

figure_eight_has_no_bad_face_identifications :
  map_outcome
    (λ currentTriangulation →
      hasBadIdentification currentTriangulation 0 ∷
      hasBadIdentification currentTriangulation 1 ∷
      hasBadIdentification currentTriangulation 2 ∷ [])
    figure_eight_knot_complement ≡
      accepted (false ∷ false ∷ false ∷ [])
figure_eight_has_no_bad_face_identifications = refl

normalised_edge_crossing_swaps_complement_before_gluing :
  map_outcome crossedEdgeTable reversedEdgePair ≡
    accepted (just (3 ∷ 2 ∷ 1 ∷ 0 ∷ []))
normalised_edge_crossing_swaps_complement_before_gluing = refl

codimension_two_full_return_detects_reversed_edge :
  map_outcome
    (λ currentTriangulation → hasBadIdentification currentTriangulation 1)
    reversedEdgePair ≡ accepted true
codimension_two_full_return_detects_reversed_edge = refl

codimension_two_link_remains_orientable :
  map_outcome
    (λ currentTriangulation → allFaceLinksOrientable currentTriangulation 1)
    reversedEdgePair ≡ accepted true
codimension_two_link_remains_orientable = refl

normalised_vertex_crossing_exhibits_complement_reversal :
  map_outcome crossedVertexTable nonorientableVertexLinkPair ≡
    accepted (just (2 ∷ 0 ∷ 1 ∷ 3 ∷ []))
normalised_vertex_crossing_exhibits_complement_reversal = refl

nonorientable_vertex_link_is_detected :
  map_outcome
    (λ currentTriangulation → allFaceLinksOrientable currentTriangulation 0)
    nonorientableVertexLinkPair ≡ accepted false
nonorientable_vertex_link_is_detected = refl

nonorientable_return_does_not_invent_a_vertex_identification :
  map_outcome
    (λ currentTriangulation → hasBadIdentification currentTriangulation 0)
    nonorientableVertexLinkPair ≡ accepted false
nonorientable_return_does_not_invent_a_vertex_identification = refl
