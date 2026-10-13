{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- Face<3,2>::join(), lock(), unlock(), and isLocked(), from
-- engine/triangulation/face.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission.

module Regina.FacetOperations3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.PermutationExtension
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks
import Regina.Embeddings as Embeddings
import Regina.SubfaceIncidence3 as Subfaces

private
  variable
    simplex_count : Nat

-- A frame relates a facet's inherent positions 0,1,2 to its local
-- tetrahedron labels. Position 3 names the opposite vertex.
record FacetFrame3 (simplex_count : Nat) : Set where
  constructor facet_frame_three
  field
    frame_simplex_number : Fin simplex_count
    frame_vertex_mapping : Permutation 4
open FacetFrame3 public

framedFacet : FacetFrame3 simplex_count → Facet 3 simplex_count
framedFacet currentFrame = facet (frame_simplex_number currentFrame)
  (image (frame_vertex_mapping currentFrame) (finalIndex 3))

private
  frameAfterMapping : Embeddings.FaceEmbedding 3 simplex_count →
    Maybe (Permutation 4) → Outcome (FacetFrame3 simplex_count)
  frameAfterMapping currentEmbedding nothing = rejected invalid_vertex_permutation
  frameAfterMapping currentEmbedding (just currentMapping) = accepted
    (facet_frame_three
      (face_simplex (Embeddings.embedded_local_face currentEmbedding))
      currentMapping)

  frameAfterEmbedding : Maybe (Embeddings.FaceEmbedding 3 simplex_count) →
    Outcome (FacetFrame3 simplex_count)
  frameAfterEmbedding nothing = rejected invalid_facet_number
  frameAfterEmbedding (just currentEmbedding) = frameAfterMapping currentEmbedding
    (from_image_list 4 (Embeddings.embeddingVertexTable currentEmbedding))

-- Resolve a global triangle class in the supplied state, always afresh.
facetFrame : Triangulation 3 simplex_count → Nat →
  Outcome (FacetFrame3 simplex_count)
facetFrame currentTriangulation classNumber = frameAfterEmbedding
  (Subfaces.representativeEmbedding classNumber
    (faceLinkClasses currentTriangulation 2))

-- Source expression:
-- destinationFrame * Perm<4>::extend(inherentGluing) * sourceFrame.inverse().
-- compose applies its right argument first, matching Regina.
facetGluingMapping : FacetFrame3 simplex_count → FacetFrame3 simplex_count →
  Permutation 3 → Permutation 4
facetGluingMapping sourceFrame destinationFrame inherentGluing = compose
  (frame_vertex_mapping destinationFrame)
  (compose (extendPermutation inherentGluing)
    (inverse (frame_vertex_mapping sourceFrame)))

-- A local source label is first read back into the source triangle's
-- inherent labels, relabelled there, and then written in the destination.
facetGluingCarriesInherentVertex :
  (sourceFrame destinationFrame : FacetFrame3 simplex_count)
  (inherentGluing : Permutation 3) (inherentVertex : Fin 3) →
  image (facetGluingMapping sourceFrame destinationFrame inherentGluing)
    (image (frame_vertex_mapping sourceFrame) (includeInitialIndex inherentVertex)) ≡
  image (frame_vertex_mapping destinationFrame)
    (includeInitialIndex (image inherentGluing inherentVertex))
facetGluingCarriesInherentVertex sourceFrame destinationFrame inherentGluing
  inherentVertex = trans
  (cong (λ currentVertex → image (frame_vertex_mapping destinationFrame)
    (image (extendPermutation inherentGluing) currentVertex))
    (preimage_image (frame_vertex_mapping sourceFrame)
      (includeInitialIndex inherentVertex)))
  (cong (image (frame_vertex_mapping destinationFrame))
    (extensionPreservesInitialImage inherentGluing inherentVertex))

-- The fourth image is a facet name, not a vertex of the glued triangle.
facetGluingCarriesOppositeVertex :
  (sourceFrame destinationFrame : FacetFrame3 simplex_count)
  (inherentGluing : Permutation 3) →
  image (facetGluingMapping sourceFrame destinationFrame inherentGluing)
    (opposite_vertex (framedFacet sourceFrame)) ≡
  opposite_vertex (framedFacet destinationFrame)
facetGluingCarriesOppositeVertex sourceFrame destinationFrame inherentGluing = trans
  (cong (λ currentVertex → image (frame_vertex_mapping destinationFrame)
    (image (extendPermutation inherentGluing) currentVertex))
    (preimage_image (frame_vertex_mapping sourceFrame) (finalIndex 3)))
  (cong (image (frame_vertex_mapping destinationFrame))
    (extensionFixesFinalIndex inherentGluing))

-- Reversing both frames and the inherent map gives the exact inverse of
-- the tetrahedron map, including its facet-naming fourth image.
facetGluingReversal : (sourceFrame destinationFrame : FacetFrame3 simplex_count)
  (inherentGluing : Permutation 3) →
  SameImages (facetGluingMapping destinationFrame sourceFrame (inverse inherentGluing))
    (inverse (facetGluingMapping sourceFrame destinationFrame inherentGluing))
facetGluingReversal sourceFrame destinationFrame inherentGluing currentVertex = refl

facetIdentityUnderOneFrame : (currentFrame : FacetFrame3 simplex_count) →
  SameImages (facetGluingMapping currentFrame currentFrame identity) identity
facetIdentityUnderOneFrame currentFrame currentVertex = trans
  (cong (image (frame_vertex_mapping currentFrame))
    (extensionPreservesIdentity
      (preimage (frame_vertex_mapping currentFrame) currentVertex)))
  (image_preimage (frame_vertex_mapping currentFrame) currentVertex)

-- Source and destination are both resolved from this one input state.
-- The low-level join checks occupancy, same-facet pairing, and locks in
-- Regina's order, then certifies reciprocal forward/inverse adjacency.
joinBoundaryFacets : Triangulation 3 simplex_count → Nat → Nat →
  Permutation 3 → Outcome (Transition 3 simplex_count)
joinBoundaryFacets currentTriangulation sourceClass destinationClass inherentGluing
  with facetFrame currentTriangulation sourceClass
... | rejected failureReason = rejected failureReason
... | accepted sourceFrame with facetFrame currentTriangulation destinationClass
... | rejected failureReason = rejected failureReason
... | accepted destinationFrame = join currentTriangulation
  (framedFacet sourceFrame)
  (frame_simplex_number destinationFrame)
  (facetGluingMapping sourceFrame destinationFrame inherentGluing)

facetFaceIsLocked : Triangulation 3 simplex_count → Nat → Outcome Bool
facetFaceIsLocked currentTriangulation classNumber
  with facetFrame currentTriangulation classNumber
... | rejected failureReason = rejected failureReason
... | accepted currentFrame = accepted
  (facet_is_locked (raw_state currentTriangulation) (framedFacet currentFrame))

lockFacetFace : Triangulation 3 simplex_count → Nat →
  Outcome (Transition 3 simplex_count)
lockFacetFace currentTriangulation classNumber
  with facetFrame currentTriangulation classNumber
... | rejected failureReason = rejected failureReason
... | accepted currentFrame = lock_facet currentTriangulation (framedFacet currentFrame)

unlockFacetFace : Triangulation 3 simplex_count → Nat →
  Outcome (Transition 3 simplex_count)
unlockFacetFace currentTriangulation classNumber
  with facetFrame currentTriangulation classNumber
... | rejected failureReason = rejected failureReason
... | accepted currentFrame = unlock_facet currentTriangulation (framedFacet currentFrame)
