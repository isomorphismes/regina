{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- Face<3,0>::buildLink() and buildLinkInclusion(), engine/triangulation/dim3/vertex3.cpp.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.VertexLinkTriangulation3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.PermutationExtension using (includeInitialIndex)
open import Regina.PermutationContraction
open import Regina.Triangulation
open import Regina.Skeleton
import Regina.Embeddings as Embeddings
import Regina.VertexLinkSurface3 as Links
import Regina.SubfaceIncidence3 as Subfaces
import Regina.TetrahedronFaces3 as TetrahedronFaces

private
  variable
    simplex_count : Nat

lookupOccurrence : (occurrences : List (Embeddings.FaceEmbedding 3 simplex_count)) →
  Fin (length occurrences) → Embeddings.FaceEmbedding 3 simplex_count
lookupOccurrence [] ()
lookupOccurrence (head ∷ tail) fzero = head
lookupOccurrence (head ∷ tail) (fsuc index) = lookupOccurrence tail index

record LinkInclusionFrame3 (simplex_count : Nat) : Set where
  constructor link_inclusion_frame_three
  field
    inclusion_tetrahedron : Fin simplex_count
    inclusion_vertex : Fin 4
    inclusion_mapping : Permutation 4
open LinkInclusionFrame3 public

occurrenceFrame : Triangulation 3 simplex_count →
  Embeddings.FaceEmbedding 3 simplex_count → Maybe (LinkInclusionFrame3 simplex_count)
occurrenceFrame currentTriangulation occurrence with Links.selectedVertex occurrence
... | nothing = nothing
... | just localVertex
  with TetrahedronFaces.tetrahedronTriangleReference currentTriangulation
    (fin_to_nat (face_simplex (Embeddings.embedded_local_face occurrence)))
    (fin_to_nat localVertex)
... | nothing = nothing
... | just reference = just (link_inclusion_frame_three
  (face_simplex (Embeddings.embedded_local_face occurrence)) localVertex
  (TetrahedronFaces.tetrahedron_face_mapping reference))

resolveLinkSide : Triangulation 3 simplex_count →
  (occurrences : List (Embeddings.FaceEmbedding 3 simplex_count)) →
  Facet 2 (length occurrences) → Maybe (Maybe (Gluing 2 (length occurrences)))
resolveLinkSide currentTriangulation occurrences sourceSide
  with occurrenceFrame currentTriangulation
    (lookupOccurrence occurrences (simplex_number sourceSide))
... | nothing = nothing
... | just sourceFrame
  with adjacency (raw_state currentTriangulation)
    (facet (inclusion_tetrahedron sourceFrame)
      (image (inclusion_mapping sourceFrame)
        (includeInitialIndex (opposite_vertex sourceSide))))
... | nothing = just nothing
... | just outwardGluing
  with Links.findOccurrenceIndex
    (Links.localVertexFace (adjacent_simplex outwardGluing)
      (image (vertex_permutation outwardGluing) (inclusion_vertex sourceFrame)))
    occurrences
... | nothing = nothing
... | just targetNumber with fin_from_nat (length occurrences) targetNumber
... | nothing = nothing
... | just targetIndex
  with occurrenceFrame currentTriangulation (lookupOccurrence occurrences targetIndex)
... | nothing = nothing
... | just targetFrame
  with contractPermutation (compose (inverse (inclusion_mapping targetFrame))
    (compose (vertex_permutation outwardGluing) (inclusion_mapping sourceFrame)))
... | nothing = nothing
... | just contractionResult = just (just
  (gluing targetIndex (contracted_permutation contractionResult)))

record BuiltVertexLink3 (simplex_count : Nat) : Set where
  constructor built_vertex_link_three
  field
    built_source_vertex_number : Nat
    built_link_triangle_count : Nat
    built_link_triangulation : Triangulation 2 built_link_triangle_count
    built_link_inclusion : List (Maybe (LinkInclusionFrame3 simplex_count))
open BuiltVertexLink3 public

private
  resolved : {element : Set} → Maybe element → Bool
  resolved nothing = false
  resolved (just _) = true

  flatten : {element : Set} → Maybe (Maybe element) → Maybe element
  flatten nothing = nothing
  flatten (just result) = result

buildFromCandidates : (numberOfTriangles : Nat) → Nat →
  List (Maybe (LinkInclusionFrame3 simplex_count)) →
  (candidate : Facet 2 numberOfTriangles → Maybe (Maybe (Gluing 2 numberOfTriangles))) →
  Maybe (BuiltVertexLink3 simplex_count)
buildFromCandidates numberOfTriangles vertexNumber inclusionFrames sideCandidate
  with all resolved inclusionFrames and
    all (λ sourceSide → resolved (sideCandidate sourceSide))
      (all_facets 2 numberOfTriangles)
... | false = nothing
... | true with certify (raw_triangulation
    (λ sourceSide → flatten (sideCandidate sourceSide)) (λ _ → false) (λ _ → false))
... | rejected _ = nothing
... | accepted surface = just (built_vertex_link_three
  vertexNumber numberOfTriangles surface inclusionFrames)

buildVertexLink : Triangulation 3 simplex_count →
  Links.ExplicitVertexLink simplex_count → Maybe (BuiltVertexLink3 simplex_count)
buildVertexLink currentTriangulation explicitLink = buildFromCandidates
  (length (Links.triangle_occurrences explicitLink))
  (Links.source_vertex_class_number explicitLink)
  (map (occurrenceFrame currentTriangulation) (Links.triangle_occurrences explicitLink))
  (resolveLinkSide currentTriangulation (Links.triangle_occurrences explicitLink))

buildVertexLinks : Triangulation 3 simplex_count →
  List (Maybe (BuiltVertexLink3 simplex_count))
buildVertexLinks currentTriangulation = map (buildVertexLink currentTriangulation)
  (Links.explicitVertexLinks currentTriangulation)
