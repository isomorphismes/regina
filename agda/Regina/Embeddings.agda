{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-09. License: ../../LICENSE.txt.

-- Explicit ordered appearances of lower-dimensional faces.
-- Derived from engine/triangulation/face.h, facenumbering.h, and
-- detail/skeleton-impl.h at e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.Embeddings where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton

private
  variable
    dimension simplex_count : Nat

appendOne : {element : Set} → List element → element → List element
appendOne existingElements newElement = existingElements ++ (newElement ∷ [])

reverseOnto : {element : Set} → List element → List element → List element
reverseOnto [] accumulatedElements = accumulatedElements
reverseOnto (headElement ∷ tailElements) accumulatedElements =
  reverseOnto tailElements (headElement ∷ accumulatedElements)

reverseList : {element : Set} → List element → List element
reverseList sourceElements = reverseOnto sourceElements []

collectMaskVertices : {numberOfVertices : Nat} →
  Vector Bool numberOfVertices → Bool → List (Fin numberOfVertices) →
  List (Fin numberOfVertices)
collectMaskVertices faceMask selectedValue [] = []
collectMaskVertices faceMask selectedValue
  (currentVertex ∷ remainingVertices)
  with bool_equal (lookup_vector faceMask currentVertex) selectedValue
... | true = currentVertex ∷
  collectMaskVertices faceMask selectedValue remainingVertices
... | false = collectMaskVertices faceMask selectedValue remainingVertices

-- FaceNumbering::ordering() always places face vertices first and in increasing
-- order. Regina permits an arbitrary order for the complement. This Agda
-- representation uses descending complement order, matching Regina's generic
-- implementation without copying packed standard-dimension lookup tables.
canonicalEmbeddingVertices : LocalFace dimension simplex_count →
  List (Fin (suc dimension))
canonicalEmbeddingVertices {dimension} sourceFace =
  collectMaskVertices (face_vertices sourceFace) true
    (all_fin (suc dimension)) ++
  reverseList
    (collectMaskVertices (face_vertices sourceFace) false
      (all_fin (suc dimension)))

record FaceEmbedding (dimension simplex_count : Nat) : Set where
  constructor face_embedding
  field
    embedded_local_face : LocalFace dimension simplex_count
    ordered_simplex_vertices : List (Fin (suc dimension))
open FaceEmbedding public

initialFaceEmbedding : LocalFace dimension simplex_count →
  FaceEmbedding dimension simplex_count
initialFaceEmbedding sourceFace =
  face_embedding sourceFace (canonicalEmbeddingVertices sourceFace)

embeddingVertexTable : FaceEmbedding dimension simplex_count → List Nat
embeddingVertexTable currentEmbedding =
  map fin_to_nat (ordered_simplex_vertices currentEmbedding)

crossFaceEmbedding : Triangulation dimension simplex_count →
  FaceEmbedding dimension simplex_count → Fin (suc dimension) →
  Maybe (FaceEmbedding dimension simplex_count)
crossFaceEmbedding currentTriangulation sourceEmbedding exitFacet
  with lookup_vector
    (face_vertices (embedded_local_face sourceEmbedding)) exitFacet
... | true = nothing
... | false with adjacency (raw_state currentTriangulation)
  (facet (face_simplex (embedded_local_face sourceEmbedding)) exitFacet)
... | nothing = nothing
... | just outwardGluing = just (face_embedding
  (local_face (adjacent_simplex outwardGluing)
    (relabel_face_vertices (vertex_permutation outwardGluing)
      (face_vertices (embedded_local_face sourceEmbedding))))
  (map (image (vertex_permutation outwardGluing))
    (ordered_simplex_vertices sourceEmbedding)))

prefixVerticesEqual : Nat → List (Fin (suc dimension)) →
  List (Fin (suc dimension)) → Bool
prefixVerticesEqual zero leftVertices rightVertices = true
prefixVerticesEqual (suc prefixLength) [] rightVertices = false
prefixVerticesEqual (suc prefixLength) leftVertices [] = false
prefixVerticesEqual (suc prefixLength)
  (leftVertex ∷ remainingLeftVertices)
  (rightVertex ∷ remainingRightVertices) =
  fin_equal leftVertex rightVertex and
  prefixVerticesEqual prefixLength remainingLeftVertices remainingRightVertices

findEmbeddingForFace : LocalFace dimension simplex_count →
  List (FaceEmbedding dimension simplex_count) →
  Maybe (FaceEmbedding dimension simplex_count)
findEmbeddingForFace targetFace [] = nothing
findEmbeddingForFace targetFace
  (candidateEmbedding ∷ remainingEmbeddings)
  with local_face_equal targetFace
    (embedded_local_face candidateEmbedding)
... | true = just candidateEmbedding
... | false = findEmbeddingForFace targetFace remainingEmbeddings

record EmbeddingTraversal (dimension simplex_count : Nat) : Set where
  constructor embedding_traversal
  field
    reached_embeddings : List (FaceEmbedding dimension simplex_count)
    pending_embeddings : List (FaceEmbedding dimension simplex_count)
    identification_conflict : Bool
open EmbeddingTraversal public

observeEmbeddingCandidateAfterLookup : Nat →
  EmbeddingTraversal dimension simplex_count →
  FaceEmbedding dimension simplex_count →
  Maybe (FaceEmbedding dimension simplex_count) →
  EmbeddingTraversal dimension simplex_count
observeEmbeddingCandidateAfterLookup faceDimension currentTraversal
  candidateEmbedding nothing =
  embedding_traversal
    (appendOne (reached_embeddings currentTraversal) candidateEmbedding)
    (appendOne (pending_embeddings currentTraversal) candidateEmbedding)
    (identification_conflict currentTraversal)
observeEmbeddingCandidateAfterLookup faceDimension currentTraversal
  candidateEmbedding (just previousEmbedding) =
  embedding_traversal
    (reached_embeddings currentTraversal)
    (pending_embeddings currentTraversal)
    (identification_conflict currentTraversal or not
      (prefixVerticesEqual (suc faceDimension)
        (ordered_simplex_vertices previousEmbedding)
        (ordered_simplex_vertices candidateEmbedding)))

observeEmbeddingCandidate : Nat →
  EmbeddingTraversal dimension simplex_count →
  FaceEmbedding dimension simplex_count →
  EmbeddingTraversal dimension simplex_count
observeEmbeddingCandidate faceDimension currentTraversal candidateEmbedding =
  observeEmbeddingCandidateAfterLookup faceDimension currentTraversal
    candidateEmbedding
    (findEmbeddingForFace (embedded_local_face candidateEmbedding)
      (reached_embeddings currentTraversal))

processEmbeddingExitAfterCrossing : Nat →
  EmbeddingTraversal dimension simplex_count →
  Maybe (FaceEmbedding dimension simplex_count) →
  EmbeddingTraversal dimension simplex_count
processEmbeddingExitAfterCrossing faceDimension currentTraversal nothing =
  currentTraversal
processEmbeddingExitAfterCrossing faceDimension currentTraversal
  (just candidateEmbedding) =
  observeEmbeddingCandidate faceDimension currentTraversal candidateEmbedding

processEmbeddingExit : Triangulation dimension simplex_count → Nat →
  EmbeddingTraversal dimension simplex_count →
  FaceEmbedding dimension simplex_count → Fin (suc dimension) →
  EmbeddingTraversal dimension simplex_count
processEmbeddingExit currentTriangulation faceDimension currentTraversal
  sourceEmbedding exitFacet =
  processEmbeddingExitAfterCrossing faceDimension currentTraversal
    (crossFaceEmbedding currentTriangulation sourceEmbedding exitFacet)

processEmbeddingExits : Triangulation dimension simplex_count → Nat →
  EmbeddingTraversal dimension simplex_count →
  FaceEmbedding dimension simplex_count → List (Fin (suc dimension)) →
  EmbeddingTraversal dimension simplex_count
processEmbeddingExits currentTriangulation faceDimension currentTraversal
  sourceEmbedding [] = currentTraversal
processEmbeddingExits currentTriangulation faceDimension currentTraversal
  sourceEmbedding (exitFacet ∷ remainingExitFacets) =
  processEmbeddingExits currentTriangulation faceDimension
    (processEmbeddingExit currentTriangulation faceDimension currentTraversal
      sourceEmbedding exitFacet)
    sourceEmbedding remainingExitFacets

walkEmbeddingQueue : (simplexDimension faceDimension : Nat) →
  {numberOfSimplices : Nat} → Nat →
  Triangulation simplexDimension numberOfSimplices →
  EmbeddingTraversal simplexDimension numberOfSimplices →
  EmbeddingTraversal simplexDimension numberOfSimplices
walkEmbeddingQueue simplexDimension faceDimension zero currentTriangulation
  currentTraversal = currentTraversal
walkEmbeddingQueue simplexDimension faceDimension (suc fuel)
  currentTriangulation currentTraversal
  with pending_embeddings currentTraversal
... | [] = currentTraversal
... | sourceEmbedding ∷ remainingQueue =
  walkEmbeddingQueue simplexDimension faceDimension fuel currentTriangulation
    (processEmbeddingExits currentTriangulation faceDimension
      (embedding_traversal
        (reached_embeddings currentTraversal)
        remainingQueue
        (identification_conflict currentTraversal))
      sourceEmbedding (all_fin (suc simplexDimension)))

record EmbeddingClass (dimension simplex_count : Nat) : Set where
  constructor embedding_class
  field
    class_embeddings : List (FaceEmbedding dimension simplex_count)
    class_has_bad_identification : Bool
open EmbeddingClass public

embeddingClassFromSeedAfterInitial :
  Triangulation dimension simplex_count → Nat → Nat →
  FaceEmbedding dimension simplex_count →
  EmbeddingClass dimension simplex_count
embeddingClassFromSeedAfterInitial {dimension} currentTriangulation
  faceDimension fuel initialEmbedding
  with walkEmbeddingQueue dimension faceDimension fuel currentTriangulation
    (embedding_traversal
      (initialEmbedding ∷ []) (initialEmbedding ∷ []) false)
... | completedTraversal = embedding_class
  (reached_embeddings completedTraversal)
  (identification_conflict completedTraversal)

embeddingClassFromSeed : Triangulation dimension simplex_count → Nat → Nat →
  LocalFace dimension simplex_count → EmbeddingClass dimension simplex_count
embeddingClassFromSeed currentTriangulation faceDimension fuel seedFace =
  embeddingClassFromSeedAfterInitial currentTriangulation faceDimension fuel
    (initialFaceEmbedding seedFace)

faceReachedByEmbeddings : LocalFace dimension simplex_count →
  List (FaceEmbedding dimension simplex_count) → Bool
faceReachedByEmbeddings targetFace [] = false
faceReachedByEmbeddings targetFace
  (candidateEmbedding ∷ remainingEmbeddings) =
  local_face_equal targetFace (embedded_local_face candidateEmbedding) or
  faceReachedByEmbeddings targetFace remainingEmbeddings

removeReachedFaces : List (FaceEmbedding dimension simplex_count) →
  List (LocalFace dimension simplex_count) →
  List (LocalFace dimension simplex_count)
removeReachedFaces reachedEmbeddings [] = []
removeReachedFaces reachedEmbeddings
  (candidateFace ∷ remainingFaces)
  with faceReachedByEmbeddings candidateFace reachedEmbeddings
... | true = removeReachedFaces reachedEmbeddings remainingFaces
... | false = candidateFace ∷
  removeReachedFaces reachedEmbeddings remainingFaces

partitionEmbeddingClasses : Nat → Nat →
  Triangulation dimension simplex_count →
  List (LocalFace dimension simplex_count) →
  List (LocalFace dimension simplex_count) →
  List (EmbeddingClass dimension simplex_count)
partitionEmbeddingClasses faceDimension zero currentTriangulation
  faceUniverse remainingFaces = []
partitionEmbeddingClasses faceDimension (suc fuel) currentTriangulation
  faceUniverse [] = []
partitionEmbeddingClasses faceDimension (suc fuel) currentTriangulation
  faceUniverse (seedFace ∷ remainingFaces)
  with embeddingClassFromSeed currentTriangulation faceDimension
    (length faceUniverse) seedFace
... | discoveredClass = discoveredClass ∷
  partitionEmbeddingClasses faceDimension fuel currentTriangulation faceUniverse
    (removeReachedFaces
      (class_embeddings discoveredClass) remainingFaces)

faceEmbeddingClasses : Triangulation dimension simplex_count → Nat →
  List (EmbeddingClass dimension simplex_count)
faceEmbeddingClasses {dimension} {simplex_count} currentTriangulation
  faceDimension
  with local_faces dimension simplex_count faceDimension
... | faceUniverse = partitionEmbeddingClasses faceDimension
  (length faceUniverse) currentTriangulation faceUniverse faceUniverse

faceEmbeddingClassCount : Triangulation dimension simplex_count → Nat → Nat
faceEmbeddingClassCount currentTriangulation faceDimension =
  length (faceEmbeddingClasses currentTriangulation faceDimension)

faceEmbeddingClassDegrees : Triangulation dimension simplex_count → Nat →
  List Nat
faceEmbeddingClassDegrees currentTriangulation faceDimension =
  map (λ discoveredClass → length (class_embeddings discoveredClass))
    (faceEmbeddingClasses currentTriangulation faceDimension)

badFaceIdentificationCount : Triangulation dimension simplex_count → Nat → Nat
badFaceIdentificationCount currentTriangulation faceDimension =
  count_matching
    (λ discoveredClass → class_has_bad_identification discoveredClass)
    (faceEmbeddingClasses currentTriangulation faceDimension)

hasBadFaceIdentification : Triangulation dimension simplex_count → Nat → Bool
hasBadFaceIdentification currentTriangulation faceDimension =
  any (λ discoveredClass → class_has_bad_identification discoveredClass)
    (faceEmbeddingClasses currentTriangulation faceDimension)
