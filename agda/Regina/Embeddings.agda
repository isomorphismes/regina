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
appendOne existing newElement = existing ++ (newElement ∷ [])

reverseOnto : {element : Set} → List element → List element → List element
reverseOnto [] result = result
reverseOnto (head ∷ tail) result = reverseOnto tail (head ∷ result)

reverseList : {element : Set} → List element → List element
reverseList source = reverseOnto source []

collectMaskVertices : {numberOfVertices : Nat} →
  Vector Bool numberOfVertices → Bool → List (Fin numberOfVertices) →
  List (Fin numberOfVertices)
collectMaskVertices mask selectedValue [] = []
collectMaskVertices mask selectedValue (currentVertex ∷ remainingVertices)
  with bool_equal (lookup_vector mask currentVertex) selectedValue
... | true = currentVertex ∷ collectMaskVertices mask selectedValue remainingVertices
... | false = collectMaskVertices mask selectedValue remainingVertices

-- FaceNumbering::ordering() always places face vertices first and in increasing
-- order. Regina permits an arbitrary order for the complement. This Agda
-- representation uses descending complement order, matching Regina's generic
-- implementation without copying packed standard-dimension lookup tables.
canonicalEmbeddingVertices : LocalFace dimension simplex_count →
  List (Fin (suc dimension))
canonicalEmbeddingVertices {dimension} source =
  collectMaskVertices (face_vertices source) true (all_fin (suc dimension)) ++
  reverseList (collectMaskVertices (face_vertices source) false
    (all_fin (suc dimension)))

record FaceEmbedding (dimension simplex_count : Nat) : Set where
  constructor face_embedding
  field
    embedded_local_face : LocalFace dimension simplex_count
    ordered_simplex_vertices : List (Fin (suc dimension))
open FaceEmbedding public

initialFaceEmbedding : LocalFace dimension simplex_count →
  FaceEmbedding dimension simplex_count
initialFaceEmbedding source = face_embedding source (canonicalEmbeddingVertices source)

embeddingVertexTable : FaceEmbedding dimension simplex_count → List Nat
embeddingVertexTable embedding = map fin_to_nat (ordered_simplex_vertices embedding)

crossFaceEmbedding : Triangulation dimension simplex_count →
  FaceEmbedding dimension simplex_count → Fin (suc dimension) →
  Maybe (FaceEmbedding dimension simplex_count)
crossFaceEmbedding current source exitFacet
  with lookup_vector (face_vertices (embedded_local_face source)) exitFacet
... | true = nothing
... | false with adjacency (raw_state current)
  (facet (face_simplex (embedded_local_face source)) exitFacet)
... | nothing = nothing
... | just outward = just (face_embedding
  (local_face (adjacent_simplex outward)
    (relabel_face_vertices (vertex_permutation outward)
      (face_vertices (embedded_local_face source))))
  (map (image (vertex_permutation outward)) (ordered_simplex_vertices source)))

prefixVerticesEqual : Nat → List (Fin (suc dimension)) →
  List (Fin (suc dimension)) → Bool
prefixVerticesEqual zero left right = true
prefixVerticesEqual (suc count) [] right = false
prefixVerticesEqual (suc count) left [] = false
prefixVerticesEqual (suc count) (left ∷ leftTail) (right ∷ rightTail) =
  fin_equal left right and prefixVerticesEqual count leftTail rightTail

findEmbeddingForFace : LocalFace dimension simplex_count →
  List (FaceEmbedding dimension simplex_count) →
  Maybe (FaceEmbedding dimension simplex_count)
findEmbeddingForFace target [] = nothing
findEmbeddingForFace target (candidate ∷ remaining)
  with local_face_equal target (embedded_local_face candidate)
... | true = just candidate
... | false = findEmbeddingForFace target remaining

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
observeEmbeddingCandidateAfterLookup faceDimension currentTraversal candidate nothing =
  embedding_traversal
    (appendOne (reached_embeddings currentTraversal) candidate)
    (appendOne (pending_embeddings currentTraversal) candidate)
    (identification_conflict currentTraversal)
observeEmbeddingCandidateAfterLookup faceDimension currentTraversal candidate
  (just previous) = embedding_traversal
    (reached_embeddings currentTraversal)
    (pending_embeddings currentTraversal)
    (identification_conflict currentTraversal or not
      (prefixVerticesEqual (suc faceDimension)
        (ordered_simplex_vertices previous)
        (ordered_simplex_vertices candidate)))

observeEmbeddingCandidate : Nat → EmbeddingTraversal dimension simplex_count →
  FaceEmbedding dimension simplex_count → EmbeddingTraversal dimension simplex_count
observeEmbeddingCandidate faceDimension currentTraversal candidate =
  observeEmbeddingCandidateAfterLookup faceDimension currentTraversal candidate
    (findEmbeddingForFace (embedded_local_face candidate)
      (reached_embeddings currentTraversal))

processEmbeddingExitAfterCrossing : Nat →
  EmbeddingTraversal dimension simplex_count →
  Maybe (FaceEmbedding dimension simplex_count) →
  EmbeddingTraversal dimension simplex_count
processEmbeddingExitAfterCrossing faceDimension currentTraversal nothing =
  currentTraversal
processEmbeddingExitAfterCrossing faceDimension currentTraversal (just candidate) =
  observeEmbeddingCandidate faceDimension currentTraversal candidate

processEmbeddingExit : Triangulation dimension simplex_count → Nat →
  EmbeddingTraversal dimension simplex_count →
  FaceEmbedding dimension simplex_count → Fin (suc dimension) →
  EmbeddingTraversal dimension simplex_count
processEmbeddingExit current faceDimension currentTraversal source exitFacet =
  processEmbeddingExitAfterCrossing faceDimension currentTraversal
    (crossFaceEmbedding current source exitFacet)

processEmbeddingExits : Triangulation dimension simplex_count → Nat →
  EmbeddingTraversal dimension simplex_count →
  FaceEmbedding dimension simplex_count → List (Fin (suc dimension)) →
  EmbeddingTraversal dimension simplex_count
processEmbeddingExits current faceDimension currentTraversal source [] =
  currentTraversal
processEmbeddingExits current faceDimension currentTraversal source
  (exitFacet ∷ remaining) =
  processEmbeddingExits current faceDimension
    (processEmbeddingExit current faceDimension currentTraversal source exitFacet)
    source remaining

walkEmbeddingQueue : (simplexDimension faceDimension : Nat) →
  {numberOfSimplices : Nat} → Nat →
  Triangulation simplexDimension numberOfSimplices →
  EmbeddingTraversal simplexDimension numberOfSimplices →
  EmbeddingTraversal simplexDimension numberOfSimplices
walkEmbeddingQueue simplexDimension faceDimension zero current currentTraversal =
  currentTraversal
walkEmbeddingQueue simplexDimension faceDimension (suc fuel) current currentTraversal
  with pending_embeddings currentTraversal
... | [] = currentTraversal
... | source ∷ remaining =
  walkEmbeddingQueue simplexDimension faceDimension fuel current
    (processEmbeddingExits current faceDimension
      (embedding_traversal (reached_embeddings currentTraversal) remaining
        (identification_conflict currentTraversal))
      source (all_fin (suc simplexDimension)))

record EmbeddingClass (dimension simplex_count : Nat) : Set where
  constructor embedding_class
  field
    class_embeddings : List (FaceEmbedding dimension simplex_count)
    class_has_bad_identification : Bool
open EmbeddingClass public

embeddingClassFromSeedAfterInitial :
  Triangulation dimension simplex_count → Nat → Nat →
  FaceEmbedding dimension simplex_count → EmbeddingClass dimension simplex_count
embeddingClassFromSeedAfterInitial {dimension} current faceDimension fuel firstEmbedding
  with walkEmbeddingQueue dimension faceDimension fuel current
    (embedding_traversal (firstEmbedding ∷ []) (firstEmbedding ∷ []) false)
... | completed = embedding_class
  (reached_embeddings completed) (identification_conflict completed)

embeddingClassFromSeed : Triangulation dimension simplex_count → Nat → Nat →
  LocalFace dimension simplex_count → EmbeddingClass dimension simplex_count
embeddingClassFromSeed current faceDimension fuel seed =
  embeddingClassFromSeedAfterInitial current faceDimension fuel
    (initialFaceEmbedding seed)

faceReachedByEmbeddings : LocalFace dimension simplex_count →
  List (FaceEmbedding dimension simplex_count) → Bool
faceReachedByEmbeddings target [] = false
faceReachedByEmbeddings target (candidate ∷ remaining) =
  local_face_equal target (embedded_local_face candidate) or
  faceReachedByEmbeddings target remaining

removeReachedFaces : List (FaceEmbedding dimension simplex_count) →
  List (LocalFace dimension simplex_count) →
  List (LocalFace dimension simplex_count)
removeReachedFaces embeddings [] = []
removeReachedFaces embeddings (candidate ∷ remaining)
  with faceReachedByEmbeddings candidate embeddings
... | true = removeReachedFaces embeddings remaining
... | false = candidate ∷ removeReachedFaces embeddings remaining

partitionEmbeddingClasses : Nat → Nat →
  Triangulation dimension simplex_count →
  List (LocalFace dimension simplex_count) →
  List (LocalFace dimension simplex_count) →
  List (EmbeddingClass dimension simplex_count)
partitionEmbeddingClasses faceDimension zero current universe remaining = []
partitionEmbeddingClasses faceDimension (suc fuel) current universe [] = []
partitionEmbeddingClasses faceDimension (suc fuel) current universe (seed ∷ remaining)
  with embeddingClassFromSeed current faceDimension (length universe) seed
... | foundClass = foundClass ∷
  partitionEmbeddingClasses faceDimension fuel current universe
    (removeReachedFaces (class_embeddings foundClass) remaining)

faceEmbeddingClasses : Triangulation dimension simplex_count → Nat →
  List (EmbeddingClass dimension simplex_count)
faceEmbeddingClasses {dimension} {simplex_count} current faceDimension
  with local_faces dimension simplex_count faceDimension
... | universe = partitionEmbeddingClasses faceDimension (length universe)
  current universe universe

faceEmbeddingClassCount : Triangulation dimension simplex_count → Nat → Nat
faceEmbeddingClassCount current faceDimension =
  length (faceEmbeddingClasses current faceDimension)

faceEmbeddingClassDegrees : Triangulation dimension simplex_count → Nat → List Nat
faceEmbeddingClassDegrees current faceDimension =
  map (λ foundClass → length (class_embeddings foundClass))
    (faceEmbeddingClasses current faceDimension)

badFaceIdentificationCount : Triangulation dimension simplex_count → Nat → Nat
badFaceIdentificationCount current faceDimension = count_matching
  class_has_bad_identification (faceEmbeddingClasses current faceDimension)

hasBadFaceIdentification : Triangulation dimension simplex_count → Nat → Bool
hasBadFaceIdentification current faceDimension = any
  class_has_bad_identification (faceEmbeddingClasses current faceDimension)
