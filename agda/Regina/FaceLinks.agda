{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- Orientation-normalised face traversal and link-orientation diagnostics.
-- Derived from engine/triangulation/detail/skeleton-impl.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.FaceLinks where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton
import Regina.Components as Components
import Regina.Embeddings as Embeddings

private
  variable
    dimension simplex_count : Nat

appendElement : {element : Set} → List element → element → List element
appendElement existingElements newElement = existingElements ++ (newElement ∷ [])

data FaceCodimensionKind : Set where
  codimension_one : FaceCodimensionKind
  codimension_two : FaceCodimensionKind
  codimension_greater_than_two : FaceCodimensionKind
  invalid_codimension : FaceCodimensionKind

classifyAfterCodimensionTwo : Nat → Nat → Bool → FaceCodimensionKind
classifyAfterCodimensionTwo simplexDimension faceDimension true =
  codimension_two
classifyAfterCodimensionTwo simplexDimension faceDimension false
  with less_than (suc (suc faceDimension)) simplexDimension
... | true = codimension_greater_than_two
... | false = invalid_codimension

classifyAfterCodimensionOne : Nat → Nat → Bool → FaceCodimensionKind
classifyAfterCodimensionOne simplexDimension faceDimension true =
  codimension_one
classifyAfterCodimensionOne simplexDimension faceDimension false =
  classifyAfterCodimensionTwo simplexDimension faceDimension
    (nat_equal (suc (suc faceDimension)) simplexDimension)

faceCodimensionKind : Nat → Nat → FaceCodimensionKind
faceCodimensionKind simplexDimension faceDimension =
  classifyAfterCodimensionOne simplexDimension faceDimension
    (nat_equal (suc faceDimension) simplexDimension)

swapLastTwo : {element : Set} → List element → List element
swapLastTwo [] = []
swapLastTwo (onlyElement ∷ []) = onlyElement ∷ []
swapLastTwo (firstElement ∷ secondElement ∷ []) =
  secondElement ∷ firstElement ∷ []
swapLastTwo
  (firstElement ∷ secondElement ∷ thirdElement ∷ remainingElements) =
  firstElement ∷
    swapLastTwo (secondElement ∷ thirdElement ∷ remainingElements)

normaliseForLinkCrossingByKind : {element : Set} →
  FaceCodimensionKind → List element → List element
normaliseForLinkCrossingByKind codimension_one orderedElements = orderedElements
normaliseForLinkCrossingByKind codimension_two orderedElements =
  swapLastTwo orderedElements
normaliseForLinkCrossingByKind codimension_greater_than_two orderedElements =
  swapLastTwo orderedElements
normaliseForLinkCrossingByKind invalid_codimension orderedElements = orderedElements

normaliseForLinkCrossing : Nat → Nat →
  List (Fin (suc dimension)) → List (Fin (suc dimension))
normaliseForLinkCrossing simplexDimension faceDimension orderedVertices =
  normaliseForLinkCrossingByKind
    (faceCodimensionKind simplexDimension faceDimension) orderedVertices

-- Regina right-multiplies the current face mapping by the transposition of
-- its last two positions before crossing any facet of codimension at least
-- two. This preserves the chosen orientation of the complementary link
-- simplex while the gluing permutation transports all local labels.
crossFaceLinkEmbedding :
  (simplexDimension faceDimension : Nat) →
  {numberOfSimplices : Nat} →
  Triangulation simplexDimension numberOfSimplices →
  Embeddings.FaceEmbedding simplexDimension numberOfSimplices →
  Fin (suc simplexDimension) →
  Maybe (Embeddings.FaceEmbedding simplexDimension numberOfSimplices)
crossFaceLinkEmbedding simplexDimension faceDimension currentTriangulation
  sourceEmbedding exitFacet
  with lookup_vector
    (face_vertices (Embeddings.embedded_local_face sourceEmbedding)) exitFacet
... | true = nothing
... | false with adjacency (raw_state currentTriangulation)
  (facet
    (face_simplex (Embeddings.embedded_local_face sourceEmbedding))
    exitFacet)
... | nothing = nothing
... | just outwardGluing = just (Embeddings.face_embedding
  (local_face (adjacent_simplex outwardGluing)
    (relabel_face_vertices (vertex_permutation outwardGluing)
      (face_vertices (Embeddings.embedded_local_face sourceEmbedding))))
  (map (image (vertex_permutation outwardGluing))
    (normaliseForLinkCrossing simplexDimension faceDimension
      (Embeddings.ordered_simplex_vertices sourceEmbedding))))

vertexListsEqual : {numberOfVertices : Nat} →
  List (Fin numberOfVertices) → List (Fin numberOfVertices) → Bool
vertexListsEqual [] [] = true
vertexListsEqual [] (rightHead ∷ rightTail) = false
vertexListsEqual (leftHead ∷ leftTail) [] = false
vertexListsEqual (leftHead ∷ leftTail) (rightHead ∷ rightTail) =
  fin_equal leftHead rightHead and vertexListsEqual leftTail rightTail

dropElements : {element : Set} → Nat → List element → List element
dropElements zero elements = elements
dropElements (suc amount) [] = []
dropElements (suc amount) (headElement ∷ tailElements) =
  dropElements amount tailElements

positionOfVertex : {numberOfVertices : Nat} →
  Fin numberOfVertices → List (Fin numberOfVertices) → Nat
positionOfVertex targetVertex [] = zero
positionOfVertex targetVertex (currentVertex ∷ remainingVertices)
  with fin_equal targetVertex currentVertex
... | true = zero
... | false = suc (positionOfVertex targetVertex remainingVertices)

relativeVertexOrder : {numberOfVertices : Nat} →
  List (Fin numberOfVertices) → List (Fin numberOfVertices) → List Nat
relativeVertexOrder referenceOrder comparedOrder =
  map (λ currentVertex → positionOfVertex currentVertex referenceOrder)
    comparedOrder

complementPermutationIsOdd : Nat →
  Embeddings.FaceEmbedding dimension simplex_count →
  Embeddings.FaceEmbedding dimension simplex_count → Bool
complementPermutationIsOdd faceDimension previousEmbedding returnedEmbedding =
  Components.oddPermutationImages
    (relativeVertexOrder
      (dropElements (suc faceDimension)
        (Embeddings.ordered_simplex_vertices previousEmbedding))
      (dropElements (suc faceDimension)
        (Embeddings.ordered_simplex_vertices returnedEmbedding)))

codimensionTwoIdentificationFailure : Bool →
  Embeddings.FaceEmbedding dimension simplex_count →
  Embeddings.FaceEmbedding dimension simplex_count → Bool
codimensionTwoIdentificationFailure false previousEmbedding returnedEmbedding =
  false
codimensionTwoIdentificationFailure true previousEmbedding returnedEmbedding =
  not (vertexListsEqual
    (Embeddings.ordered_simplex_vertices previousEmbedding)
    (Embeddings.ordered_simplex_vertices returnedEmbedding))

identificationFailureByKind : FaceCodimensionKind → Nat → Nat →
  Embeddings.FaceEmbedding dimension simplex_count →
  Embeddings.FaceEmbedding dimension simplex_count → Bool
identificationFailureByKind codimension_one simplexDimension faceDimension
  previousEmbedding returnedEmbedding = false
identificationFailureByKind codimension_two simplexDimension faceDimension
  previousEmbedding returnedEmbedding =
  codimensionTwoIdentificationFailure
    (less_than 2 simplexDimension) previousEmbedding returnedEmbedding
identificationFailureByKind codimension_greater_than_two simplexDimension
  faceDimension previousEmbedding returnedEmbedding =
  not (Embeddings.prefixVerticesEqual (suc faceDimension)
    (Embeddings.ordered_simplex_vertices previousEmbedding)
    (Embeddings.ordered_simplex_vertices returnedEmbedding))
identificationFailureByKind invalid_codimension simplexDimension faceDimension
  previousEmbedding returnedEmbedding = false

identificationFailureOnReturn : Nat → Nat →
  Embeddings.FaceEmbedding dimension simplex_count →
  Embeddings.FaceEmbedding dimension simplex_count → Bool
identificationFailureOnReturn simplexDimension faceDimension
  previousEmbedding returnedEmbedding =
  identificationFailureByKind
    (faceCodimensionKind simplexDimension faceDimension)
    simplexDimension faceDimension previousEmbedding returnedEmbedding

linkOrientationFailureByKind : FaceCodimensionKind → Nat →
  Embeddings.FaceEmbedding dimension simplex_count →
  Embeddings.FaceEmbedding dimension simplex_count → Bool
linkOrientationFailureByKind codimension_one faceDimension
  previousEmbedding returnedEmbedding = false
linkOrientationFailureByKind codimension_two faceDimension
  previousEmbedding returnedEmbedding = false
linkOrientationFailureByKind codimension_greater_than_two faceDimension
  previousEmbedding returnedEmbedding =
  complementPermutationIsOdd faceDimension previousEmbedding returnedEmbedding
linkOrientationFailureByKind invalid_codimension faceDimension
  previousEmbedding returnedEmbedding = false

linkOrientationFailureOnReturn : Nat → Nat →
  Embeddings.FaceEmbedding dimension simplex_count →
  Embeddings.FaceEmbedding dimension simplex_count → Bool
linkOrientationFailureOnReturn simplexDimension faceDimension
  previousEmbedding returnedEmbedding =
  linkOrientationFailureByKind
    (faceCodimensionKind simplexDimension faceDimension)
    faceDimension previousEmbedding returnedEmbedding

record FaceLinkTraversal (dimension simplex_count : Nat) : Set where
  constructor face_link_traversal
  field
    reached_link_embeddings :
      List (Embeddings.FaceEmbedding dimension simplex_count)
    pending_link_embeddings :
      List (Embeddings.FaceEmbedding dimension simplex_count)
    bad_identification_seen : Bool
    nonorientable_return_seen : Bool
open FaceLinkTraversal public

observeFaceLinkReturn : (simplexDimension faceDimension : Nat) →
  {numberOfSimplices : Nat} →
  FaceLinkTraversal simplexDimension numberOfSimplices →
  Embeddings.FaceEmbedding simplexDimension numberOfSimplices →
  Maybe (Embeddings.FaceEmbedding simplexDimension numberOfSimplices) →
  FaceLinkTraversal simplexDimension numberOfSimplices
observeFaceLinkReturn simplexDimension faceDimension currentTraversal
  returnedEmbedding nothing = face_link_traversal
  (appendElement (reached_link_embeddings currentTraversal) returnedEmbedding)
  (appendElement (pending_link_embeddings currentTraversal) returnedEmbedding)
  (bad_identification_seen currentTraversal)
  (nonorientable_return_seen currentTraversal)
observeFaceLinkReturn simplexDimension faceDimension currentTraversal
  returnedEmbedding (just previousEmbedding) = face_link_traversal
  (reached_link_embeddings currentTraversal)
  (pending_link_embeddings currentTraversal)
  (bad_identification_seen currentTraversal or
    identificationFailureOnReturn simplexDimension faceDimension
      previousEmbedding returnedEmbedding)
  (nonorientable_return_seen currentTraversal or
    linkOrientationFailureOnReturn simplexDimension faceDimension
      previousEmbedding returnedEmbedding)

observeFaceLinkEmbedding : (simplexDimension faceDimension : Nat) →
  {numberOfSimplices : Nat} →
  FaceLinkTraversal simplexDimension numberOfSimplices →
  Embeddings.FaceEmbedding simplexDimension numberOfSimplices →
  FaceLinkTraversal simplexDimension numberOfSimplices
observeFaceLinkEmbedding simplexDimension faceDimension currentTraversal
  returnedEmbedding =
  observeFaceLinkReturn simplexDimension faceDimension currentTraversal
    returnedEmbedding
    (Embeddings.findEmbeddingForFace
      (Embeddings.embedded_local_face returnedEmbedding)
      (reached_link_embeddings currentTraversal))

processFaceLinkExit : (simplexDimension faceDimension : Nat) →
  {numberOfSimplices : Nat} →
  Triangulation simplexDimension numberOfSimplices →
  FaceLinkTraversal simplexDimension numberOfSimplices →
  Embeddings.FaceEmbedding simplexDimension numberOfSimplices →
  Fin (suc simplexDimension) →
  FaceLinkTraversal simplexDimension numberOfSimplices
processFaceLinkExit simplexDimension faceDimension currentTriangulation
  currentTraversal sourceEmbedding exitFacet
  with crossFaceLinkEmbedding simplexDimension faceDimension
    currentTriangulation sourceEmbedding exitFacet
... | nothing = currentTraversal
... | just returnedEmbedding =
  observeFaceLinkEmbedding simplexDimension faceDimension currentTraversal
    returnedEmbedding

processFaceLinkExits : (simplexDimension faceDimension : Nat) →
  {numberOfSimplices : Nat} →
  Triangulation simplexDimension numberOfSimplices →
  FaceLinkTraversal simplexDimension numberOfSimplices →
  Embeddings.FaceEmbedding simplexDimension numberOfSimplices →
  List (Fin (suc simplexDimension)) →
  FaceLinkTraversal simplexDimension numberOfSimplices
processFaceLinkExits simplexDimension faceDimension currentTriangulation
  currentTraversal sourceEmbedding [] = currentTraversal
processFaceLinkExits simplexDimension faceDimension currentTriangulation
  currentTraversal sourceEmbedding (exitFacet ∷ remainingExitFacets) =
  processFaceLinkExits simplexDimension faceDimension currentTriangulation
    (processFaceLinkExit simplexDimension faceDimension currentTriangulation
      currentTraversal sourceEmbedding exitFacet)
    sourceEmbedding remainingExitFacets

walkFaceLinkQueue : (simplexDimension faceDimension : Nat) →
  {numberOfSimplices : Nat} → Nat →
  Triangulation simplexDimension numberOfSimplices →
  FaceLinkTraversal simplexDimension numberOfSimplices →
  FaceLinkTraversal simplexDimension numberOfSimplices
walkFaceLinkQueue simplexDimension faceDimension zero currentTriangulation
  currentTraversal = currentTraversal
walkFaceLinkQueue simplexDimension faceDimension (suc fuel)
  currentTriangulation currentTraversal
  with pending_link_embeddings currentTraversal
... | [] = currentTraversal
... | sourceEmbedding ∷ remainingQueue =
  walkFaceLinkQueue simplexDimension faceDimension fuel currentTriangulation
    (processFaceLinkExits simplexDimension faceDimension currentTriangulation
      (face_link_traversal
        (reached_link_embeddings currentTraversal)
        remainingQueue
        (bad_identification_seen currentTraversal)
        (nonorientable_return_seen currentTraversal))
      sourceEmbedding (all_fin (suc simplexDimension)))

record FaceLinkClass (dimension simplex_count : Nat) : Set where
  constructor face_link_class
  field
    face_link_embeddings :
      List (Embeddings.FaceEmbedding dimension simplex_count)
    face_has_bad_identification : Bool
    face_link_is_orientable : Bool
open FaceLinkClass public

faceLinkClassFromSeed : (simplexDimension faceDimension : Nat) →
  {numberOfSimplices : Nat} → Nat →
  Triangulation simplexDimension numberOfSimplices →
  LocalFace simplexDimension numberOfSimplices →
  FaceLinkClass simplexDimension numberOfSimplices
faceLinkClassFromSeed simplexDimension faceDimension fuel
  currentTriangulation seedFace
  with Embeddings.initialFaceEmbedding seedFace
... | firstEmbedding
  with walkFaceLinkQueue simplexDimension faceDimension fuel
    currentTriangulation
    (face_link_traversal
      (firstEmbedding ∷ []) (firstEmbedding ∷ []) false false)
... | completedTraversal = face_link_class
  (reached_link_embeddings completedTraversal)
  (bad_identification_seen completedTraversal)
  (not (nonorientable_return_seen completedTraversal))

faceReachedByLinkEmbeddings : LocalFace dimension simplex_count →
  List (Embeddings.FaceEmbedding dimension simplex_count) → Bool
faceReachedByLinkEmbeddings targetFace [] = false
faceReachedByLinkEmbeddings targetFace
  (currentEmbedding ∷ remainingEmbeddings) =
  local_face_equal targetFace
    (Embeddings.embedded_local_face currentEmbedding) or
  faceReachedByLinkEmbeddings targetFace remainingEmbeddings

removeFacesReachedByLinkClass :
  List (Embeddings.FaceEmbedding dimension simplex_count) →
  List (LocalFace dimension simplex_count) →
  List (LocalFace dimension simplex_count)
removeFacesReachedByLinkClass reachedEmbeddings [] = []
removeFacesReachedByLinkClass reachedEmbeddings
  (currentFace ∷ remainingFaces)
  with faceReachedByLinkEmbeddings currentFace reachedEmbeddings
... | true = removeFacesReachedByLinkClass reachedEmbeddings remainingFaces
... | false = currentFace ∷
  removeFacesReachedByLinkClass reachedEmbeddings remainingFaces

partitionFaceLinkClasses : (simplexDimension faceDimension : Nat) →
  {numberOfSimplices : Nat} → Nat →
  Triangulation simplexDimension numberOfSimplices →
  List (LocalFace simplexDimension numberOfSimplices) →
  List (LocalFace simplexDimension numberOfSimplices) →
  List (FaceLinkClass simplexDimension numberOfSimplices)
partitionFaceLinkClasses simplexDimension faceDimension zero
  currentTriangulation faceUniverse remainingFaces = []
partitionFaceLinkClasses simplexDimension faceDimension (suc fuel)
  currentTriangulation faceUniverse [] = []
partitionFaceLinkClasses simplexDimension faceDimension (suc fuel)
  currentTriangulation faceUniverse (seedFace ∷ remainingFaces)
  with faceLinkClassFromSeed simplexDimension faceDimension
    (length faceUniverse) currentTriangulation seedFace
... | discoveredClass = discoveredClass ∷
  partitionFaceLinkClasses simplexDimension faceDimension fuel
    currentTriangulation faceUniverse
    (removeFacesReachedByLinkClass
      (face_link_embeddings discoveredClass) remainingFaces)

faceLinkClasses : Triangulation dimension simplex_count → Nat →
  List (FaceLinkClass dimension simplex_count)
faceLinkClasses {dimension} {simplex_count} currentTriangulation faceDimension
  with local_faces dimension simplex_count faceDimension
... | faceUniverse = partitionFaceLinkClasses dimension faceDimension
  (length faceUniverse) currentTriangulation faceUniverse faceUniverse

faceLinkClassDegrees : Triangulation dimension simplex_count → Nat → List Nat
faceLinkClassDegrees currentTriangulation faceDimension =
  map (λ discoveredClass → length (face_link_embeddings discoveredClass))
    (faceLinkClasses currentTriangulation faceDimension)

badIdentificationCount : Triangulation dimension simplex_count → Nat → Nat
badIdentificationCount currentTriangulation faceDimension =
  count_matching face_has_bad_identification
    (faceLinkClasses currentTriangulation faceDimension)

nonorientableFaceLinkCount :
  Triangulation dimension simplex_count → Nat → Nat
nonorientableFaceLinkCount currentTriangulation faceDimension =
  count_matching
    (λ discoveredClass → not (face_link_is_orientable discoveredClass))
    (faceLinkClasses currentTriangulation faceDimension)

hasBadIdentification : Triangulation dimension simplex_count → Nat → Bool
hasBadIdentification currentTriangulation faceDimension =
  any face_has_bad_identification
    (faceLinkClasses currentTriangulation faceDimension)

allFaceLinksOrientable : Triangulation dimension simplex_count → Nat → Bool
allFaceLinksOrientable currentTriangulation faceDimension =
  all face_link_is_orientable
    (faceLinkClasses currentTriangulation faceDimension)
