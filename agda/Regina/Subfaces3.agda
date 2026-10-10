{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- Dimension-three subface lookup and inherent-vertex mappings.
-- Derived from Face::face() and Face::faceMapping() in
-- engine/triangulation/face.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.Subfaces3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks hiding (positionOfVertex)
import Regina.Embeddings as Embeddings
import Regina.Link3 as Link3

private
  variable
    simplex_count : Nat

lookupList : {element : Set} → Nat → List element → Maybe element
lookupList zero [] = nothing
lookupList zero (headElement ∷ tailElements) = just headElement
lookupList (suc requestedIndex) [] = nothing
lookupList (suc requestedIndex) (headElement ∷ tailElements) =
  lookupList requestedIndex tailElements

takeElements : {element : Set} → Nat → List element → List element
takeElements zero elements = []
takeElements (suc requestedLength) [] = []
takeElements (suc requestedLength) (headElement ∷ tailElements) =
  headElement ∷ takeElements requestedLength tailElements

natMember : Nat → List Nat → Bool
natMember targetValue [] = false
natMember targetValue (candidateValue ∷ remainingValues) =
  nat_equal targetValue candidateValue or
  natMember targetValue remainingValues

finMember : {numberOfElements : Nat} → Fin numberOfElements →
  List (Fin numberOfElements) → Bool
finMember targetVertex [] = false
finMember targetVertex (candidateVertex ∷ remainingVertices) =
  fin_equal targetVertex candidateVertex or
  finMember targetVertex remainingVertices

filterNatsNotUsed : List Nat → List Nat → List Nat
filterNatsNotUsed usedValues [] = []
filterNatsNotUsed usedValues (candidateValue ∷ remainingValues)
  with natMember candidateValue usedValues
... | true = filterNatsNotUsed usedValues remainingValues
... | false = candidateValue ∷
  filterNatsNotUsed usedValues remainingValues

allFourVertexNumbers : List Nat
allFourVertexNumbers = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

completeMappingFromActiveImages : List Nat → Maybe (Permutation 4)
completeMappingFromActiveImages activeImages = from_image_list 4
  (activeImages ++ filterNatsNotUsed activeImages allFourVertexNumbers)

positionOfVertexFrom : Nat → Fin 4 → List (Fin 4) → Maybe Nat
positionOfVertexFrom currentPosition targetVertex [] = nothing
positionOfVertexFrom currentPosition targetVertex
  (candidateVertex ∷ remainingVertices)
  with fin_equal targetVertex candidateVertex
... | true = just currentPosition
... | false = positionOfVertexFrom (suc currentPosition)
  targetVertex remainingVertices

positionOfVertex : Fin 4 → List (Fin 4) → Maybe Nat
positionOfVertex targetVertex vertices =
  positionOfVertexFrom zero targetVertex vertices

mapVerticesToPositions : List (Fin 4) → List (Fin 4) →
  Maybe (List Nat)
mapVerticesToPositions [] containingVertices = just []
mapVerticesToPositions (currentVertex ∷ remainingVertices)
  containingVertices
  with positionOfVertex currentVertex containingVertices |
       mapVerticesToPositions remainingVertices containingVertices
... | just currentPosition | just remainingPositions =
  just (currentPosition ∷ remainingPositions)
... | nothing | _ = nothing
... | just currentPosition | nothing = nothing

naturalRange : Nat → List Nat
naturalRange numberOfElements =
  map fin_to_nat (all_fin numberOfElements)

faceMaskFromVertices : List (Fin 4) → Vector Bool 4
faceMaskFromVertices selectedVertices = tabulate_vector 4
  (λ localVertex → finMember localVertex selectedVertices)

localFaceFromVertices : Fin simplex_count → List (Fin 4) →
  LocalFace 3 simplex_count
localFaceFromVertices simplexIndex selectedVertices =
  local_face simplexIndex (faceMaskFromVertices selectedVertices)

firstClassEmbedding : FaceLinkClass 3 simplex_count →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count)
firstClassEmbedding currentClass
  with face_link_embeddings currentClass
... | [] = nothing
... | firstEmbedding ∷ remainingEmbeddings = just firstEmbedding

representativeEmbedding : Nat → List (FaceLinkClass 3 simplex_count) →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count)
representativeEmbedding classNumber classes
  with lookupList classNumber classes
... | nothing = nothing
... | just currentClass = firstClassEmbedding currentClass

record IndexedFaceOccurrence3 (simplex_count : Nat) : Set where
  constructor indexed_face_occurrence_three
  field
    occurrence_face_class_number : Nat
    occurrence_face_embedding : Embeddings.FaceEmbedding 3 simplex_count
open IndexedFaceOccurrence3 public

findIndexedOccurrenceFrom : Nat → LocalFace 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) →
  Maybe (IndexedFaceOccurrence3 simplex_count)
findIndexedOccurrenceFrom currentClassNumber targetFace [] = nothing
findIndexedOccurrenceFrom currentClassNumber targetFace
  (currentClass ∷ remainingClasses)
  with Embeddings.findEmbeddingForFace targetFace
    (face_link_embeddings currentClass)
... | just matchingEmbedding = just
  (indexed_face_occurrence_three currentClassNumber matchingEmbedding)
... | nothing = findIndexedOccurrenceFrom (suc currentClassNumber)
  targetFace remainingClasses

findIndexedOccurrence : LocalFace 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) →
  Maybe (IndexedFaceOccurrence3 simplex_count)
findIndexedOccurrence targetFace classes =
  findIndexedOccurrenceFrom zero targetFace classes

record SubfaceReference3 : Set where
  constructor subface_reference_three
  field
    referenced_face_dimension : Nat
    referenced_face_class_number : Nat
    referenced_face_mapping : Permutation 4
open SubfaceReference3 public

referenceMappingImages : SubfaceReference3 → List Nat
referenceMappingImages currentReference =
  image_table (referenced_face_mapping currentReference)

referenceActiveImages : SubfaceReference3 → List Nat
referenceActiveImages currentReference = takeElements
  (suc (referenced_face_dimension currentReference))
  (referenceMappingImages currentReference)

buildReferenceAfterMapping : Nat → IndexedFaceOccurrence3 simplex_count →
  Maybe (Permutation 4) → Maybe SubfaceReference3
buildReferenceAfterMapping lowerFaceDimension indexedOccurrence nothing = nothing
buildReferenceAfterMapping lowerFaceDimension indexedOccurrence
  (just completedMapping) = just (subface_reference_three
  lowerFaceDimension
  (occurrence_face_class_number indexedOccurrence)
  completedMapping)

buildReferenceAfterPositions : Nat → IndexedFaceOccurrence3 simplex_count →
  Maybe (List Nat) → Maybe SubfaceReference3
buildReferenceAfterPositions lowerFaceDimension indexedOccurrence nothing = nothing
buildReferenceAfterPositions lowerFaceDimension indexedOccurrence
  (just activeImages) = buildReferenceAfterMapping lowerFaceDimension
  indexedOccurrence (completeMappingFromActiveImages activeImages)

buildReferenceAfterOccurrence : Nat → List (Fin 4) →
  Maybe (IndexedFaceOccurrence3 simplex_count) → Maybe SubfaceReference3
buildReferenceAfterOccurrence lowerFaceDimension containingVertices nothing = nothing
buildReferenceAfterOccurrence lowerFaceDimension containingVertices
  (just indexedOccurrence) = buildReferenceAfterPositions lowerFaceDimension
  indexedOccurrence
  (mapVerticesToPositions lowerFaceVertices containingVertices)
  where
  lowerFaceVertices : List (Fin 4)
  lowerFaceVertices = takeElements (suc lowerFaceDimension)
    (Embeddings.ordered_simplex_vertices
      (occurrence_face_embedding indexedOccurrence))

subfaceReferenceFromVertices : Nat →
  List (FaceLinkClass 3 simplex_count) →
  Embeddings.FaceEmbedding 3 simplex_count → List (Fin 4) →
  Maybe SubfaceReference3
subfaceReferenceFromVertices lowerFaceDimension lowerFaceClasses
  containingEmbedding selectedLocalVertices = buildReferenceAfterOccurrence
  lowerFaceDimension containingVertices
  (findIndexedOccurrence targetFace lowerFaceClasses)
  where
  containingVertices : List (Fin 4)
  containingVertices = takeElements
    (true_count (face_vertices
      (Embeddings.embedded_local_face containingEmbedding)))
    (Embeddings.ordered_simplex_vertices containingEmbedding)

  targetFace : LocalFace 3 simplex_count
  targetFace = localFaceFromVertices
    (face_simplex (Embeddings.embedded_local_face containingEmbedding))
    selectedLocalVertices

singleVertexSelection : Nat → List (Fin 4) → Maybe (List (Fin 4))
singleVertexSelection vertexNumber containingVertices
  with lookupList vertexNumber containingVertices
... | nothing = nothing
... | just selectedVertex = just (selectedVertex ∷ [])

triangleEdgeSelection : Nat → List (Fin 4) → Maybe (List (Fin 4))
triangleEdgeSelection edgeNumber
  (vertexZero ∷ vertexOne ∷ vertexTwo ∷ remainingVertices)
  with edgeNumber
... | zero = just (vertexOne ∷ vertexTwo ∷ [])
... | suc zero = just (vertexZero ∷ vertexTwo ∷ [])
... | suc (suc zero) = just (vertexZero ∷ vertexOne ∷ [])
... | suc (suc (suc remainingNumber)) = nothing
triangleEdgeSelection edgeNumber vertices = nothing

referenceAfterSelection : Nat →
  List (FaceLinkClass 3 simplex_count) →
  Embeddings.FaceEmbedding 3 simplex_count →
  Maybe (List (Fin 4)) → Maybe SubfaceReference3
referenceAfterSelection lowerFaceDimension lowerFaceClasses
  containingEmbedding nothing = nothing
referenceAfterSelection lowerFaceDimension lowerFaceClasses
  containingEmbedding (just selectedVertices) =
  subfaceReferenceFromVertices lowerFaceDimension lowerFaceClasses
    containingEmbedding selectedVertices

edgeVertexReference : Triangulation 3 simplex_count → Nat → Nat →
  Maybe SubfaceReference3
edgeVertexReference currentTriangulation edgeClassNumber vertexNumber
  with representativeEmbedding edgeClassNumber
    (faceLinkClasses currentTriangulation 1)
... | nothing = nothing
... | just edgeEmbedding = referenceAfterSelection 0
  (faceLinkClasses currentTriangulation 0)
  edgeEmbedding
  (singleVertexSelection vertexNumber
    (takeElements 2 (Embeddings.ordered_simplex_vertices edgeEmbedding)))

triangleVertexReference : Triangulation 3 simplex_count → Nat → Nat →
  Maybe SubfaceReference3
triangleVertexReference currentTriangulation triangleClassNumber vertexNumber
  with representativeEmbedding triangleClassNumber
    (faceLinkClasses currentTriangulation 2)
... | nothing = nothing
... | just triangleEmbedding = referenceAfterSelection 0
  (faceLinkClasses currentTriangulation 0)
  triangleEmbedding
  (singleVertexSelection vertexNumber
    (takeElements 3
      (Embeddings.ordered_simplex_vertices triangleEmbedding)))

triangleEdgeReference : Triangulation 3 simplex_count → Nat → Nat →
  Maybe SubfaceReference3
triangleEdgeReference currentTriangulation triangleClassNumber edgeNumber
  with representativeEmbedding triangleClassNumber
    (faceLinkClasses currentTriangulation 2)
... | nothing = nothing
... | just triangleEmbedding = referenceAfterSelection 1
  (faceLinkClasses currentTriangulation 1)
  triangleEmbedding
  (triangleEdgeSelection edgeNumber
    (takeElements 3
      (Embeddings.ordered_simplex_vertices triangleEmbedding)))

edgeVertexReferences : Triangulation 3 simplex_count → Nat →
  List (Maybe SubfaceReference3)
edgeVertexReferences currentTriangulation edgeClassNumber =
  edgeVertexReference currentTriangulation edgeClassNumber 0 ∷
  edgeVertexReference currentTriangulation edgeClassNumber 1 ∷ []

triangleVertexReferences : Triangulation 3 simplex_count → Nat →
  List (Maybe SubfaceReference3)
triangleVertexReferences currentTriangulation triangleClassNumber =
  triangleVertexReference currentTriangulation triangleClassNumber 0 ∷
  triangleVertexReference currentTriangulation triangleClassNumber 1 ∷
  triangleVertexReference currentTriangulation triangleClassNumber 2 ∷ []

triangleEdgeReferences : Triangulation 3 simplex_count → Nat →
  List (Maybe SubfaceReference3)
triangleEdgeReferences currentTriangulation triangleClassNumber =
  triangleEdgeReference currentTriangulation triangleClassNumber 0 ∷
  triangleEdgeReference currentTriangulation triangleClassNumber 1 ∷
  triangleEdgeReference currentTriangulation triangleClassNumber 2 ∷ []

allEdgeVertexReferences : Triangulation 3 simplex_count →
  List (List (Maybe SubfaceReference3))
allEdgeVertexReferences currentTriangulation = map
  (edgeVertexReferences currentTriangulation)
  (naturalRange (length (faceLinkClasses currentTriangulation 1)))

allTriangleVertexReferences : Triangulation 3 simplex_count →
  List (List (Maybe SubfaceReference3))
allTriangleVertexReferences currentTriangulation = map
  (triangleVertexReferences currentTriangulation)
  (naturalRange (length (faceLinkClasses currentTriangulation 2)))

allTriangleEdgeReferences : Triangulation 3 simplex_count →
  List (List (Maybe SubfaceReference3))
allTriangleEdgeReferences currentTriangulation = map
  (triangleEdgeReferences currentTriangulation)
  (naturalRange (length (faceLinkClasses currentTriangulation 2)))

referenceResolved : Maybe SubfaceReference3 → Bool
referenceResolved nothing = false
referenceResolved (just currentReference) = true

referenceRowsResolved : List (List (Maybe SubfaceReference3)) → Bool
referenceRowsResolved rows = all (all referenceResolved) rows

edgeVertexReferencesResolved : Triangulation 3 simplex_count → Bool
edgeVertexReferencesResolved currentTriangulation =
  referenceRowsResolved (allEdgeVertexReferences currentTriangulation)

triangleVertexReferencesResolved : Triangulation 3 simplex_count → Bool
triangleVertexReferencesResolved currentTriangulation =
  referenceRowsResolved (allTriangleVertexReferences currentTriangulation)

triangleEdgeReferencesResolved : Triangulation 3 simplex_count → Bool
triangleEdgeReferencesResolved currentTriangulation =
  referenceRowsResolved (allTriangleEdgeReferences currentTriangulation)

singleImageMatches : Nat → Maybe SubfaceReference3 → Bool
singleImageMatches expectedImage nothing = false
singleImageMatches expectedImage (just currentReference)
  with referenceActiveImages currentReference
... | actualImage ∷ [] = nat_equal actualImage expectedImage
... | actualImages = false

pairImagesMatch : Nat → Nat → Maybe SubfaceReference3 → Bool
pairImagesMatch firstExpected secondExpected nothing = false
pairImagesMatch firstExpected secondExpected (just currentReference)
  with referenceActiveImages currentReference
... | firstActual ∷ secondActual ∷ [] =
  (nat_equal firstActual firstExpected and
   nat_equal secondActual secondExpected) or
  (nat_equal firstActual secondExpected and
   nat_equal secondActual firstExpected)
... | actualImages = false

edgeVertexNumberingValid : Triangulation 3 simplex_count → Nat → Bool
edgeVertexNumberingValid currentTriangulation edgeClassNumber =
  singleImageMatches 0
    (edgeVertexReference currentTriangulation edgeClassNumber 0) and
  singleImageMatches 1
    (edgeVertexReference currentTriangulation edgeClassNumber 1)

allEdgeVertexNumberingValid : Triangulation 3 simplex_count → Bool
allEdgeVertexNumberingValid currentTriangulation = all
  (edgeVertexNumberingValid currentTriangulation)
  (naturalRange (length (faceLinkClasses currentTriangulation 1)))

triangleVertexNumberingValid : Triangulation 3 simplex_count → Nat → Bool
triangleVertexNumberingValid currentTriangulation triangleClassNumber =
  singleImageMatches 0
    (triangleVertexReference currentTriangulation triangleClassNumber 0) and
  singleImageMatches 1
    (triangleVertexReference currentTriangulation triangleClassNumber 1) and
  singleImageMatches 2
    (triangleVertexReference currentTriangulation triangleClassNumber 2)

allTriangleVertexNumberingValid : Triangulation 3 simplex_count → Bool
allTriangleVertexNumberingValid currentTriangulation = all
  (triangleVertexNumberingValid currentTriangulation)
  (naturalRange (length (faceLinkClasses currentTriangulation 2)))

triangleEdgeNumberingValid : Triangulation 3 simplex_count → Nat → Bool
triangleEdgeNumberingValid currentTriangulation triangleClassNumber =
  pairImagesMatch 1 2
    (triangleEdgeReference currentTriangulation triangleClassNumber 0) and
  pairImagesMatch 0 2
    (triangleEdgeReference currentTriangulation triangleClassNumber 1) and
  pairImagesMatch 0 1
    (triangleEdgeReference currentTriangulation triangleClassNumber 2)

allTriangleEdgeNumberingValid : Triangulation 3 simplex_count → Bool
allTriangleEdgeNumberingValid currentTriangulation = all
  (triangleEdgeNumberingValid currentTriangulation)
  (naturalRange (length (faceLinkClasses currentTriangulation 2)))

referenceTargetsClass : Nat → Maybe SubfaceReference3 → Bool
referenceTargetsClass requestedClass nothing = false
referenceTargetsClass requestedClass (just currentReference) = nat_equal
  requestedClass (referenced_face_class_number currentReference)

containsClass : Nat → List (Maybe SubfaceReference3) → Bool
containsClass requestedClass references = any
  (referenceTargetsClass requestedClass) references

edgeContainsVertexClass : Triangulation 3 simplex_count → Nat → Nat → Bool
edgeContainsVertexClass currentTriangulation edgeClassNumber vertexClassNumber =
  containsClass vertexClassNumber
    (edgeVertexReferences currentTriangulation edgeClassNumber)

triangleContainsVertexClass : Triangulation 3 simplex_count → Nat → Nat → Bool
triangleContainsVertexClass currentTriangulation triangleClassNumber
  vertexClassNumber = containsClass vertexClassNumber
  (triangleVertexReferences currentTriangulation triangleClassNumber)

triangleContainsEdgeClass : Triangulation 3 simplex_count → Nat → Nat → Bool
triangleContainsEdgeClass currentTriangulation triangleClassNumber edgeClassNumber =
  containsClass edgeClassNumber
    (triangleEdgeReferences currentTriangulation triangleClassNumber)

countReferencesToClass : Nat → List (Maybe SubfaceReference3) → Nat
countReferencesToClass requestedClass [] = zero
countReferencesToClass requestedClass (nothing ∷ remainingReferences) =
  countReferencesToClass requestedClass remainingReferences
countReferencesToClass requestedClass
  (just currentReference ∷ remainingReferences)
  with nat_equal requestedClass
    (referenced_face_class_number currentReference)
... | true = suc (countReferencesToClass requestedClass remainingReferences)
... | false = countReferencesToClass requestedClass remainingReferences

countReferenceRowsToClass : Nat →
  List (List (Maybe SubfaceReference3)) → Nat
countReferenceRowsToClass requestedClass [] = zero
countReferenceRowsToClass requestedClass
  (currentRow ∷ remainingRows) =
  countReferencesToClass requestedClass currentRow +
  countReferenceRowsToClass requestedClass remainingRows

incidenceCounts : Nat → List (List (Maybe SubfaceReference3)) → List Nat
incidenceCounts targetClassCount referenceRows = map
  (λ requestedClass → countReferenceRowsToClass requestedClass referenceRows)
  (naturalRange targetClassCount)

edgeVertexIncidenceCounts : Triangulation 3 simplex_count → List Nat
edgeVertexIncidenceCounts currentTriangulation = incidenceCounts
  (length (faceLinkClasses currentTriangulation 0))
  (allEdgeVertexReferences currentTriangulation)

triangleVertexIncidenceCounts : Triangulation 3 simplex_count → List Nat
triangleVertexIncidenceCounts currentTriangulation = incidenceCounts
  (length (faceLinkClasses currentTriangulation 0))
  (allTriangleVertexReferences currentTriangulation)

triangleEdgeIncidenceCounts : Triangulation 3 simplex_count → List Nat
triangleEdgeIncidenceCounts currentTriangulation = incidenceCounts
  (length (faceLinkClasses currentTriangulation 1))
  (allTriangleEdgeReferences currentTriangulation)

record EdgeEndpointReport3 : Set where
  constructor edge_endpoint_report_three
  field
    first_endpoint_vertex_class : Nat
    first_endpoint_vertex_image : Nat
    second_endpoint_vertex_class : Nat
    second_endpoint_vertex_image : Nat
open EdgeEndpointReport3 public

singleReferenceData : Maybe SubfaceReference3 → Maybe (List Nat)
singleReferenceData nothing = nothing
singleReferenceData (just currentReference)
  with referenceActiveImages currentReference
... | imageValue ∷ [] = just
  (referenced_face_class_number currentReference ∷ imageValue ∷ [])
... | values = nothing

combineEndpointData : Maybe (List Nat) → Maybe (List Nat) →
  Maybe EdgeEndpointReport3
combineEndpointData (just (firstClass ∷ firstImage ∷ []))
  (just (secondClass ∷ secondImage ∷ [])) = just
  (edge_endpoint_report_three
    firstClass firstImage secondClass secondImage)
combineEndpointData firstData secondData = nothing

edgeEndpointReport : Triangulation 3 simplex_count → Nat →
  Maybe EdgeEndpointReport3
edgeEndpointReport currentTriangulation edgeClassNumber =
  combineEndpointData
    (singleReferenceData
      (edgeVertexReference currentTriangulation edgeClassNumber 0))
    (singleReferenceData
      (edgeVertexReference currentTriangulation edgeClassNumber 1))

edgeIsLoopFromReport : Maybe EdgeEndpointReport3 → Bool
edgeIsLoopFromReport nothing = false
edgeIsLoopFromReport (just currentReport) = nat_equal
  (first_endpoint_vertex_class currentReport)
  (second_endpoint_vertex_class currentReport)

edgeIsLoop : Triangulation 3 simplex_count → Nat → Bool
edgeIsLoop currentTriangulation edgeClassNumber =
  edgeIsLoopFromReport
    (edgeEndpointReport currentTriangulation edgeClassNumber)

edgeLoopFlags : Triangulation 3 simplex_count → List Bool
edgeLoopFlags currentTriangulation = map
  (edgeIsLoop currentTriangulation)
  (naturalRange (length (faceLinkClasses currentTriangulation 1)))
