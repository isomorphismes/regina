{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- Dimension-three Simplex::face() and Simplex::faceMapping() semantics.
-- Derived from engine/triangulation/simplex.h and facenumbering.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.TetrahedronFaces3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks
import Regina.Embeddings as Embeddings
import Regina.SubfaceIncidence3 as Subfaces

private
  variable
    simplex_count : Nat

vertexZero : Fin 4
vertexZero = fzero

vertexOne : Fin 4
vertexOne = fsuc fzero

vertexTwo : Fin 4
vertexTwo = fsuc (fsuc fzero)

vertexThree : Fin 4
vertexThree = fsuc (fsuc (fsuc fzero))

record TetrahedronFaceReference3 : Set where
  constructor tetrahedron_face_reference_three
  field
    tetrahedron_face_dimension : Nat
    tetrahedron_face_class_number : Nat
    tetrahedron_face_mapping : Permutation 4
open TetrahedronFaceReference3 public

tetrahedronFaceMappingImages : TetrahedronFaceReference3 → List Nat
tetrahedronFaceMappingImages currentReference =
  image_table (tetrahedron_face_mapping currentReference)

tetrahedronFaceActiveImages : TetrahedronFaceReference3 → List Nat
tetrahedronFaceActiveImages currentReference = Subfaces.takeElements
  (suc (tetrahedron_face_dimension currentReference))
  (tetrahedronFaceMappingImages currentReference)

referenceAfterMapping : Nat → Subfaces.IndexedOccurrence3 simplex_count →
  Maybe (Permutation 4) → Maybe TetrahedronFaceReference3
referenceAfterMapping faceDimension indexedOccurrence nothing = nothing
referenceAfterMapping faceDimension indexedOccurrence (just currentMapping) =
  just (tetrahedron_face_reference_three
    faceDimension
    (Subfaces.occurrence_class_number indexedOccurrence)
    currentMapping)

referenceAfterOccurrence : Nat →
  Maybe (Subfaces.IndexedOccurrence3 simplex_count) →
  Maybe TetrahedronFaceReference3
referenceAfterOccurrence faceDimension nothing = nothing
referenceAfterOccurrence faceDimension (just indexedOccurrence) =
  referenceAfterMapping faceDimension indexedOccurrence
    (from_image_list 4
      (map fin_to_nat
        (Embeddings.ordered_simplex_vertices
          (Subfaces.occurrence_embedding indexedOccurrence))))

referenceFromSelectedVertices : Triangulation 3 simplex_count → Nat →
  Fin simplex_count → List (Fin 4) → Maybe TetrahedronFaceReference3
referenceFromSelectedVertices currentTriangulation faceDimension
  simplexIndex selectedVertices = referenceAfterOccurrence faceDimension
  (Subfaces.findOccurrence targetFace
    (faceLinkClasses currentTriangulation faceDimension))
  where
  targetFace : LocalFace 3 simplex_count
  targetFace = Subfaces.localFaceFromVertices simplexIndex selectedVertices

referenceAfterInputs : Triangulation 3 simplex_count → Nat →
  Maybe (Fin simplex_count) → Maybe (List (Fin 4)) →
  Maybe TetrahedronFaceReference3
referenceAfterInputs currentTriangulation faceDimension nothing selectedVertices =
  nothing
referenceAfterInputs currentTriangulation faceDimension
  (just simplexIndex) nothing = nothing
referenceAfterInputs currentTriangulation faceDimension
  (just simplexIndex) (just selectedVertices) =
  referenceFromSelectedVertices currentTriangulation faceDimension
    simplexIndex selectedVertices

vertexSelection : Nat → Maybe (List (Fin 4))
vertexSelection zero = just (vertexZero ∷ [])
vertexSelection (suc zero) = just (vertexOne ∷ [])
vertexSelection (suc (suc zero)) = just (vertexTwo ∷ [])
vertexSelection (suc (suc (suc zero))) = just (vertexThree ∷ [])
vertexSelection (suc (suc (suc (suc remaining)))) = nothing

edgeSelection : Nat → Maybe (List (Fin 4))
edgeSelection zero = just (vertexZero ∷ vertexOne ∷ [])
edgeSelection (suc zero) = just (vertexZero ∷ vertexTwo ∷ [])
edgeSelection (suc (suc zero)) = just (vertexZero ∷ vertexThree ∷ [])
edgeSelection (suc (suc (suc zero))) =
  just (vertexOne ∷ vertexTwo ∷ [])
edgeSelection (suc (suc (suc (suc zero)))) =
  just (vertexOne ∷ vertexThree ∷ [])
edgeSelection (suc (suc (suc (suc (suc zero))))) =
  just (vertexTwo ∷ vertexThree ∷ [])
edgeSelection (suc (suc (suc (suc (suc (suc remaining)))))) = nothing

triangleSelection : Nat → Maybe (List (Fin 4))
triangleSelection zero =
  just (vertexOne ∷ vertexTwo ∷ vertexThree ∷ [])
triangleSelection (suc zero) =
  just (vertexZero ∷ vertexTwo ∷ vertexThree ∷ [])
triangleSelection (suc (suc zero)) =
  just (vertexZero ∷ vertexOne ∷ vertexThree ∷ [])
triangleSelection (suc (suc (suc zero))) =
  just (vertexZero ∷ vertexOne ∷ vertexTwo ∷ [])
triangleSelection (suc (suc (suc (suc remaining)))) = nothing

tetrahedronVertexReference : Triangulation 3 simplex_count → Nat → Nat →
  Maybe TetrahedronFaceReference3
tetrahedronVertexReference {simplex_count} currentTriangulation
  simplexNumber vertexNumber = referenceAfterInputs currentTriangulation 0
  (fin_from_nat simplex_count simplexNumber) (vertexSelection vertexNumber)

tetrahedronEdgeReference : Triangulation 3 simplex_count → Nat → Nat →
  Maybe TetrahedronFaceReference3
tetrahedronEdgeReference {simplex_count} currentTriangulation
  simplexNumber edgeNumber = referenceAfterInputs currentTriangulation 1
  (fin_from_nat simplex_count simplexNumber) (edgeSelection edgeNumber)

tetrahedronTriangleReference : Triangulation 3 simplex_count → Nat → Nat →
  Maybe TetrahedronFaceReference3
tetrahedronTriangleReference {simplex_count} currentTriangulation
  simplexNumber triangleNumber = referenceAfterInputs currentTriangulation 2
  (fin_from_nat simplex_count simplexNumber) (triangleSelection triangleNumber)

tetrahedronVertexReferences : Triangulation 3 simplex_count → Nat →
  List (Maybe TetrahedronFaceReference3)
tetrahedronVertexReferences currentTriangulation simplexNumber = map
  (tetrahedronVertexReference currentTriangulation simplexNumber)
  (Subfaces.naturalRange 4)

tetrahedronEdgeReferences : Triangulation 3 simplex_count → Nat →
  List (Maybe TetrahedronFaceReference3)
tetrahedronEdgeReferences currentTriangulation simplexNumber = map
  (tetrahedronEdgeReference currentTriangulation simplexNumber)
  (Subfaces.naturalRange 6)

tetrahedronTriangleReferences : Triangulation 3 simplex_count → Nat →
  List (Maybe TetrahedronFaceReference3)
tetrahedronTriangleReferences currentTriangulation simplexNumber = map
  (tetrahedronTriangleReference currentTriangulation simplexNumber)
  (Subfaces.naturalRange 4)

allTetrahedronVertexReferences : Triangulation 3 simplex_count →
  List (List (Maybe TetrahedronFaceReference3))
allTetrahedronVertexReferences {simplex_count} currentTriangulation = map
  (tetrahedronVertexReferences currentTriangulation)
  (Subfaces.naturalRange simplex_count)

allTetrahedronEdgeReferences : Triangulation 3 simplex_count →
  List (List (Maybe TetrahedronFaceReference3))
allTetrahedronEdgeReferences {simplex_count} currentTriangulation = map
  (tetrahedronEdgeReferences currentTriangulation)
  (Subfaces.naturalRange simplex_count)

allTetrahedronTriangleReferences : Triangulation 3 simplex_count →
  List (List (Maybe TetrahedronFaceReference3))
allTetrahedronTriangleReferences {simplex_count} currentTriangulation = map
  (tetrahedronTriangleReferences currentTriangulation)
  (Subfaces.naturalRange simplex_count)

referenceResolved : Maybe TetrahedronFaceReference3 → Bool
referenceResolved nothing = false
referenceResolved (just currentReference) = true

referenceRowsResolved :
  List (List (Maybe TetrahedronFaceReference3)) → Bool
referenceRowsResolved referenceRows = all (all referenceResolved) referenceRows

allTetrahedronFaceReferencesResolved : Triangulation 3 simplex_count → Bool
allTetrahedronFaceReferencesResolved currentTriangulation =
  referenceRowsResolved
    (allTetrahedronVertexReferences currentTriangulation) and
  referenceRowsResolved
    (allTetrahedronEdgeReferences currentTriangulation) and
  referenceRowsResolved
    (allTetrahedronTriangleReferences currentTriangulation)

natMember : Nat → List Nat → Bool
natMember requestedValue [] = false
natMember requestedValue (currentValue ∷ remainingValues) =
  nat_equal requestedValue currentValue or
  natMember requestedValue remainingValues

sameNatSet : List Nat → List Nat → Bool
sameNatSet firstValues secondValues =
  nat_equal (length firstValues) (length secondValues) and
  all (λ currentValue → natMember currentValue secondValues) firstValues and
  all (λ currentValue → natMember currentValue firstValues) secondValues

selectionMatchesReference : Maybe (List (Fin 4)) →
  Maybe TetrahedronFaceReference3 → Bool
selectionMatchesReference nothing currentReference = false
selectionMatchesReference selectedVertices nothing = false
selectionMatchesReference (just selectedVertices) (just currentReference) =
  sameNatSet
    (map fin_to_nat selectedVertices)
    (tetrahedronFaceActiveImages currentReference)

vertexMappingValid : Triangulation 3 simplex_count → Nat → Nat → Bool
vertexMappingValid currentTriangulation simplexNumber vertexNumber =
  selectionMatchesReference (vertexSelection vertexNumber)
    (tetrahedronVertexReference currentTriangulation
      simplexNumber vertexNumber)

edgeMappingValid : Triangulation 3 simplex_count → Nat → Nat → Bool
edgeMappingValid currentTriangulation simplexNumber edgeNumber =
  selectionMatchesReference (edgeSelection edgeNumber)
    (tetrahedronEdgeReference currentTriangulation simplexNumber edgeNumber)

triangleMappingValid : Triangulation 3 simplex_count → Nat → Nat → Bool
triangleMappingValid currentTriangulation simplexNumber triangleNumber =
  selectionMatchesReference (triangleSelection triangleNumber)
    (tetrahedronTriangleReference currentTriangulation
      simplexNumber triangleNumber)

allTetrahedronMappingsValid : Triangulation 3 simplex_count → Bool
allTetrahedronMappingsValid {simplex_count} currentTriangulation = all
  (λ simplexNumber →
    all (vertexMappingValid currentTriangulation simplexNumber)
      (Subfaces.naturalRange 4) and
    all (edgeMappingValid currentTriangulation simplexNumber)
      (Subfaces.naturalRange 6) and
    all (triangleMappingValid currentTriangulation simplexNumber)
      (Subfaces.naturalRange 4))
  (Subfaces.naturalRange simplex_count)

referenceTargetsClass : Nat → Maybe TetrahedronFaceReference3 → Bool
referenceTargetsClass requestedClass nothing = false
referenceTargetsClass requestedClass (just currentReference) = nat_equal
  requestedClass (tetrahedron_face_class_number currentReference)

countReferencesToClass : Nat →
  List (Maybe TetrahedronFaceReference3) → Nat
countReferencesToClass requestedClass [] = zero
countReferencesToClass requestedClass
  (currentReference ∷ remainingReferences)
  with referenceTargetsClass requestedClass currentReference
... | true = suc (countReferencesToClass requestedClass remainingReferences)
... | false = countReferencesToClass requestedClass remainingReferences

countReferenceRowsToClass : Nat →
  List (List (Maybe TetrahedronFaceReference3)) → Nat
countReferenceRowsToClass requestedClass [] = zero
countReferenceRowsToClass requestedClass
  (currentRow ∷ remainingRows) =
  countReferencesToClass requestedClass currentRow +
  countReferenceRowsToClass requestedClass remainingRows

incidenceCounts : Nat →
  List (List (Maybe TetrahedronFaceReference3)) → List Nat
incidenceCounts targetClassCount referenceRows = map
  (λ requestedClass → countReferenceRowsToClass requestedClass referenceRows)
  (Subfaces.naturalRange targetClassCount)

tetrahedronVertexIncidenceCounts : Triangulation 3 simplex_count → List Nat
tetrahedronVertexIncidenceCounts currentTriangulation = incidenceCounts
  (length (faceLinkClasses currentTriangulation 0))
  (allTetrahedronVertexReferences currentTriangulation)

tetrahedronEdgeIncidenceCounts : Triangulation 3 simplex_count → List Nat
tetrahedronEdgeIncidenceCounts currentTriangulation = incidenceCounts
  (length (faceLinkClasses currentTriangulation 1))
  (allTetrahedronEdgeReferences currentTriangulation)

tetrahedronTriangleIncidenceCounts : Triangulation 3 simplex_count → List Nat
tetrahedronTriangleIncidenceCounts currentTriangulation = incidenceCounts
  (length (faceLinkClasses currentTriangulation 2))
  (allTetrahedronTriangleReferences currentTriangulation)

natListsEqual : List Nat → List Nat → Bool
natListsEqual [] [] = true
natListsEqual [] (headValue ∷ tailValues) = false
natListsEqual (headValue ∷ tailValues) [] = false
natListsEqual (firstHead ∷ firstTail) (secondHead ∷ secondTail) =
  nat_equal firstHead secondHead and natListsEqual firstTail secondTail

tetrahedronIncidencesMatchFaceDegrees :
  Triangulation 3 simplex_count → Bool
tetrahedronIncidencesMatchFaceDegrees currentTriangulation =
  natListsEqual
    (tetrahedronVertexIncidenceCounts currentTriangulation)
    (faceLinkClassDegrees currentTriangulation 0) and
  natListsEqual
    (tetrahedronEdgeIncidenceCounts currentTriangulation)
    (faceLinkClassDegrees currentTriangulation 1) and
  natListsEqual
    (tetrahedronTriangleIncidenceCounts currentTriangulation)
    (faceLinkClassDegrees currentTriangulation 2)

maybeNatEqual : Maybe Nat → Maybe Nat → Bool
maybeNatEqual nothing nothing = true
maybeNatEqual nothing (just rightValue) = false
maybeNatEqual (just leftValue) nothing = false
maybeNatEqual (just leftValue) (just rightValue) =
  nat_equal leftValue rightValue

referenceClassNumber : Maybe TetrahedronFaceReference3 → Maybe Nat
referenceClassNumber nothing = nothing
referenceClassNumber (just currentReference) =
  just (tetrahedron_face_class_number currentReference)

referenceClassRowsEqual :
  List (Maybe TetrahedronFaceReference3) →
  List (Maybe TetrahedronFaceReference3) → Bool
referenceClassRowsEqual [] [] = true
referenceClassRowsEqual [] (rightHead ∷ rightTail) = false
referenceClassRowsEqual (leftHead ∷ leftTail) [] = false
referenceClassRowsEqual (leftHead ∷ leftTail)
  (rightHead ∷ rightTail) =
  maybeNatEqual (referenceClassNumber leftHead)
    (referenceClassNumber rightHead) and
  referenceClassRowsEqual leftTail rightTail

tetrahedronClassTablesEqual : Triangulation 3 simplex_count → Nat → Nat → Bool
tetrahedronClassTablesEqual currentTriangulation firstSimplex secondSimplex =
  referenceClassRowsEqual
    (tetrahedronVertexReferences currentTriangulation firstSimplex)
    (tetrahedronVertexReferences currentTriangulation secondSimplex) and
  referenceClassRowsEqual
    (tetrahedronEdgeReferences currentTriangulation firstSimplex)
    (tetrahedronEdgeReferences currentTriangulation secondSimplex) and
  referenceClassRowsEqual
    (tetrahedronTriangleReferences currentTriangulation firstSimplex)
    (tetrahedronTriangleReferences currentTriangulation secondSimplex)

transportVertexNumber : Permutation 4 → Nat → Maybe Nat
transportVertexNumber currentMapping vertexNumber
  with fin_from_nat 4 vertexNumber
... | nothing = nothing
... | just localVertex = just
  (fin_to_nat (image currentMapping localVertex))

transportVertexNumbers : Permutation 4 → List Nat → Maybe (List Nat)
transportVertexNumbers currentMapping [] = just []
transportVertexNumbers currentMapping (currentVertex ∷ remainingVertices)
  with transportVertexNumber currentMapping currentVertex |
       transportVertexNumbers currentMapping remainingVertices
... | just transportedVertex | just remainingTransported =
  just (transportedVertex ∷ remainingTransported)
... | nothing | _ = nothing
... | just transportedVertex | nothing = nothing

classAndTransportMatch : Permutation 4 →
  Maybe TetrahedronFaceReference3 →
  Maybe TetrahedronFaceReference3 → Bool
classAndTransportMatch currentMapping nothing targetReference = false
classAndTransportMatch currentMapping sourceReference nothing = false
classAndTransportMatch currentMapping (just sourceReference)
  (just targetReference)
  with transportVertexNumbers currentMapping
    (tetrahedronFaceActiveImages sourceReference)
... | nothing = false
... | just transportedImages =
  nat_equal
    (tetrahedron_face_class_number sourceReference)
    (tetrahedron_face_class_number targetReference) and
  natListsEqual transportedImages
    (tetrahedronFaceActiveImages targetReference)

facetCompatibilityAfterLookup : Triangulation 3 simplex_count →
  Fin simplex_count → Fin 4 → Maybe (Gluing 3 simplex_count) → Bool
facetCompatibilityAfterLookup currentTriangulation sourceSimplex sourceFacet
  nothing = true
facetCompatibilityAfterLookup currentTriangulation sourceSimplex sourceFacet
  (just outwardGluing) = classAndTransportMatch
  (vertex_permutation outwardGluing)
  (tetrahedronTriangleReference currentTriangulation
    (fin_to_nat sourceSimplex) (fin_to_nat sourceFacet))
  (tetrahedronTriangleReference currentTriangulation
    (fin_to_nat (adjacent_simplex outwardGluing))
    (fin_to_nat (image (vertex_permutation outwardGluing) sourceFacet)))

facetMappingCompatible : Triangulation 3 simplex_count →
  Fin simplex_count → Fin 4 → Bool
facetMappingCompatible currentTriangulation sourceSimplex sourceFacet =
  facetCompatibilityAfterLookup currentTriangulation sourceSimplex sourceFacet
    (adjacency (raw_state currentTriangulation)
      (facet sourceSimplex sourceFacet))

allFacetMappingsCompatible : Triangulation 3 simplex_count → Bool
allFacetMappingsCompatible {simplex_count} currentTriangulation = all
  (λ sourceSimplex → all
    (facetMappingCompatible currentTriangulation sourceSimplex)
    (all_fin 4))
  (all_fin simplex_count)
