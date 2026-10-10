{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- Explicit two-dimensional vertex-link complexes for dimension three.
-- Derived from engine/triangulation/dim3/vertex3.cpp at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.VertexLinkComplex3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks
import Regina.Embeddings as Embeddings
import Regina.Link3 as Link3

private
  variable
    simplex_count : Nat

filterElements : {element : Set} →
  (element → Bool) → List element → List element
filterElements predicate [] = []
filterElements predicate (headElement ∷ tailElements)
  with predicate headElement
... | true = headElement ∷ filterElements predicate tailElements
... | false = filterElements predicate tailElements

selectedVertex : Embeddings.FaceEmbedding 3 simplex_count → Maybe (Fin 4)
selectedVertex currentOccurrence = find
  (λ localVertex → lookup_vector
    (face_vertices (Embeddings.embedded_local_face currentOccurrence))
    localVertex)
  (all_fin 4)

otherVertices : Embeddings.FaceEmbedding 3 simplex_count → List (Fin 4)
otherVertices currentOccurrence with selectedVertex currentOccurrence
... | nothing = []
... | just selectedLocalVertex = filterElements
  (λ localVertex → not (fin_equal localVertex selectedLocalVertex))
  (all_fin 4)

verticesDifferentFromBoth : Fin 4 → Fin 4 → Fin 4 → Bool
verticesDifferentFromBoth firstExcluded secondExcluded candidateVertex = not
  (fin_equal candidateVertex firstExcluded or
   fin_equal candidateVertex secondExcluded)

sideEndpointVertices : Fin 4 → Fin 4 → List (Fin 4)
sideEndpointVertices selectedLocalVertex exitFacet = filterElements
  (verticesDifferentFromBoth selectedLocalVertex exitFacet) (all_fin 4)

singletonVertexMask : Fin 4 → Vector Bool 4
singletonVertexMask selectedLocalVertex = tabulate_vector 4
  (λ localVertex → fin_equal localVertex selectedLocalVertex)

edgeMask : Fin 4 → Fin 4 → Vector Bool 4
edgeMask firstVertex secondVertex = tabulate_vector 4
  (λ localVertex →
    fin_equal localVertex firstVertex or fin_equal localVertex secondVertex)

localVertexFace : Fin simplex_count → Fin 4 → LocalFace 3 simplex_count
localVertexFace simplexIndex localVertex =
  local_face simplexIndex (singletonVertexMask localVertex)

localEdgeFace : Fin simplex_count → Fin 4 → Fin 4 →
  LocalFace 3 simplex_count
localEdgeFace simplexIndex firstVertex secondVertex =
  local_face simplexIndex (edgeMask firstVertex secondVertex)

findOccurrenceIndexFrom : Nat → LocalFace 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Maybe Nat
findOccurrenceIndexFrom currentIndex targetFace [] = nothing
findOccurrenceIndexFrom currentIndex targetFace
  (currentOccurrence ∷ remainingOccurrences)
  with local_face_equal targetFace
    (Embeddings.embedded_local_face currentOccurrence)
... | true = just currentIndex
... | false = findOccurrenceIndexFrom (suc currentIndex)
  targetFace remainingOccurrences

findOccurrenceIndex : LocalFace 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Maybe Nat
findOccurrenceIndex targetFace triangleOccurrences =
  findOccurrenceIndexFrom zero targetFace triangleOccurrences

record IndexedEdgeClass (simplex_count : Nat) : Set where
  constructor indexed_edge_class
  field
    indexed_edge_number : Nat
    indexed_edge_value : FaceLinkClass 3 simplex_count
open IndexedEdgeClass public

findIndexedEdgeClassFrom : Nat → LocalFace 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) → Maybe (IndexedEdgeClass simplex_count)
findIndexedEdgeClassFrom currentIndex targetEdge [] = nothing
findIndexedEdgeClassFrom currentIndex targetEdge
  (currentEdgeClass ∷ remainingEdgeClasses)
  with any
    (λ currentEmbedding → local_face_equal targetEdge
      (Embeddings.embedded_local_face currentEmbedding))
    (face_link_embeddings currentEdgeClass)
... | true = just (indexed_edge_class currentIndex currentEdgeClass)
... | false = findIndexedEdgeClassFrom (suc currentIndex)
  targetEdge remainingEdgeClasses

findIndexedEdgeClass : LocalFace 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) → Maybe (IndexedEdgeClass simplex_count)
findIndexedEdgeClass targetEdge edgeClasses =
  findIndexedEdgeClassFrom zero targetEdge edgeClasses

findMatchingEdgeEmbedding : LocalFace 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count)
findMatchingEdgeEmbedding targetEdge [] = nothing
findMatchingEdgeEmbedding targetEdge
  (currentEmbedding ∷ remainingEmbeddings)
  with local_face_equal targetEdge
    (Embeddings.embedded_local_face currentEmbedding)
... | true = just currentEmbedding
... | false = findMatchingEdgeEmbedding targetEdge remainingEmbeddings

endpointNumberFromList : Fin 4 → List (Fin 4) → Maybe Nat
endpointNumberFromList selectedLocalVertex [] = nothing
endpointNumberFromList selectedLocalVertex (firstVertex ∷ [])
  with fin_equal selectedLocalVertex firstVertex
... | true = just zero
... | false = nothing
endpointNumberFromList selectedLocalVertex
  (firstVertex ∷ secondVertex ∷ remainingVertices)
  with fin_equal selectedLocalVertex firstVertex
... | true = just zero
... | false with fin_equal selectedLocalVertex secondVertex
...   | true = just (suc zero)
...   | false = nothing

record LinkCornerLabel : Set where
  constructor link_corner_label
  field
    corner_edge_class_number : Nat
    corner_edge_endpoint_number : Nat
open LinkCornerLabel public

cornerLabelEqual : LinkCornerLabel → LinkCornerLabel → Bool
cornerLabelEqual firstLabel secondLabel =
  nat_equal
    (corner_edge_class_number firstLabel)
    (corner_edge_class_number secondLabel) and
  nat_equal
    (corner_edge_endpoint_number firstLabel)
    (corner_edge_endpoint_number secondLabel)

cornerLabelAfterEmbedding : Nat → Fin 4 →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count) → Maybe LinkCornerLabel
cornerLabelAfterEmbedding edgeClassNumber selectedLocalVertex nothing = nothing
cornerLabelAfterEmbedding edgeClassNumber selectedLocalVertex
  (just matchingEmbedding)
  with endpointNumberFromList selectedLocalVertex
    (Embeddings.ordered_simplex_vertices matchingEmbedding)
... | nothing = nothing
... | just endpointNumber =
  just (link_corner_label edgeClassNumber endpointNumber)

cornerLabelAfterEdgeClass : Fin 4 → LocalFace 3 simplex_count →
  Maybe (IndexedEdgeClass simplex_count) → Maybe LinkCornerLabel
cornerLabelAfterEdgeClass selectedLocalVertex targetEdge nothing = nothing
cornerLabelAfterEdgeClass selectedLocalVertex targetEdge
  (just indexedEdgeClass) = cornerLabelAfterEmbedding
  (indexed_edge_number indexedEdgeClass)
  selectedLocalVertex
  (findMatchingEdgeEmbedding targetEdge
    (face_link_embeddings (indexed_edge_value indexedEdgeClass)))

cornerLabelForVertices : List (FaceLinkClass 3 simplex_count) →
  Embeddings.FaceEmbedding 3 simplex_count → Fin 4 → Fin 4 →
  Maybe LinkCornerLabel
cornerLabelForVertices edgeClasses currentOccurrence selectedLocalVertex
  otherLocalVertex = cornerLabelAfterEdgeClass selectedLocalVertex targetEdge
  (findIndexedEdgeClass targetEdge edgeClasses)
  where
  targetEdge : LocalFace 3 simplex_count
  targetEdge = localEdgeFace
    (face_simplex (Embeddings.embedded_local_face currentOccurrence))
    selectedLocalVertex otherLocalVertex

cornerLabelsForVertices : List (FaceLinkClass 3 simplex_count) →
  Embeddings.FaceEmbedding 3 simplex_count → Fin 4 → List (Fin 4) →
  List (Maybe LinkCornerLabel)
cornerLabelsForVertices edgeClasses currentOccurrence selectedLocalVertex
  localVertices = map
  (cornerLabelForVertices edgeClasses currentOccurrence selectedLocalVertex)
  localVertices

cornerLabelsForOccurrence : List (FaceLinkClass 3 simplex_count) →
  Embeddings.FaceEmbedding 3 simplex_count → List (Maybe LinkCornerLabel)
cornerLabelsForOccurrence edgeClasses currentOccurrence
  with selectedVertex currentOccurrence
... | nothing = []
... | just selectedLocalVertex = cornerLabelsForVertices edgeClasses
  currentOccurrence selectedLocalVertex (otherVertices currentOccurrence)

record ExplicitLinkTriangle (simplex_count : Nat) : Set where
  constructor explicit_link_triangle
  field
    explicit_triangle_number : Nat
    explicit_triangle_occurrence :
      Embeddings.FaceEmbedding 3 simplex_count
    explicit_triangle_corner_labels : List (Maybe LinkCornerLabel)
open ExplicitLinkTriangle public

assembleTrianglesFrom : List (FaceLinkClass 3 simplex_count) → Nat →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (ExplicitLinkTriangle simplex_count)
assembleTrianglesFrom edgeClasses nextTriangleNumber [] = []
assembleTrianglesFrom edgeClasses nextTriangleNumber
  (currentOccurrence ∷ remainingOccurrences) =
  explicit_link_triangle nextTriangleNumber currentOccurrence
    (cornerLabelsForOccurrence edgeClasses currentOccurrence) ∷
  assembleTrianglesFrom edgeClasses (suc nextTriangleNumber)
    remainingOccurrences

assembleTriangles : List (FaceLinkClass 3 simplex_count) →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (ExplicitLinkTriangle simplex_count)
assembleTriangles edgeClasses triangleOccurrences =
  assembleTrianglesFrom edgeClasses zero triangleOccurrences

record LinkSideAddress : Set where
  constructor link_side_address
  field
    side_triangle_number : Nat
    side_exit_facet_number : Nat
open LinkSideAddress public

data LinkSideDestination : Set where
  boundary_side : LinkSideDestination
  paired_side : Maybe LinkSideAddress → List Nat → LinkSideDestination

record LinkTriangleSide : Set where
  constructor link_triangle_side
  field
    source_triangle_number : Nat
    source_exit_facet_number : Nat
    source_endpoint_vertex_numbers : List Nat
    destination_side : LinkSideDestination
open LinkTriangleSide public

addressFromTarget : Maybe Nat → Fin 4 → Maybe LinkSideAddress
addressFromTarget nothing targetExitFacet = nothing
addressFromTarget (just targetTriangleNumber) targetExitFacet =
  just (link_side_address targetTriangleNumber (fin_to_nat targetExitFacet))

transportedVertices : Permutation 4 → List (Fin 4) → List Nat
transportedVertices gluingPermutation localVertices = map
  (λ localVertex → fin_to_nat (image gluingPermutation localVertex))
  localVertices

pairedDestination : List (Embeddings.FaceEmbedding 3 simplex_count) →
  Fin 4 → Fin 4 → List (Fin 4) → Gluing 3 simplex_count →
  LinkSideDestination
pairedDestination triangleOccurrences selectedLocalVertex exitFacet
  endpointVertices outwardGluing = paired_side
  (addressFromTarget
    (findOccurrenceIndex
      (localVertexFace
        (adjacent_simplex outwardGluing)
        (image (vertex_permutation outwardGluing) selectedLocalVertex))
      triangleOccurrences)
    (image (vertex_permutation outwardGluing) exitFacet))
  (transportedVertices (vertex_permutation outwardGluing) endpointVertices)

sideDestinationAfterLookup :
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  Fin 4 → Fin 4 → List (Fin 4) → Maybe (Gluing 3 simplex_count) →
  LinkSideDestination
sideDestinationAfterLookup triangleOccurrences selectedLocalVertex exitFacet
  endpointVertices nothing = boundary_side
sideDestinationAfterLookup triangleOccurrences selectedLocalVertex exitFacet
  endpointVertices (just outwardGluing) = pairedDestination
  triangleOccurrences selectedLocalVertex exitFacet endpointVertices outwardGluing

buildOneSide : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Nat →
  Embeddings.FaceEmbedding 3 simplex_count → Fin 4 → Fin 4 →
  LinkTriangleSide
buildOneSide currentTriangulation triangleOccurrences triangleNumber
  currentOccurrence selectedLocalVertex exitFacet = link_triangle_side
  triangleNumber
  (fin_to_nat exitFacet)
  (map fin_to_nat endpointVertices)
  (sideDestinationAfterLookup triangleOccurrences selectedLocalVertex exitFacet
    endpointVertices
    (adjacency (raw_state currentTriangulation)
      (facet
        (face_simplex (Embeddings.embedded_local_face currentOccurrence))
        exitFacet)))
  where
  endpointVertices : List (Fin 4)
  endpointVertices = sideEndpointVertices selectedLocalVertex exitFacet

buildSidesAcrossFacets : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Nat →
  Embeddings.FaceEmbedding 3 simplex_count → Fin 4 → List (Fin 4) →
  List LinkTriangleSide
buildSidesAcrossFacets currentTriangulation triangleOccurrences triangleNumber
  currentOccurrence selectedLocalVertex [] = []
buildSidesAcrossFacets currentTriangulation triangleOccurrences triangleNumber
  currentOccurrence selectedLocalVertex (exitFacet ∷ remainingFacets)
  with fin_equal exitFacet selectedLocalVertex
... | true = buildSidesAcrossFacets currentTriangulation
  triangleOccurrences triangleNumber currentOccurrence selectedLocalVertex
  remainingFacets
... | false = buildOneSide currentTriangulation triangleOccurrences
  triangleNumber currentOccurrence selectedLocalVertex exitFacet ∷
  buildSidesAcrossFacets currentTriangulation triangleOccurrences
    triangleNumber currentOccurrence selectedLocalVertex remainingFacets

buildSidesForOccurrence : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Nat →
  Embeddings.FaceEmbedding 3 simplex_count → List LinkTriangleSide
buildSidesForOccurrence currentTriangulation triangleOccurrences triangleNumber
  currentOccurrence with selectedVertex currentOccurrence
... | nothing = []
... | just selectedLocalVertex = buildSidesAcrossFacets
  currentTriangulation triangleOccurrences triangleNumber currentOccurrence
  selectedLocalVertex (all_fin 4)

buildAllSidesFrom : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Nat →
  List (Embeddings.FaceEmbedding 3 simplex_count) → List LinkTriangleSide
buildAllSidesFrom currentTriangulation allOccurrences nextTriangleNumber [] = []
buildAllSidesFrom currentTriangulation allOccurrences nextTriangleNumber
  (currentOccurrence ∷ remainingOccurrences) =
  buildSidesForOccurrence currentTriangulation allOccurrences
    nextTriangleNumber currentOccurrence ++
  buildAllSidesFrom currentTriangulation allOccurrences
    (suc nextTriangleNumber) remainingOccurrences

buildAllSides : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) → List LinkTriangleSide
buildAllSides currentTriangulation triangleOccurrences =
  buildAllSidesFrom currentTriangulation triangleOccurrences zero
    triangleOccurrences

cornerLabelMember : LinkCornerLabel → List LinkCornerLabel → Bool
cornerLabelMember targetLabel [] = false
cornerLabelMember targetLabel (currentLabel ∷ remainingLabels) =
  cornerLabelEqual targetLabel currentLabel or
  cornerLabelMember targetLabel remainingLabels

insertCornerLabel : LinkCornerLabel → List LinkCornerLabel → List LinkCornerLabel
insertCornerLabel newLabel existingLabels with
  cornerLabelMember newLabel existingLabels
... | true = existingLabels
... | false = newLabel ∷ existingLabels

collectResolvedLabels : List (Maybe LinkCornerLabel) →
  List LinkCornerLabel → List LinkCornerLabel
collectResolvedLabels [] accumulatedLabels = accumulatedLabels
collectResolvedLabels (nothing ∷ remainingLabels) accumulatedLabels =
  collectResolvedLabels remainingLabels accumulatedLabels
collectResolvedLabels (just currentLabel ∷ remainingLabels) accumulatedLabels =
  collectResolvedLabels remainingLabels
    (insertCornerLabel currentLabel accumulatedLabels)

collectTriangleLabels : List (ExplicitLinkTriangle simplex_count) →
  List LinkCornerLabel → List LinkCornerLabel
collectTriangleLabels [] accumulatedLabels = accumulatedLabels
collectTriangleLabels (currentTriangle ∷ remainingTriangles)
  accumulatedLabels = collectTriangleLabels remainingTriangles
  (collectResolvedLabels
    (explicit_triangle_corner_labels currentTriangle) accumulatedLabels)

cornerLabelResolved : Maybe LinkCornerLabel → Bool
cornerLabelResolved nothing = false
cornerLabelResolved (just currentLabel) = true

triangleCornerLabelsResolved : ExplicitLinkTriangle simplex_count → Bool
triangleCornerLabelsResolved currentTriangle = all cornerLabelResolved
  (explicit_triangle_corner_labels currentTriangle)

record ExplicitVertexLink (simplex_count : Nat) : Set where
  constructor explicit_vertex_link
  field
    source_vertex_class_number : Nat
    explicit_link_triangles : List (ExplicitLinkTriangle simplex_count)
    triangle_sides : List LinkTriangleSide
    explicit_link_has_bad_identification : Bool
    explicit_link_is_orientable : Bool
open ExplicitVertexLink public

buildExplicitLinkWithOccurrences : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) → Nat →
  FaceLinkClass 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  ExplicitVertexLink simplex_count
buildExplicitLinkWithOccurrences currentTriangulation edgeClasses
  vertexClassNumber currentVertexClass triangleOccurrences =
  explicit_vertex_link
    vertexClassNumber
    (assembleTriangles edgeClasses triangleOccurrences)
    (buildAllSides currentTriangulation triangleOccurrences)
    (face_has_bad_identification currentVertexClass)
    (face_link_is_orientable currentVertexClass)

buildExplicitLink : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) → Nat →
  FaceLinkClass 3 simplex_count → ExplicitVertexLink simplex_count
buildExplicitLink currentTriangulation edgeClasses vertexClassNumber
  currentVertexClass = buildExplicitLinkWithOccurrences currentTriangulation
  edgeClasses vertexClassNumber currentVertexClass
  (face_link_embeddings currentVertexClass)

buildExplicitLinksFrom : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) → Nat →
  List (FaceLinkClass 3 simplex_count) →
  List (ExplicitVertexLink simplex_count)
buildExplicitLinksFrom currentTriangulation edgeClasses nextClassNumber [] = []
buildExplicitLinksFrom currentTriangulation edgeClasses nextClassNumber
  (currentVertexClass ∷ remainingVertexClasses) =
  buildExplicitLink currentTriangulation edgeClasses nextClassNumber
    currentVertexClass ∷
  buildExplicitLinksFrom currentTriangulation edgeClasses
    (suc nextClassNumber) remainingVertexClasses

explicitVertexLinks : Triangulation 3 simplex_count →
  List (ExplicitVertexLink simplex_count)
explicitVertexLinks currentTriangulation = buildExplicitLinksFrom
  currentTriangulation
  (faceLinkClasses currentTriangulation 1)
  zero
  (faceLinkClasses currentTriangulation 0)

sideIsBoundary : LinkTriangleSide → Bool
sideIsBoundary currentSide with destination_side currentSide
... | boundary_side = true
... | paired_side targetAddress transportedEndpointVertices = false

sideIsPaired : LinkTriangleSide → Bool
sideIsPaired currentSide with destination_side currentSide
... | boundary_side = false
... | paired_side targetAddress transportedEndpointVertices = true

sideIsResolved : LinkTriangleSide → Bool
sideIsResolved currentSide with destination_side currentSide
... | boundary_side = true
... | paired_side nothing transportedEndpointVertices = false
... | paired_side (just targetAddress) transportedEndpointVertices = true

halfNatural : Nat → Nat
halfNatural zero = zero
halfNatural (suc zero) = zero
halfNatural (suc (suc remaining)) = suc (halfNatural remaining)

explicitLinkTriangleCount : ExplicitVertexLink simplex_count → Nat
explicitLinkTriangleCount currentLink =
  length (explicit_link_triangles currentLink)

explicitLinkVertexCount : ExplicitVertexLink simplex_count → Nat
explicitLinkVertexCount currentLink = length
  (collectTriangleLabels (explicit_link_triangles currentLink) [])

explicitLinkBoundaryEdgeCount : ExplicitVertexLink simplex_count → Nat
explicitLinkBoundaryEdgeCount currentLink = count_matching sideIsBoundary
  (triangle_sides currentLink)

explicitLinkPairedSideCount : ExplicitVertexLink simplex_count → Nat
explicitLinkPairedSideCount currentLink = count_matching sideIsPaired
  (triangle_sides currentLink)

explicitLinkEdgeCount : ExplicitVertexLink simplex_count → Nat
explicitLinkEdgeCount currentLink = explicitLinkBoundaryEdgeCount currentLink +
  halfNatural (explicitLinkPairedSideCount currentLink)

explicitLinkEulerCharacteristic : ExplicitVertexLink simplex_count →
  Link3.SignedInteger
explicitLinkEulerCharacteristic currentLink = Link3.naturalDifference
  (explicitLinkVertexCount currentLink + explicitLinkTriangleCount currentLink)
  (explicitLinkEdgeCount currentLink)

explicitLinkCornersResolved : ExplicitVertexLink simplex_count → Bool
explicitLinkCornersResolved currentLink = all triangleCornerLabelsResolved
  (explicit_link_triangles currentLink)

sideAddressEqual : LinkSideAddress → LinkSideAddress → Bool
sideAddressEqual firstAddress secondAddress =
  nat_equal (side_triangle_number firstAddress)
    (side_triangle_number secondAddress) and
  nat_equal (side_exit_facet_number firstAddress)
    (side_exit_facet_number secondAddress)

sourceAddress : LinkTriangleSide → LinkSideAddress
sourceAddress currentSide = link_side_address
  (source_triangle_number currentSide)
  (source_exit_facet_number currentSide)

findSide : LinkSideAddress → List LinkTriangleSide → Maybe LinkTriangleSide
findSide targetAddress [] = nothing
findSide targetAddress (currentSide ∷ remainingSides)
  with sideAddressEqual targetAddress (sourceAddress currentSide)
... | true = just currentSide
... | false = findSide targetAddress remainingSides

destinationMatches : LinkSideAddress → LinkSideDestination → Bool
destinationMatches expectedAddress boundary_side = false
destinationMatches expectedAddress
  (paired_side nothing transportedEndpointVertices) = false
destinationMatches expectedAddress
  (paired_side (just actualAddress) transportedEndpointVertices) =
  sideAddressEqual expectedAddress actualAddress

reciprocityAfterTargetLookup : LinkSideAddress →
  Maybe LinkTriangleSide → Bool
reciprocityAfterTargetLookup originalAddress nothing = false
reciprocityAfterTargetLookup originalAddress (just targetSide) =
  destinationMatches originalAddress (destination_side targetSide)

sidePairingReciprocal : List LinkTriangleSide → LinkTriangleSide → Bool
sidePairingReciprocal allSides currentSide with destination_side currentSide
... | boundary_side = true
... | paired_side nothing transportedEndpointVertices = false
... | paired_side (just targetAddress) transportedEndpointVertices =
  reciprocityAfterTargetLookup (sourceAddress currentSide)
    (findSide targetAddress allSides)

explicitLinkPairingsResolved : ExplicitVertexLink simplex_count → Bool
explicitLinkPairingsResolved currentLink = all sideIsResolved
  (triangle_sides currentLink)

explicitLinkPairingsReciprocal : ExplicitVertexLink simplex_count → Bool
explicitLinkPairingsReciprocal currentLink = all
  (sidePairingReciprocal (triangle_sides currentLink))
  (triangle_sides currentLink)
