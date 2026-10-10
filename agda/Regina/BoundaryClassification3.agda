{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- Real-boundary orientation and closed-surface classification in dimension 3.
-- Derived from calculateRealBoundary() in
-- engine/triangulation/detail/skeleton-impl.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.BoundaryClassification3 where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks
import Regina.Embeddings as Embeddings
import Regina.VertexLinkSurface3 as VertexLinks
import Regina.Boundary3 as Boundary
import Regina.Link3 as Link3

filterElements : {element : Set} →
  (element → Bool) → List element → List element
filterElements predicate [] = []
filterElements predicate (headElement ∷ tailElements)
  with predicate headElement
... | true = headElement ∷ filterElements predicate tailElements
... | false = filterElements predicate tailElements

concatMap : {source target : Set} →
  (source → List target) → List source → List target
concatMap function [] = []
concatMap function (headElement ∷ tailElements) =
  function headElement ++ concatMap function tailElements

record TriangleVertices : Set where
  constructor triangle_vertices
  field
    triangle_vertex_zero : Fin 4
    triangle_vertex_one : Fin 4
    triangle_vertex_two : Fin 4
open TriangleVertices public

triangleVerticesFromList : List (Fin 4) → Maybe TriangleVertices
triangleVerticesFromList [] = nothing
triangleVerticesFromList (firstVertex ∷ []) = nothing
triangleVerticesFromList (firstVertex ∷ secondVertex ∷ []) = nothing
triangleVerticesFromList
  (firstVertex ∷ secondVertex ∷ thirdVertex ∷ remainingVertices) =
  just (triangle_vertices firstVertex secondVertex thirdVertex)

record BoundaryDirectedSide : Set where
  constructor boundary_directed_side
  field
    side_facet_number : Nat
    side_local_number : Nat
    side_edge_number : Nat
    side_forward_direction : Bool
open BoundaryDirectedSide public

directionFromEndpoints : Nat → Nat → Maybe Bool
directionFromEndpoints zero (suc zero) = just true
directionFromEndpoints (suc zero) zero = just false
directionFromEndpoints firstEndpoint secondEndpoint = nothing

assembleSideFromDirection : Nat → Nat → Nat → Maybe Bool →
  Maybe BoundaryDirectedSide
assembleSideFromDirection facetNumber sideNumber edgeNumber nothing = nothing
assembleSideFromDirection facetNumber sideNumber edgeNumber
  (just forwardDirection) = just
  (boundary_directed_side facetNumber sideNumber edgeNumber forwardDirection)

assembleSideFromNumbers : Nat → Nat → Nat → Nat → Nat → Nat →
  Maybe BoundaryDirectedSide
assembleSideFromNumbers facetNumber sideNumber firstEdge firstEndpoint
  secondEdge secondEndpoint
  with nat_equal firstEdge secondEdge
... | false = nothing
... | true = assembleSideFromDirection facetNumber sideNumber firstEdge
  (directionFromEndpoints firstEndpoint secondEndpoint)

assembleSideFromLabels : Nat → Nat →
  Maybe VertexLinks.LinkCornerLabel → Maybe VertexLinks.LinkCornerLabel →
  Maybe BoundaryDirectedSide
assembleSideFromLabels facetNumber sideNumber nothing secondLabel = nothing
assembleSideFromLabels facetNumber sideNumber (just firstLabel) nothing = nothing
assembleSideFromLabels facetNumber sideNumber
  (just firstLabel) (just secondLabel) = assembleSideFromNumbers
  facetNumber sideNumber
  (VertexLinks.corner_edge_class_number firstLabel)
  (VertexLinks.corner_edge_endpoint_number firstLabel)
  (VertexLinks.corner_edge_class_number secondLabel)
  (VertexLinks.corner_edge_endpoint_number secondLabel)

makeDirectedSide : {numberOfSimplices : Nat} →
  List (FaceLinkClass 3 numberOfSimplices) →
  Nat → Nat → Fin numberOfSimplices → Fin 4 → Fin 4 →
  Maybe BoundaryDirectedSide
makeDirectedSide edgeClasses facetNumber sideNumber simplexIndex
  firstVertex secondVertex = assembleSideFromLabels facetNumber sideNumber
  (VertexLinks.findCornerLabelFrom zero
    (VertexLinks.localEdgeFace simplexIndex firstVertex secondVertex)
    firstVertex edgeClasses)
  (VertexLinks.findCornerLabelFrom zero
    (VertexLinks.localEdgeFace simplexIndex firstVertex secondVertex)
    secondVertex edgeClasses)

unresolvedFacetSides : List (Maybe BoundaryDirectedSide)
unresolvedFacetSides = nothing ∷ nothing ∷ nothing ∷ []

facetSidesFromTriangle : {numberOfSimplices : Nat} →
  List (FaceLinkClass 3 numberOfSimplices) →
  Nat → Fin numberOfSimplices → TriangleVertices →
  List (Maybe BoundaryDirectedSide)
facetSidesFromTriangle edgeClasses facetNumber simplexIndex triangleVertices =
  makeDirectedSide edgeClasses facetNumber 0 simplexIndex
    (triangle_vertex_one triangleVertices)
    (triangle_vertex_two triangleVertices) ∷
  makeDirectedSide edgeClasses facetNumber 1 simplexIndex
    (triangle_vertex_two triangleVertices)
    (triangle_vertex_zero triangleVertices) ∷
  makeDirectedSide edgeClasses facetNumber 2 simplexIndex
    (triangle_vertex_zero triangleVertices)
    (triangle_vertex_one triangleVertices) ∷ []

facetSidesAfterVertices : {numberOfSimplices : Nat} →
  List (FaceLinkClass 3 numberOfSimplices) → Nat →
  Embeddings.FaceEmbedding 3 numberOfSimplices → Maybe TriangleVertices →
  List (Maybe BoundaryDirectedSide)
facetSidesAfterVertices edgeClasses facetNumber currentEmbedding nothing =
  unresolvedFacetSides
facetSidesAfterVertices edgeClasses facetNumber currentEmbedding
  (just triangleVertices) = facetSidesFromTriangle edgeClasses facetNumber
  (face_simplex (Embeddings.embedded_local_face currentEmbedding))
  triangleVertices

facetSidesAfterEmbedding : {numberOfSimplices : Nat} →
  List (FaceLinkClass 3 numberOfSimplices) →
  Boundary.IndexedBoundaryFacet numberOfSimplices →
  Maybe (Embeddings.FaceEmbedding 3 numberOfSimplices) →
  List (Maybe BoundaryDirectedSide)
facetSidesAfterEmbedding edgeClasses currentFacet nothing =
  unresolvedFacetSides
facetSidesAfterEmbedding edgeClasses currentFacet (just currentEmbedding) =
  facetSidesAfterVertices edgeClasses
    (Boundary.boundary_facet_class_number currentFacet)
    currentEmbedding
    (triangleVerticesFromList
      (Embeddings.ordered_simplex_vertices currentEmbedding))

facetSideCandidates : {numberOfSimplices : Nat} →
  List (FaceLinkClass 3 numberOfSimplices) →
  Boundary.IndexedBoundaryFacet numberOfSimplices →
  List (Maybe BoundaryDirectedSide)
facetSideCandidates edgeClasses currentFacet = facetSidesAfterEmbedding
  edgeClasses currentFacet
  (Boundary.firstEmbedding
    (Boundary.boundary_facet_class_value currentFacet))

componentSideCandidates : {numberOfSimplices : Nat} →
  List (FaceLinkClass 3 numberOfSimplices) →
  List (Boundary.IndexedBoundaryFacet numberOfSimplices) →
  List (Maybe BoundaryDirectedSide)
componentSideCandidates edgeClasses currentComponent =
  concatMap (facetSideCandidates edgeClasses) currentComponent

candidateResolved : Maybe BoundaryDirectedSide → Bool
candidateResolved nothing = false
candidateResolved (just currentSide) = true

collectResolvedSides : List (Maybe BoundaryDirectedSide) →
  List BoundaryDirectedSide
collectResolvedSides [] = []
collectResolvedSides (nothing ∷ remainingCandidates) =
  collectResolvedSides remainingCandidates
collectResolvedSides (just currentSide ∷ remainingCandidates) =
  currentSide ∷ collectResolvedSides remainingCandidates

sameSideOccurrence : BoundaryDirectedSide → BoundaryDirectedSide → Bool
sameSideOccurrence firstSide secondSide =
  nat_equal (side_facet_number firstSide)
    (side_facet_number secondSide) and
  nat_equal (side_local_number firstSide)
    (side_local_number secondSide)

sameGlobalEdge : BoundaryDirectedSide → BoundaryDirectedSide → Bool
sameGlobalEdge firstSide secondSide =
  nat_equal (side_edge_number firstSide) (side_edge_number secondSide)

countEdgeOccurrences : Nat → List BoundaryDirectedSide → Nat
countEdgeOccurrences requestedEdge [] = zero
countEdgeOccurrences requestedEdge (currentSide ∷ remainingSides)
  with nat_equal requestedEdge (side_edge_number currentSide)
... | true = suc (countEdgeOccurrences requestedEdge remainingSides)
... | false = countEdgeOccurrences requestedEdge remainingSides

edgeOccurrencePaired : List BoundaryDirectedSide →
  BoundaryDirectedSide → Bool
edgeOccurrencePaired allSides currentSide = nat_equal
  (countEdgeOccurrences (side_edge_number currentSide) allSides) 2

allEdgeOccurrencesPaired : List BoundaryDirectedSide → Bool
allEdgeOccurrencesPaired allSides = all (edgeOccurrencePaired allSides) allSides

record OrientedBoundaryFacet : Set where
  constructor oriented_boundary_facet
  field
    oriented_facet_number : Nat
    oriented_facet_positive : Bool
open OrientedBoundaryFacet public

orientedFacetEqual : OrientedBoundaryFacet → OrientedBoundaryFacet → Bool
orientedFacetEqual firstFacet secondFacet =
  nat_equal (oriented_facet_number firstFacet)
    (oriented_facet_number secondFacet) and
  bool_equal (oriented_facet_positive firstFacet)
    (oriented_facet_positive secondFacet)

orientedFacetMember : OrientedBoundaryFacet →
  List OrientedBoundaryFacet → Bool
orientedFacetMember targetFacet [] = false
orientedFacetMember targetFacet (currentFacet ∷ remainingFacets) =
  orientedFacetEqual targetFacet currentFacet or
  orientedFacetMember targetFacet remainingFacets

statesForFacet : {numberOfSimplices : Nat} →
  Boundary.IndexedBoundaryFacet numberOfSimplices →
  List OrientedBoundaryFacet
statesForFacet currentFacet =
  oriented_boundary_facet
    (Boundary.boundary_facet_class_number currentFacet) true ∷
  oriented_boundary_facet
    (Boundary.boundary_facet_class_number currentFacet) false ∷ []

allFacetStates : {numberOfSimplices : Nat} →
  List (Boundary.IndexedBoundaryFacet numberOfSimplices) →
  List OrientedBoundaryFacet
allFacetStates currentComponent = concatMap statesForFacet currentComponent

sideBelongsToState : OrientedBoundaryFacet → BoundaryDirectedSide → Bool
sideBelongsToState currentFacetState currentSide = nat_equal
  (oriented_facet_number currentFacetState) (side_facet_number currentSide)

transportPositiveValue : Bool → Bool → Bool
transportPositiveValue sourcePositive true = not sourcePositive
transportPositiveValue sourcePositive false = sourcePositive

transportAcrossSides : Bool → BoundaryDirectedSide →
  BoundaryDirectedSide → Bool
transportAcrossSides sourcePositive sourceSide targetSide =
  transportPositiveValue sourcePositive
    (bool_equal (side_forward_direction sourceSide)
      (side_forward_direction targetSide))

pairConnects : OrientedBoundaryFacet → BoundaryDirectedSide →
  BoundaryDirectedSide → Bool
pairConnects sourceFacetState sourceSide targetSide =
  sideBelongsToState sourceFacetState sourceSide and
  sameGlobalEdge sourceSide targetSide and
  not (sameSideOccurrence sourceSide targetSide)

neighborFromPair : OrientedBoundaryFacet → BoundaryDirectedSide →
  BoundaryDirectedSide → List OrientedBoundaryFacet
neighborFromPair sourceFacetState sourceSide targetSide
  with pairConnects sourceFacetState sourceSide targetSide
... | false = []
... | true = oriented_boundary_facet
  (side_facet_number targetSide)
  (transportAcrossSides
    (oriented_facet_positive sourceFacetState) sourceSide targetSide) ∷ []

neighborsForSourceSide : OrientedBoundaryFacet → BoundaryDirectedSide →
  List BoundaryDirectedSide → List OrientedBoundaryFacet
neighborsForSourceSide sourceFacetState sourceSide allSides =
  concatMap (neighborFromPair sourceFacetState sourceSide) allSides

neighborsForFacetState : OrientedBoundaryFacet →
  List BoundaryDirectedSide → List OrientedBoundaryFacet
neighborsForFacetState sourceFacetState allSides = concatMap
  (λ sourceSide → neighborsForSourceSide sourceFacetState sourceSide allSides)
  allSides

directlyConnected : List BoundaryDirectedSide →
  OrientedBoundaryFacet → OrientedBoundaryFacet → Bool
directlyConnected allSides firstFacetState secondFacetState =
  orientedFacetEqual firstFacetState secondFacetState or
  orientedFacetMember secondFacetState
    (neighborsForFacetState firstFacetState allSides)

expandOnce : List BoundaryDirectedSide → List OrientedBoundaryFacet →
  List OrientedBoundaryFacet → List OrientedBoundaryFacet
expandOnce allSides facetStateUniverse reachedFacetStates = filterElements
  (λ candidateFacetState → any
    (λ reachedFacetState → directlyConnected allSides
      reachedFacetState candidateFacetState)
    reachedFacetStates)
  facetStateUniverse

expandFacetStates : Nat → List BoundaryDirectedSide →
  List OrientedBoundaryFacet → List OrientedBoundaryFacet →
  List OrientedBoundaryFacet
expandFacetStates zero allSides facetStateUniverse reachedFacetStates =
  reachedFacetStates
expandFacetStates (suc fuel) allSides facetStateUniverse reachedFacetStates =
  expandFacetStates fuel allSides facetStateUniverse
    (expandOnce allSides facetStateUniverse reachedFacetStates)

reachableFacetStates : {numberOfSimplices : Nat} →
  List (Boundary.IndexedBoundaryFacet numberOfSimplices) →
  List BoundaryDirectedSide → List OrientedBoundaryFacet
reachableFacetStates [] allSides = []
reachableFacetStates (rootFacet ∷ remainingFacets) allSides =
  expandFacetStates (length facetStateUniverse) allSides facetStateUniverse
    (oriented_boundary_facet
      (Boundary.boundary_facet_class_number rootFacet) true ∷ [])
  where
  facetStateUniverse : List OrientedBoundaryFacet
  facetStateUniverse = allFacetStates (rootFacet ∷ remainingFacets)

facetHasBothSigns : {numberOfSimplices : Nat} →
  List OrientedBoundaryFacet →
  Boundary.IndexedBoundaryFacet numberOfSimplices → Bool
facetHasBothSigns reachedFacetStates currentFacet =
  orientedFacetMember
    (oriented_boundary_facet
      (Boundary.boundary_facet_class_number currentFacet) true)
    reachedFacetStates and
  orientedFacetMember
    (oriented_boundary_facet
      (Boundary.boundary_facet_class_number currentFacet) false)
    reachedFacetStates

componentOrientationValue : {numberOfSimplices : Nat} →
  List (Boundary.IndexedBoundaryFacet numberOfSimplices) →
  List BoundaryDirectedSide → Bool
componentOrientationValue currentComponent allSides = not
  (any (facetHasBothSigns
    (reachableFacetStates currentComponent allSides)) currentComponent)

orientationDataResolved : {numberOfSimplices : Nat} →
  List (Boundary.IndexedBoundaryFacet numberOfSimplices) →
  List (Maybe BoundaryDirectedSide) → List BoundaryDirectedSide → Bool
orientationDataResolved currentComponent candidates resolvedSides =
  all candidateResolved candidates and
  allEdgeOccurrencesPaired resolvedSides and
  nat_equal (length resolvedSides) (3 * length currentComponent)

record RealBoundaryOrientationSummary : Set where
  constructor real_boundary_orientation_summary
  field
    real_boundary_facet_numbers : List Nat
    real_boundary_orientation_computed : Bool
    real_boundary_orientation_value : Bool
open RealBoundaryOrientationSummary public

summaryAfterResolution : {numberOfSimplices : Nat} →
  List (Boundary.IndexedBoundaryFacet numberOfSimplices) →
  List BoundaryDirectedSide → Bool → RealBoundaryOrientationSummary
summaryAfterResolution currentComponent resolvedSides false =
  real_boundary_orientation_summary
    (Boundary.componentFacetNumbers currentComponent) false false
summaryAfterResolution currentComponent resolvedSides true =
  real_boundary_orientation_summary
    (Boundary.componentFacetNumbers currentComponent) true
    (componentOrientationValue currentComponent resolvedSides)

analyseRealBoundaryComponent : {numberOfSimplices : Nat} →
  List (FaceLinkClass 3 numberOfSimplices) →
  List (Boundary.IndexedBoundaryFacet numberOfSimplices) →
  RealBoundaryOrientationSummary
analyseRealBoundaryComponent edgeClasses currentComponent =
  summaryAfterResolution currentComponent resolvedSides
    (orientationDataResolved currentComponent candidates resolvedSides)
  where
  candidates : List (Maybe BoundaryDirectedSide)
  candidates = componentSideCandidates edgeClasses currentComponent

  resolvedSides : List BoundaryDirectedSide
  resolvedSides = collectResolvedSides candidates

realBoundaryOrientationSummaries : {numberOfSimplices : Nat} →
  Triangulation 3 numberOfSimplices → List RealBoundaryOrientationSummary
realBoundaryOrientationSummaries {numberOfSimplices} currentTriangulation = map
  (analyseRealBoundaryComponent edgeClasses)
  (Boundary.realBoundaryFacetComponents currentTriangulation)
  where
  edgeClasses : List (FaceLinkClass 3 numberOfSimplices)
  edgeClasses = faceLinkClasses currentTriangulation 1

data ClosedSurfaceType : Set where
  orientable_genus : Nat → ClosedSurfaceType
  nonorientable_genus : Nat → ClosedSurfaceType
  unclassified_surface : ClosedSurfaceType

twoMinusEuler : Link3.SignedInteger → Maybe Nat
twoMinusEuler Link3.signed_zero = just 2
twoMinusEuler (Link3.signed_positive zero) = just 1
twoMinusEuler (Link3.signed_positive (suc zero)) = just zero
twoMinusEuler (Link3.signed_positive (suc (suc remaining))) = nothing
twoMinusEuler (Link3.signed_negative magnitudeRemainder) =
  just (suc (suc (suc magnitudeRemainder)))

halfEvenNatural : Nat → Maybe Nat
halfEvenNatural zero = just zero
halfEvenNatural (suc zero) = nothing
halfEvenNatural (suc (suc remaining))
  with halfEvenNatural remaining
... | nothing = nothing
... | just halfValue = just (suc halfValue)

classifyOrientableDelta : Maybe Nat → ClosedSurfaceType
classifyOrientableDelta nothing = unclassified_surface
classifyOrientableDelta (just deltaValue)
  with halfEvenNatural deltaValue
... | nothing = unclassified_surface
... | just surfaceGenusValue = orientable_genus surfaceGenusValue

classifyNonorientableDelta : Maybe Nat → ClosedSurfaceType
classifyNonorientableDelta nothing = unclassified_surface
classifyNonorientableDelta (just zero) = unclassified_surface
classifyNonorientableDelta (just (suc crosscapRemainder)) =
  nonorientable_genus (suc crosscapRemainder)

classifyClosedSurface : Bool → Bool → Link3.SignedInteger →
  ClosedSurfaceType
classifyClosedSurface false orientationValue eulerCharacteristic =
  unclassified_surface
classifyClosedSurface true true eulerCharacteristic =
  classifyOrientableDelta (twoMinusEuler eulerCharacteristic)
classifyClosedSurface true false eulerCharacteristic =
  classifyNonorientableDelta (twoMinusEuler eulerCharacteristic)

record ClassifiedBoundarySurface : Set where
  constructor classified_boundary_surface
  field
    classified_boundary_kind : Boundary.BoundaryComponentKind
    classified_source_face_numbers : List Nat
    classified_vertex_number : Nat
    classified_edge_number : Nat
    classified_triangle_number : Nat
    classified_euler_characteristic : Link3.SignedInteger
    classified_orientation_computed : Bool
    classified_orientation_value : Bool
    classified_surface_type : ClosedSurfaceType
open ClassifiedBoundarySurface public

classifyBoundaryData : Boundary.BoundaryComponent3 → Bool → Bool →
  ClassifiedBoundarySurface
classifyBoundaryData currentBoundary orientationComputed orientationValue =
  classified_boundary_surface
    (Boundary.boundary_component_kind currentBoundary)
    (Boundary.source_face_class_numbers currentBoundary)
    (Boundary.boundary_vertex_count currentBoundary)
    (Boundary.boundary_edge_count currentBoundary)
    (Boundary.boundary_triangle_count currentBoundary)
    (Boundary.boundary_euler_characteristic currentBoundary)
    orientationComputed
    orientationValue
    (classifyClosedSurface orientationComputed orientationValue
      (Boundary.boundary_euler_characteristic currentBoundary))

classifyRealBoundaryWithSummary : Boundary.BoundaryComponent3 →
  RealBoundaryOrientationSummary → ClassifiedBoundarySurface
classifyRealBoundaryWithSummary currentBoundary orientationSummary =
  classifyBoundaryData currentBoundary
    (real_boundary_orientation_computed orientationSummary)
    (real_boundary_orientation_value orientationSummary)

classifyRealBoundaryComponent : {numberOfSimplices : Nat} →
  List (FaceLinkClass 3 numberOfSimplices) →
  List (FaceLinkClass 3 numberOfSimplices) →
  List (Boundary.IndexedBoundaryFacet numberOfSimplices) →
  ClassifiedBoundarySurface
classifyRealBoundaryComponent vertexClasses edgeClasses currentComponent =
  classifyRealBoundaryWithSummary
    (Boundary.makeRealBoundaryComponent vertexClasses edgeClasses currentComponent)
    (analyseRealBoundaryComponent edgeClasses currentComponent)

classifiedRealBoundarySurfaces : {numberOfSimplices : Nat} →
  Triangulation 3 numberOfSimplices → List ClassifiedBoundarySurface
classifiedRealBoundarySurfaces {numberOfSimplices} currentTriangulation = map
  (classifyRealBoundaryComponent vertexClasses edgeClasses)
  (Boundary.realBoundaryFacetComponents currentTriangulation)
  where
  vertexClasses : List (FaceLinkClass 3 numberOfSimplices)
  vertexClasses = faceLinkClasses currentTriangulation 0

  edgeClasses : List (FaceLinkClass 3 numberOfSimplices)
  edgeClasses = faceLinkClasses currentTriangulation 1

classifyExistingBoundary : Boundary.BoundaryComponent3 →
  ClassifiedBoundarySurface
classifyExistingBoundary currentBoundary = classifyBoundaryData currentBoundary
  (Boundary.boundary_orientation_computed currentBoundary)
  (Boundary.boundary_is_orientable currentBoundary)

classifiedIdealBoundarySurfaces : {numberOfSimplices : Nat} →
  Triangulation 3 numberOfSimplices → List ClassifiedBoundarySurface
classifiedIdealBoundarySurfaces currentTriangulation = map
  classifyExistingBoundary (Boundary.idealBoundaryComponents currentTriangulation)

classifiedBoundarySurfaces : {numberOfSimplices : Nat} →
  Triangulation 3 numberOfSimplices → List ClassifiedBoundarySurface
classifiedBoundarySurfaces currentTriangulation =
  classifiedRealBoundarySurfaces currentTriangulation ++
  classifiedIdealBoundarySurfaces currentTriangulation
