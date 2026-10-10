{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- Real-boundary orientation and closed-surface classification in dimension 3.
-- Derived from calculateRealBoundary() in
-- engine/triangulation/detail/skeleton-impl.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.BoundarySurface3 where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks
import Regina.Embeddings as Embeddings
import Regina.VertexLinkSurface3 as VertexLinks
import Regina.Boundary3 as Boundary
import Regina.Components as Components
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
    directed_facet_number : Nat
    directed_side_number : Nat
    directed_edge_number : Nat
    directed_edge_orientation : Components.Orientation
open BoundaryDirectedSide public

directionFromEndpointNumbers : Nat → Nat → Maybe Components.Orientation
directionFromEndpointNumbers zero (suc zero) = just Components.positive
directionFromEndpointNumbers (suc zero) zero = just Components.negative
directionFromEndpointNumbers firstEndpoint secondEndpoint = nothing

sideFromResolvedLabels : Nat → Nat →
  VertexLinks.LinkCornerLabel → VertexLinks.LinkCornerLabel →
  Maybe BoundaryDirectedSide
sideFromResolvedLabels facetNumber sideNumber firstLabel secondLabel
  with nat_equal
    (VertexLinks.corner_edge_class_number firstLabel)
    (VertexLinks.corner_edge_class_number secondLabel)
... | false = nothing
... | true with directionFromEndpointNumbers
  (VertexLinks.corner_edge_endpoint_number firstLabel)
  (VertexLinks.corner_edge_endpoint_number secondLabel)
...   | nothing = nothing
...   | just edgeOrientation = just (boundary_directed_side
  facetNumber sideNumber
  (VertexLinks.corner_edge_class_number firstLabel)
  edgeOrientation)

sideFromLabelLookups : Nat → Nat →
  Maybe VertexLinks.LinkCornerLabel → Maybe VertexLinks.LinkCornerLabel →
  Maybe BoundaryDirectedSide
sideFromLabelLookups facetNumber sideNumber nothing secondLabel = nothing
sideFromLabelLookups facetNumber sideNumber (just firstLabel) nothing = nothing
sideFromLabelLookups facetNumber sideNumber
  (just firstLabel) (just secondLabel) =
  sideFromResolvedLabels facetNumber sideNumber firstLabel secondLabel

makeDirectedSide : List (FaceLinkClass 3 simplex_count) →
  Nat → Nat → Fin simplex_count → Fin 4 → Fin 4 →
  Maybe BoundaryDirectedSide
makeDirectedSide edgeClasses facetNumber sideNumber simplexIndex
  firstVertex secondVertex = sideFromLabelLookups facetNumber sideNumber
  (VertexLinks.findCornerLabelFrom zero targetEdge firstVertex edgeClasses)
  (VertexLinks.findCornerLabelFrom zero targetEdge secondVertex edgeClasses)
  where
  targetEdge : LocalFace 3 simplex_count
  targetEdge = VertexLinks.localEdgeFace simplexIndex firstVertex secondVertex

unresolvedFacetSides : List (Maybe BoundaryDirectedSide)
unresolvedFacetSides = nothing ∷ nothing ∷ nothing ∷ []

facetSidesFromTriangle : List (FaceLinkClass 3 simplex_count) →
  Nat → Fin simplex_count → TriangleVertices →
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

facetSidesFromTriangleLookup : List (FaceLinkClass 3 simplex_count) →
  Nat → Embeddings.FaceEmbedding 3 simplex_count → Maybe TriangleVertices →
  List (Maybe BoundaryDirectedSide)
facetSidesFromTriangleLookup edgeClasses facetNumber currentEmbedding nothing =
  unresolvedFacetSides
facetSidesFromTriangleLookup edgeClasses facetNumber currentEmbedding
  (just triangleVertices) = facetSidesFromTriangle edgeClasses facetNumber
  (face_simplex (Embeddings.embedded_local_face currentEmbedding))
  triangleVertices

facetSidesFromEmbeddingLookup : List (FaceLinkClass 3 simplex_count) →
  Boundary.IndexedBoundaryFacet simplex_count →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count) →
  List (Maybe BoundaryDirectedSide)
facetSidesFromEmbeddingLookup edgeClasses currentFacet nothing =
  unresolvedFacetSides
facetSidesFromEmbeddingLookup edgeClasses currentFacet
  (just currentEmbedding) = facetSidesFromTriangleLookup edgeClasses
  (Boundary.boundary_facet_class_number currentFacet)
  currentEmbedding
  (triangleVerticesFromList
    (Embeddings.ordered_simplex_vertices currentEmbedding))

boundaryFacetSideCandidates : List (FaceLinkClass 3 simplex_count) →
  Boundary.IndexedBoundaryFacet simplex_count →
  List (Maybe BoundaryDirectedSide)
boundaryFacetSideCandidates edgeClasses currentFacet =
  facetSidesFromEmbeddingLookup edgeClasses currentFacet
    (Boundary.firstEmbedding
      (Boundary.boundary_facet_class_value currentFacet))

componentSideCandidates : List (FaceLinkClass 3 simplex_count) →
  List (Boundary.IndexedBoundaryFacet simplex_count) →
  List (Maybe BoundaryDirectedSide)
componentSideCandidates edgeClasses currentComponent =
  concatMap (boundaryFacetSideCandidates edgeClasses) currentComponent

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
  nat_equal (directed_facet_number firstSide)
    (directed_facet_number secondSide) and
  nat_equal (directed_side_number firstSide)
    (directed_side_number secondSide)

sameGlobalEdge : BoundaryDirectedSide → BoundaryDirectedSide → Bool
sameGlobalEdge firstSide secondSide = nat_equal
  (directed_edge_number firstSide) (directed_edge_number secondSide)

countEdgeOccurrences : Nat → List BoundaryDirectedSide → Nat
countEdgeOccurrences edgeNumber [] = zero
countEdgeOccurrences edgeNumber (currentSide ∷ remainingSides)
  with nat_equal edgeNumber (directed_edge_number currentSide)
... | true = suc (countEdgeOccurrences edgeNumber remainingSides)
... | false = countEdgeOccurrences edgeNumber remainingSides

edgeOccurrenceIsPaired : List BoundaryDirectedSide →
  BoundaryDirectedSide → Bool
edgeOccurrenceIsPaired allSides currentSide = nat_equal
  (countEdgeOccurrences (directed_edge_number currentSide) allSides) 2

allEdgeOccurrencesPaired : List BoundaryDirectedSide → Bool
allEdgeOccurrencesPaired allSides = all
  (edgeOccurrenceIsPaired allSides) allSides

record OrientedBoundaryFacet : Set where
  constructor oriented_boundary_facet
  field
    oriented_facet_number : Nat
    oriented_facet_orientation : Components.Orientation
open OrientedBoundaryFacet public

orientedFacetEqual : OrientedBoundaryFacet → OrientedBoundaryFacet → Bool
orientedFacetEqual firstFacet secondFacet =
  nat_equal (oriented_facet_number firstFacet)
    (oriented_facet_number secondFacet) and
  Components.orientationEqual
    (oriented_facet_orientation firstFacet)
    (oriented_facet_orientation secondFacet)

orientedFacetMember : OrientedBoundaryFacet →
  List OrientedBoundaryFacet → Bool
orientedFacetMember targetFacet [] = false
orientedFacetMember targetFacet (currentFacet ∷ remainingFacets) =
  orientedFacetEqual targetFacet currentFacet or
  orientedFacetMember targetFacet remainingFacets

statesForFacet : Boundary.IndexedBoundaryFacet simplex_count →
  List OrientedBoundaryFacet
statesForFacet currentFacet =
  oriented_boundary_facet
    (Boundary.boundary_facet_class_number currentFacet)
    Components.positive ∷
  oriented_boundary_facet
    (Boundary.boundary_facet_class_number currentFacet)
    Components.negative ∷ []

allFacetStates : List (Boundary.IndexedBoundaryFacet simplex_count) →
  List OrientedBoundaryFacet
allFacetStates currentComponent = concatMap statesForFacet currentComponent

sideBelongsToState : OrientedBoundaryFacet → BoundaryDirectedSide → Bool
sideBelongsToState currentState currentSide = nat_equal
  (oriented_facet_number currentState)
  (directed_facet_number currentSide)

transportAfterDirectionComparison : Components.Orientation → Bool →
  Components.Orientation
transportAfterDirectionComparison sourceOrientation true =
  Components.flipOrientation sourceOrientation
transportAfterDirectionComparison sourceOrientation false = sourceOrientation

transportOrientation : Components.Orientation → BoundaryDirectedSide →
  BoundaryDirectedSide → Components.Orientation
transportOrientation sourceOrientation sourceSide targetSide =
  transportAfterDirectionComparison sourceOrientation
    (Components.orientationEqual
      (directed_edge_orientation sourceSide)
      (directed_edge_orientation targetSide))

pairConnects : OrientedBoundaryFacet → BoundaryDirectedSide →
  BoundaryDirectedSide → Bool
pairConnects sourceState sourceSide targetSide =
  sideBelongsToState sourceState sourceSide and
  sameGlobalEdge sourceSide targetSide and
  not (sameSideOccurrence sourceSide targetSide)

neighborFromPair : OrientedBoundaryFacet → BoundaryDirectedSide →
  BoundaryDirectedSide → List OrientedBoundaryFacet
neighborFromPair sourceState sourceSide targetSide
  with pairConnects sourceState sourceSide targetSide
... | false = []
... | true = oriented_boundary_facet
  (directed_facet_number targetSide)
  (transportOrientation
    (oriented_facet_orientation sourceState) sourceSide targetSide) ∷ []

neighborsForSourceSide : OrientedBoundaryFacet → BoundaryDirectedSide →
  List BoundaryDirectedSide → List OrientedBoundaryFacet
neighborsForSourceSide sourceState sourceSide allSides =
  concatMap (neighborFromPair sourceState sourceSide) allSides

neighborsForState : OrientedBoundaryFacet → List BoundaryDirectedSide →
  List OrientedBoundaryFacet
neighborsForState sourceState allSides = concatMap
  (λ sourceSide → neighborsForSourceSide sourceState sourceSide allSides)
  allSides

directlyConnected : List BoundaryDirectedSide →
  OrientedBoundaryFacet → OrientedBoundaryFacet → Bool
directlyConnected allSides firstState secondState =
  orientedFacetEqual firstState secondState or
  orientedFacetMember secondState (neighborsForState firstState allSides)

expandOnce : List BoundaryDirectedSide → List OrientedBoundaryFacet →
  List OrientedBoundaryFacet → List OrientedBoundaryFacet
expandOnce allSides universe reachedStates = filterElements
  (λ candidateState → any
    (λ reachedState → directlyConnected allSides reachedState candidateState)
    reachedStates)
  universe

expandStates : Nat → List BoundaryDirectedSide →
  List OrientedBoundaryFacet → List OrientedBoundaryFacet →
  List OrientedBoundaryFacet
expandStates zero allSides universe reachedStates = reachedStates
expandStates (suc fuel) allSides universe reachedStates =
  expandStates fuel allSides universe
    (expandOnce allSides universe reachedStates)

reachableStates : List (Boundary.IndexedBoundaryFacet simplex_count) →
  List BoundaryDirectedSide → List OrientedBoundaryFacet
reachableStates [] allSides = []
reachableStates (rootFacet ∷ remainingFacets) allSides =
  expandStates (length universe) allSides universe
    (oriented_boundary_facet
      (Boundary.boundary_facet_class_number rootFacet)
      Components.positive ∷ [])
  where
  universe : List OrientedBoundaryFacet
  universe = allFacetStates (rootFacet ∷ remainingFacets)

facetHasBothOrientations : List OrientedBoundaryFacet →
  Boundary.IndexedBoundaryFacet simplex_count → Bool
facetHasBothOrientations reachedStates currentFacet =
  orientedFacetMember
    (oriented_boundary_facet
      (Boundary.boundary_facet_class_number currentFacet)
      Components.positive)
    reachedStates and
  orientedFacetMember
    (oriented_boundary_facet
      (Boundary.boundary_facet_class_number currentFacet)
      Components.negative)
    reachedStates

componentOrientable : List (Boundary.IndexedBoundaryFacet simplex_count) →
  List BoundaryDirectedSide → Bool
componentOrientable currentComponent allSides = not
  (any (facetHasBothOrientations
    (reachableStates currentComponent allSides)) currentComponent)

orientationDataResolved :
  List (Boundary.IndexedBoundaryFacet simplex_count) →
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
    real_boundary_is_orientable : Bool
open RealBoundaryOrientationSummary public

summaryAfterResolution :
  List (Boundary.IndexedBoundaryFacet simplex_count) →
  List BoundaryDirectedSide → Bool → RealBoundaryOrientationSummary
summaryAfterResolution currentComponent resolvedSides false =
  real_boundary_orientation_summary
    (Boundary.componentFacetNumbers currentComponent) false false
summaryAfterResolution currentComponent resolvedSides true =
  real_boundary_orientation_summary
    (Boundary.componentFacetNumbers currentComponent) true
    (componentOrientable currentComponent resolvedSides)

analyseRealBoundaryComponent : List (FaceLinkClass 3 simplex_count) →
  List (Boundary.IndexedBoundaryFacet simplex_count) →
  RealBoundaryOrientationSummary
analyseRealBoundaryComponent edgeClasses currentComponent =
  summaryAfterResolution currentComponent resolvedSides
    (orientationDataResolved currentComponent candidates resolvedSides)
  where
  candidates : List (Maybe BoundaryDirectedSide)
  candidates = componentSideCandidates edgeClasses currentComponent

  resolvedSides : List BoundaryDirectedSide
  resolvedSides = collectResolvedSides candidates

realBoundaryOrientationSummaries : Triangulation 3 simplex_count →
  List RealBoundaryOrientationSummary
realBoundaryOrientationSummaries
  {simplex_count = numberOfSimplices} currentTriangulation = map
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
classifyOrientableDelta (just delta)
  with halfEvenNatural delta
... | nothing = unclassified_surface
... | just surfaceGenusValue = orientable_genus surfaceGenusValue

classifyNonorientableDelta : Maybe Nat → ClosedSurfaceType
classifyNonorientableDelta nothing = unclassified_surface
classifyNonorientableDelta (just zero) = unclassified_surface
classifyNonorientableDelta (just (suc crosscapRemainder)) =
  nonorientable_genus (suc crosscapRemainder)

classifyClosedSurface : Bool → Bool → Link3.SignedInteger →
  ClosedSurfaceType
classifyClosedSurface false orientable eulerCharacteristic =
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
    classified_vertex_count : Nat
    classified_edge_count : Nat
    classified_triangle_count : Nat
    classified_euler_characteristic : Link3.SignedInteger
    classified_orientation_computed : Bool
    classified_is_orientable : Bool
    classified_surface_type : ClosedSurfaceType
open ClassifiedBoundarySurface public

classifyBoundaryData : Boundary.BoundaryComponent3 → Bool → Bool →
  ClassifiedBoundarySurface
classifyBoundaryData currentBoundary orientationComputed orientable =
  classified_boundary_surface
    (Boundary.boundary_component_kind currentBoundary)
    (Boundary.source_face_class_numbers currentBoundary)
    (Boundary.boundary_vertex_count currentBoundary)
    (Boundary.boundary_edge_count currentBoundary)
    (Boundary.boundary_triangle_count currentBoundary)
    (Boundary.boundary_euler_characteristic currentBoundary)
    orientationComputed
    orientable
    (classifyClosedSurface orientationComputed orientable
      (Boundary.boundary_euler_characteristic currentBoundary))

classifyRealBoundaryAfterSummary : Boundary.BoundaryComponent3 →
  RealBoundaryOrientationSummary → ClassifiedBoundarySurface
classifyRealBoundaryAfterSummary currentBoundary orientationSummary =
  classifyBoundaryData currentBoundary
    (real_boundary_orientation_computed orientationSummary)
    (real_boundary_is_orientable orientationSummary)

classifyRealBoundaryComponent :
  List (FaceLinkClass 3 simplex_count) →
  List (FaceLinkClass 3 simplex_count) →
  List (Boundary.IndexedBoundaryFacet simplex_count) →
  ClassifiedBoundarySurface
classifyRealBoundaryComponent vertexClasses edgeClasses currentComponent =
  classifyRealBoundaryAfterSummary
    (Boundary.makeRealBoundaryComponent vertexClasses edgeClasses
      currentComponent)
    (analyseRealBoundaryComponent edgeClasses currentComponent)

classifiedRealBoundarySurfaces : Triangulation 3 simplex_count →
  List ClassifiedBoundarySurface
classifiedRealBoundarySurfaces
  {simplex_count = numberOfSimplices} currentTriangulation = map
  (classifyRealBoundaryComponent vertexClasses edgeClasses)
  (Boundary.realBoundaryFacetComponents currentTriangulation)
  where
  vertexClasses : List (FaceLinkClass 3 numberOfSimplices)
  vertexClasses = faceLinkClasses currentTriangulation 0

  edgeClasses : List (FaceLinkClass 3 numberOfSimplices)
  edgeClasses = faceLinkClasses currentTriangulation 1

classifyExistingBoundary : Boundary.BoundaryComponent3 →
  ClassifiedBoundarySurface
classifyExistingBoundary currentBoundary = classifyBoundaryData
  currentBoundary
  (Boundary.boundary_orientation_computed currentBoundary)
  (Boundary.boundary_is_orientable currentBoundary)

classifiedIdealBoundarySurfaces : Triangulation 3 simplex_count →
  List ClassifiedBoundarySurface
classifiedIdealBoundarySurfaces currentTriangulation = map
  classifyExistingBoundary
  (Boundary.idealBoundaryComponents currentTriangulation)

classifiedBoundarySurfaces : Triangulation 3 simplex_count →
  List ClassifiedBoundarySurface
classifiedBoundarySurfaces currentTriangulation =
  classifiedRealBoundarySurfaces currentTriangulation ++
  classifiedIdealBoundarySurfaces currentTriangulation
