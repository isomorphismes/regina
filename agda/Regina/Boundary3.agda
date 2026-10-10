{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- Real and ideal boundary-component structure in dimension three.
-- Derived from engine/triangulation/detail/skeleton-impl.h and
-- engine/triangulation/dim3/skeleton.cpp at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.Boundary3 where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks
import Regina.Embeddings as Embeddings
import Regina.Link3 as Link3
import Regina.VertexLinkSurface3 as VertexLinks

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

natMember : Nat → List Nat → Bool
natMember target [] = false
natMember target (candidate ∷ remaining) =
  nat_equal target candidate or natMember target remaining

insertNat : Nat → List Nat → List Nat
insertNat newValue existingValues with natMember newValue existingValues
... | true = existingValues
... | false = newValue ∷ existingValues

collectJustNats : List (Maybe Nat) → List Nat → List Nat
collectJustNats [] accumulatedValues = accumulatedValues
collectJustNats (nothing ∷ remainingValues) accumulatedValues =
  collectJustNats remainingValues accumulatedValues
collectJustNats (just currentValue ∷ remainingValues) accumulatedValues =
  collectJustNats remainingValues (insertNat currentValue accumulatedValues)

uniqueNats : List Nat → List Nat
uniqueNats values = collect values []
  where
  collect : List Nat → List Nat → List Nat
  collect [] accumulatedValues = accumulatedValues
  collect (headValue ∷ tailValues) accumulatedValues =
    collect tailValues (insertNat headValue accumulatedValues)

selectedVertices : Embeddings.FaceEmbedding 3 simplex_count → List (Fin 4)
selectedVertices currentEmbedding = filterElements
  (λ localVertex → lookup_vector
    (face_vertices (Embeddings.embedded_local_face currentEmbedding))
    localVertex)
  (all_fin 4)

firstEmbedding : FaceLinkClass 3 simplex_count →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count)
firstEmbedding currentClass with face_link_embeddings currentClass
... | [] = nothing
... | headEmbedding ∷ remainingEmbeddings = just headEmbedding

record IndexedBoundaryFacet (simplex_count : Nat) : Set where
  constructor indexed_boundary_facet
  field
    boundary_facet_class_number : Nat
    boundary_facet_class_value : FaceLinkClass 3 simplex_count
open IndexedBoundaryFacet public

indexBoundaryFacetsFrom : Triangulation 3 simplex_count → Nat →
  List (FaceLinkClass 3 simplex_count) →
  List (IndexedBoundaryFacet simplex_count)
indexBoundaryFacetsFrom currentTriangulation nextClassNumber [] = []
indexBoundaryFacetsFrom currentTriangulation nextClassNumber
  (currentFacetClass ∷ remainingFacetClasses)
  with Link3.faceLinkClassTouchesBoundary currentTriangulation currentFacetClass
... | true = indexed_boundary_facet nextClassNumber currentFacetClass ∷
  indexBoundaryFacetsFrom currentTriangulation (suc nextClassNumber)
    remainingFacetClasses
... | false = indexBoundaryFacetsFrom currentTriangulation
  (suc nextClassNumber) remainingFacetClasses

boundaryFacetClasses : Triangulation 3 simplex_count →
  List (IndexedBoundaryFacet simplex_count)
boundaryFacetClasses currentTriangulation = indexBoundaryFacetsFrom
  currentTriangulation zero (faceLinkClasses currentTriangulation 2)

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

vertexClassNumbersForVertices :
  List (FaceLinkClass 3 simplex_count) → Fin simplex_count → List (Fin 4) →
  List (Maybe Nat)
vertexClassNumbersForVertices vertexClasses simplexIndex localVertices = map
  (λ localVertex → Link3.findFaceLinkClassIndex
    (localVertexFace simplexIndex localVertex) vertexClasses)
  localVertices

edgeClassNumbersForThreeVertices :
  List (FaceLinkClass 3 simplex_count) → Fin simplex_count → List (Fin 4) →
  List (Maybe Nat)
edgeClassNumbersForThreeVertices edgeClasses simplexIndex [] = []
edgeClassNumbersForThreeVertices edgeClasses simplexIndex
  (firstVertex ∷ []) = []
edgeClassNumbersForThreeVertices edgeClasses simplexIndex
  (firstVertex ∷ secondVertex ∷ []) =
  Link3.findFaceLinkClassIndex
    (localEdgeFace simplexIndex firstVertex secondVertex) edgeClasses ∷ []
edgeClassNumbersForThreeVertices edgeClasses simplexIndex
  (firstVertex ∷ secondVertex ∷ thirdVertex ∷ remainingVertices) =
  Link3.findFaceLinkClassIndex
    (localEdgeFace simplexIndex firstVertex secondVertex) edgeClasses ∷
  Link3.findFaceLinkClassIndex
    (localEdgeFace simplexIndex firstVertex thirdVertex) edgeClasses ∷
  Link3.findFaceLinkClassIndex
    (localEdgeFace simplexIndex secondVertex thirdVertex) edgeClasses ∷ []

facetVertexNumbersAfterEmbedding :
  List (FaceLinkClass 3 simplex_count) →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count) → List Nat
facetVertexNumbersAfterEmbedding vertexClasses nothing = []
facetVertexNumbersAfterEmbedding vertexClasses (just currentEmbedding) =
  collectJustNats
    (vertexClassNumbersForVertices vertexClasses
      (face_simplex (Embeddings.embedded_local_face currentEmbedding))
      (selectedVertices currentEmbedding))
    []

facetEdgeNumbersAfterEmbedding :
  List (FaceLinkClass 3 simplex_count) →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count) → List Nat
facetEdgeNumbersAfterEmbedding edgeClasses nothing = []
facetEdgeNumbersAfterEmbedding edgeClasses (just currentEmbedding) =
  collectJustNats
    (edgeClassNumbersForThreeVertices edgeClasses
      (face_simplex (Embeddings.embedded_local_face currentEmbedding))
      (selectedVertices currentEmbedding))
    []

facetVertexClassNumbers : List (FaceLinkClass 3 simplex_count) →
  IndexedBoundaryFacet simplex_count → List Nat
facetVertexClassNumbers vertexClasses currentFacet =
  facetVertexNumbersAfterEmbedding vertexClasses
    (firstEmbedding (boundary_facet_class_value currentFacet))

facetEdgeClassNumbers : List (FaceLinkClass 3 simplex_count) →
  IndexedBoundaryFacet simplex_count → List Nat
facetEdgeClassNumbers edgeClasses currentFacet =
  facetEdgeNumbersAfterEmbedding edgeClasses
    (firstEmbedding (boundary_facet_class_value currentFacet))

listsShareNat : List Nat → List Nat → Bool
listsShareNat [] rightValues = false
listsShareNat (leftValue ∷ remainingLeftValues) rightValues =
  natMember leftValue rightValues or
  listsShareNat remainingLeftValues rightValues

indexedFacetEqual : IndexedBoundaryFacet simplex_count →
  IndexedBoundaryFacet simplex_count → Bool
indexedFacetEqual firstFacet secondFacet = nat_equal
  (boundary_facet_class_number firstFacet)
  (boundary_facet_class_number secondFacet)

facetMember : IndexedBoundaryFacet simplex_count →
  List (IndexedBoundaryFacet simplex_count) → Bool
facetMember targetFacet [] = false
facetMember targetFacet (currentFacet ∷ remainingFacets) =
  indexedFacetEqual targetFacet currentFacet or
  facetMember targetFacet remainingFacets

boundaryFacetsAdjacent : List (FaceLinkClass 3 simplex_count) →
  IndexedBoundaryFacet simplex_count → IndexedBoundaryFacet simplex_count → Bool
boundaryFacetsAdjacent edgeClasses firstFacet secondFacet =
  indexedFacetEqual firstFacet secondFacet or
  listsShareNat
    (facetEdgeClassNumbers edgeClasses firstFacet)
    (facetEdgeClassNumbers edgeClasses secondFacet)

expandBoundaryFacetsOnce : List (FaceLinkClass 3 simplex_count) →
  List (IndexedBoundaryFacet simplex_count) →
  List (IndexedBoundaryFacet simplex_count) →
  List (IndexedBoundaryFacet simplex_count)
expandBoundaryFacetsOnce edgeClasses facetUniverse reachedFacets =
  filterElements
    (λ candidateFacet → any
      (λ reachedFacet → boundaryFacetsAdjacent edgeClasses
        reachedFacet candidateFacet)
      reachedFacets)
    facetUniverse

expandBoundaryFacets : Nat → List (FaceLinkClass 3 simplex_count) →
  List (IndexedBoundaryFacet simplex_count) →
  List (IndexedBoundaryFacet simplex_count) →
  List (IndexedBoundaryFacet simplex_count)
expandBoundaryFacets zero edgeClasses facetUniverse reachedFacets = reachedFacets
expandBoundaryFacets (suc fuel) edgeClasses facetUniverse reachedFacets =
  expandBoundaryFacets fuel edgeClasses facetUniverse
    (expandBoundaryFacetsOnce edgeClasses facetUniverse reachedFacets)

boundaryFacetComponentFromSeed : List (FaceLinkClass 3 simplex_count) →
  List (IndexedBoundaryFacet simplex_count) →
  IndexedBoundaryFacet simplex_count →
  List (IndexedBoundaryFacet simplex_count)
boundaryFacetComponentFromSeed edgeClasses facetUniverse seedFacet =
  expandBoundaryFacets (length facetUniverse) edgeClasses facetUniverse
    (seedFacet ∷ [])

removeBoundaryFacets : List (IndexedBoundaryFacet simplex_count) →
  List (IndexedBoundaryFacet simplex_count) →
  List (IndexedBoundaryFacet simplex_count)
removeBoundaryFacets removedFacets = filterElements
  (λ candidateFacet → not (facetMember candidateFacet removedFacets))

partitionBoundaryFacets : Nat → List (FaceLinkClass 3 simplex_count) →
  List (IndexedBoundaryFacet simplex_count) →
  List (IndexedBoundaryFacet simplex_count) →
  List (List (IndexedBoundaryFacet simplex_count))
partitionBoundaryFacets zero edgeClasses facetUniverse remainingFacets = []
partitionBoundaryFacets (suc fuel) edgeClasses facetUniverse [] = []
partitionBoundaryFacets (suc fuel) edgeClasses facetUniverse
  (seedFacet ∷ remainingFacets)
  with boundaryFacetComponentFromSeed edgeClasses facetUniverse seedFacet
... | discoveredComponent = discoveredComponent ∷
  partitionBoundaryFacets fuel edgeClasses facetUniverse
    (removeBoundaryFacets discoveredComponent remainingFacets)

realBoundaryFacetComponents : Triangulation 3 simplex_count →
  List (List (IndexedBoundaryFacet simplex_count))
realBoundaryFacetComponents
  {simplex_count = numberOfSimplices} currentTriangulation =
  partitionBoundaryFacets (length facetUniverse) edgeClasses
    facetUniverse facetUniverse
  where
  edgeClasses : List (FaceLinkClass 3 numberOfSimplices)
  edgeClasses = faceLinkClasses currentTriangulation 1

  facetUniverse : List (IndexedBoundaryFacet numberOfSimplices)
  facetUniverse = boundaryFacetClasses currentTriangulation

data BoundaryComponentKind : Set where
  real_boundary_component : BoundaryComponentKind
  ideal_boundary_component : BoundaryComponentKind

record BoundaryComponent3 : Set where
  constructor boundary_component_three
  field
    boundary_component_kind : BoundaryComponentKind
    source_face_class_numbers : List Nat
    boundary_vertex_count : Nat
    boundary_edge_count : Nat
    boundary_triangle_count : Nat
    boundary_euler_characteristic : Link3.SignedInteger
    boundary_orientation_computed : Bool
    boundary_is_orientable : Bool
open BoundaryComponent3 public

componentFacetNumbers : List (IndexedBoundaryFacet simplex_count) → List Nat
componentFacetNumbers currentComponent = map
  boundary_facet_class_number currentComponent

componentVertexNumbers : List (FaceLinkClass 3 simplex_count) →
  List (IndexedBoundaryFacet simplex_count) → List Nat
componentVertexNumbers vertexClasses currentComponent = uniqueNats
  (concatMap (facetVertexClassNumbers vertexClasses) currentComponent)

componentEdgeNumbers : List (FaceLinkClass 3 simplex_count) →
  List (IndexedBoundaryFacet simplex_count) → List Nat
componentEdgeNumbers edgeClasses currentComponent = uniqueNats
  (concatMap (facetEdgeClassNumbers edgeClasses) currentComponent)

makeRealBoundaryComponent : List (FaceLinkClass 3 simplex_count) →
  List (FaceLinkClass 3 simplex_count) →
  List (IndexedBoundaryFacet simplex_count) → BoundaryComponent3
makeRealBoundaryComponent vertexClasses edgeClasses currentComponent =
  boundary_component_three
    real_boundary_component
    (componentFacetNumbers currentComponent)
    (length vertexNumbers)
    (length edgeNumbers)
    (length currentComponent)
    (Link3.naturalDifference
      (length vertexNumbers + length currentComponent)
      (length edgeNumbers))
    false
    false
  where
  vertexNumbers : List Nat
  vertexNumbers = componentVertexNumbers vertexClasses currentComponent

  edgeNumbers : List Nat
  edgeNumbers = componentEdgeNumbers edgeClasses currentComponent

realBoundaryComponents : Triangulation 3 simplex_count →
  List BoundaryComponent3
realBoundaryComponents
  {simplex_count = numberOfSimplices} currentTriangulation = map
  (makeRealBoundaryComponent vertexClasses edgeClasses)
  (realBoundaryFacetComponents currentTriangulation)
  where
  vertexClasses : List (FaceLinkClass 3 numberOfSimplices)
  vertexClasses = faceLinkClasses currentTriangulation 0

  edgeClasses : List (FaceLinkClass 3 numberOfSimplices)
  edgeClasses = faceLinkClasses currentTriangulation 1

makeIdealBoundaryComponent : Link3.VertexLinkSummary →
  VertexLinks.ExplicitVertexLink simplex_count → BoundaryComponent3
makeIdealBoundaryComponent currentSummary currentExplicitLink =
  boundary_component_three
    ideal_boundary_component
    (Link3.vertex_class_number currentSummary ∷ [])
    (VertexLinks.explicitLinkVertexCount currentExplicitLink)
    (VertexLinks.explicitLinkEdgeCount currentExplicitLink)
    (VertexLinks.explicitLinkTriangleCount currentExplicitLink)
    (VertexLinks.explicitLinkEulerCharacteristic currentExplicitLink)
    true
    (VertexLinks.explicit_link_is_orientable currentExplicitLink)

idealBoundaryComponentsFrom : List Link3.VertexLinkSummary →
  List (VertexLinks.ExplicitVertexLink simplex_count) →
  List BoundaryComponent3
idealBoundaryComponentsFrom [] explicitLinks = []
idealBoundaryComponentsFrom summaries [] = []
idealBoundaryComponentsFrom (currentSummary ∷ remainingSummaries)
  (currentExplicitLink ∷ remainingExplicitLinks)
  with Link3.summaryIsIdeal currentSummary
... | true = makeIdealBoundaryComponent currentSummary currentExplicitLink ∷
  idealBoundaryComponentsFrom remainingSummaries remainingExplicitLinks
... | false = idealBoundaryComponentsFrom
  remainingSummaries remainingExplicitLinks

idealBoundaryComponents : Triangulation 3 simplex_count →
  List BoundaryComponent3
idealBoundaryComponents currentTriangulation = idealBoundaryComponentsFrom
  (Link3.threeDimensionalVertexLinkSummaries currentTriangulation)
  (VertexLinks.explicitVertexLinks currentTriangulation)

boundaryComponents : Triangulation 3 simplex_count → List BoundaryComponent3
boundaryComponents currentTriangulation =
  realBoundaryComponents currentTriangulation ++
  idealBoundaryComponents currentTriangulation

isRealBoundaryComponent : BoundaryComponent3 → Bool
isRealBoundaryComponent currentComponent
  with boundary_component_kind currentComponent
... | real_boundary_component = true
... | ideal_boundary_component = false

isIdealBoundaryComponent : BoundaryComponent3 → Bool
isIdealBoundaryComponent currentComponent
  with boundary_component_kind currentComponent
... | real_boundary_component = false
... | ideal_boundary_component = true

boundaryComponentCount : Triangulation 3 simplex_count → Nat
boundaryComponentCount currentTriangulation =
  length (boundaryComponents currentTriangulation)

realBoundaryComponentCount : Triangulation 3 simplex_count → Nat
realBoundaryComponentCount currentTriangulation = count_matching
  isRealBoundaryComponent (boundaryComponents currentTriangulation)

idealBoundaryComponentCount : Triangulation 3 simplex_count → Nat
idealBoundaryComponentCount currentTriangulation = count_matching
  isIdealBoundaryComponent (boundaryComponents currentTriangulation)
