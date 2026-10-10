{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- Exact dimension-three codimension-two traversal order.
-- Derived from calculateFaces<dim-2>() in
-- engine/triangulation/detail/skeleton-impl.h and the edge tables in
-- engine/triangulation/facenumbering.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.ExactEdgeLinks3 where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Skeleton
import Regina.Components as Components
import Regina.Embeddings as Embeddings
import Regina.FaceLinks as FaceLinks
import Regina.SubfaceIncidence3 as Subfaces

private
  variable
    simplex_count : Nat

appendElement : {element : Set} → List element → element → List element
appendElement existingElements newElement =
  existingElements ++ (newElement ∷ [])

lookupList : {element : Set} → Nat → List element → Maybe element
lookupList zero [] = nothing
lookupList zero (headElement ∷ remainingElements) = just headElement
lookupList (suc requestedIndex) [] = nothing
lookupList (suc requestedIndex) (headElement ∷ remainingElements) =
  lookupList requestedIndex remainingElements

record SimplexOrientationLabel3 (simplex_count : Nat) : Set where
  constructor simplex_orientation_label_three
  field
    labelled_simplex : Fin simplex_count
    labelled_simplex_orientation : Components.Orientation
open SimplexOrientationLabel3 public

findOrientationLabel : Fin simplex_count →
  List (SimplexOrientationLabel3 simplex_count) →
  Maybe (SimplexOrientationLabel3 simplex_count)
findOrientationLabel requestedSimplex [] = nothing
findOrientationLabel requestedSimplex
  (currentLabel ∷ remainingLabels)
  with fin_equal requestedSimplex (labelled_simplex currentLabel)
... | true = just currentLabel
... | false = findOrientationLabel requestedSimplex remainingLabels

orientationForSimplex : Fin simplex_count →
  List (SimplexOrientationLabel3 simplex_count) →
  Maybe Components.Orientation
orientationForSimplex requestedSimplex labels
  with findOrientationLabel requestedSimplex labels
... | nothing = nothing
... | just currentLabel = just
  (labelled_simplex_orientation currentLabel)

record SimplexOrientationState3 (simplex_count : Nat) : Set where
  constructor simplex_orientation_state_three
  field
    simplex_orientation_labels :
      List (SimplexOrientationLabel3 simplex_count)
    pending_orientation_labels :
      List (SimplexOrientationLabel3 simplex_count)
    simplex_orientation_conflict : Bool
open SimplexOrientationState3 public

transportSimplexOrientation : Components.Orientation →
  Gluing 3 simplex_count → Components.Orientation
transportSimplexOrientation sourceOrientation outwardGluing
  with Components.permutationEven (vertex_permutation outwardGluing)
... | true = Components.flipOrientation sourceOrientation
... | false = sourceOrientation

recordProposedOrientation : SimplexOrientationState3 simplex_count →
  SimplexOrientationLabel3 simplex_count →
  Maybe (SimplexOrientationLabel3 simplex_count) →
  SimplexOrientationState3 simplex_count
recordProposedOrientation currentState proposedLabel nothing =
  simplex_orientation_state_three
    (appendElement (simplex_orientation_labels currentState) proposedLabel)
    (appendElement (pending_orientation_labels currentState) proposedLabel)
    (simplex_orientation_conflict currentState)
recordProposedOrientation currentState proposedLabel (just existingLabel) =
  simplex_orientation_state_three
    (simplex_orientation_labels currentState)
    (pending_orientation_labels currentState)
    (simplex_orientation_conflict currentState or not
      (Components.orientationEqual
        (labelled_simplex_orientation proposedLabel)
        (labelled_simplex_orientation existingLabel)))

processOrientationLookup : Triangulation 3 simplex_count →
  SimplexOrientationLabel3 simplex_count →
  SimplexOrientationState3 simplex_count →
  Maybe (Gluing 3 simplex_count) →
  SimplexOrientationState3 simplex_count
processOrientationLookup {simplex_count = numberOfSimplices}
  currentTriangulation sourceLabel currentState nothing = currentState
processOrientationLookup {simplex_count = numberOfSimplices}
  currentTriangulation sourceLabel currentState (just outwardGluing) =
  recordProposedOrientation currentState proposedLabel
    (findOrientationLabel (adjacent_simplex outwardGluing)
      (simplex_orientation_labels currentState))
  where
  proposedLabel : SimplexOrientationLabel3 numberOfSimplices
  proposedLabel = simplex_orientation_label_three
    (adjacent_simplex outwardGluing)
    (transportSimplexOrientation
      (labelled_simplex_orientation sourceLabel) outwardGluing)

processOrientationFacet : Triangulation 3 simplex_count →
  SimplexOrientationLabel3 simplex_count → Fin 4 →
  SimplexOrientationState3 simplex_count →
  SimplexOrientationState3 simplex_count
processOrientationFacet currentTriangulation sourceLabel localFacet
  currentState = processOrientationLookup currentTriangulation sourceLabel
  currentState
  (adjacency (raw_state currentTriangulation)
    (facet (labelled_simplex sourceLabel) localFacet))

processOrientationFacets : Triangulation 3 simplex_count →
  SimplexOrientationLabel3 simplex_count → List (Fin 4) →
  SimplexOrientationState3 simplex_count →
  SimplexOrientationState3 simplex_count
processOrientationFacets currentTriangulation sourceLabel [] currentState =
  currentState
processOrientationFacets currentTriangulation sourceLabel
  (localFacet ∷ remainingFacets) currentState =
  processOrientationFacets currentTriangulation sourceLabel remainingFacets
    (processOrientationFacet currentTriangulation sourceLabel localFacet
      currentState)

walkOrientationQueueByFuel : Nat → Triangulation 3 simplex_count →
  SimplexOrientationState3 simplex_count →
  SimplexOrientationState3 simplex_count
walkOrientationQueueByFuel zero currentTriangulation currentState = currentState
walkOrientationQueueByFuel (suc remainingFuel) currentTriangulation currentState
  with pending_orientation_labels currentState
... | [] = currentState
... | sourceLabel ∷ remainingQueue = walkOrientationQueueByFuel
  remainingFuel currentTriangulation
  (processOrientationFacets currentTriangulation sourceLabel (all_fin 4)
    (simplex_orientation_state_three
      (simplex_orientation_labels currentState)
      remainingQueue
      (simplex_orientation_conflict currentState)))

startOrientationRoot : Nat → Triangulation 3 simplex_count →
  SimplexOrientationState3 simplex_count → Fin simplex_count →
  SimplexOrientationState3 simplex_count
startOrientationRoot {simplex_count = numberOfSimplices} fuel
  currentTriangulation currentState rootSimplex
  with findOrientationLabel rootSimplex
    (simplex_orientation_labels currentState)
... | just existingLabel = currentState
... | nothing = walkOrientationQueueByFuel fuel currentTriangulation
  (simplex_orientation_state_three
    (appendElement (simplex_orientation_labels currentState) rootLabel)
    (rootLabel ∷ [])
    (simplex_orientation_conflict currentState))
  where
  rootLabel : SimplexOrientationLabel3 numberOfSimplices
  rootLabel = simplex_orientation_label_three rootSimplex Components.positive

processOrientationRoots : Nat → Triangulation 3 simplex_count →
  SimplexOrientationState3 simplex_count → List (Fin simplex_count) →
  SimplexOrientationState3 simplex_count
processOrientationRoots fuel currentTriangulation currentState [] = currentState
processOrientationRoots fuel currentTriangulation currentState
  (rootSimplex ∷ remainingRoots) = processOrientationRoots fuel
  currentTriangulation
  (startOrientationRoot fuel currentTriangulation currentState rootSimplex)
  remainingRoots

simplexOrientationState3 : Triangulation 3 simplex_count →
  SimplexOrientationState3 simplex_count
simplexOrientationState3 {simplex_count = numberOfSimplices}
  currentTriangulation = processOrientationRoots numberOfSimplices
  currentTriangulation
  (simplex_orientation_state_three [] [] false)
  (all_fin numberOfSimplices)

simplexOrientationLabels3 : Triangulation 3 simplex_count →
  List (SimplexOrientationLabel3 simplex_count)
simplexOrientationLabels3 currentTriangulation =
  simplex_orientation_labels (simplexOrientationState3 currentTriangulation)

simplexOrientationConflict3 : Triangulation 3 simplex_count → Bool
simplexOrientationConflict3 currentTriangulation =
  simplex_orientation_conflict (simplexOrientationState3 currentTriangulation)

vertexZero : Fin 4
vertexZero = fzero

vertexOne : Fin 4
vertexOne = fsuc fzero

vertexTwo : Fin 4
vertexTwo = fsuc (fsuc fzero)

vertexThree : Fin 4
vertexThree = fsuc (fsuc (fsuc fzero))

-- Exact FaceNumberingTables<3,1>::faceOrdering entries.
evenEdgeOrdering : Nat → Maybe (List (Fin 4))
evenEdgeOrdering zero =
  just (vertexZero ∷ vertexOne ∷ vertexTwo ∷ vertexThree ∷ [])
evenEdgeOrdering (suc zero) =
  just (vertexZero ∷ vertexTwo ∷ vertexThree ∷ vertexOne ∷ [])
evenEdgeOrdering (suc (suc zero)) =
  just (vertexZero ∷ vertexThree ∷ vertexOne ∷ vertexTwo ∷ [])
evenEdgeOrdering (suc (suc (suc zero))) =
  just (vertexOne ∷ vertexTwo ∷ vertexZero ∷ vertexThree ∷ [])
evenEdgeOrdering (suc (suc (suc (suc zero)))) =
  just (vertexOne ∷ vertexThree ∷ vertexTwo ∷ vertexZero ∷ [])
evenEdgeOrdering (suc (suc (suc (suc (suc zero))))) =
  just (vertexTwo ∷ vertexThree ∷ vertexZero ∷ vertexOne ∷ [])
evenEdgeOrdering (suc (suc (suc (suc (suc (suc remaining)))))) = nothing

orientEdgeOrdering : Components.Orientation →
  Maybe (List (Fin 4)) → Maybe (List (Fin 4))
orientEdgeOrdering sourceOrientation nothing = nothing
orientEdgeOrdering Components.positive (just orderingVertices) =
  just orderingVertices
orientEdgeOrdering Components.negative (just orderingVertices) =
  just (FaceLinks.swapLastTwo orderingVertices)

edgeOrderingForSimplex : Triangulation 3 simplex_count →
  Fin simplex_count → Nat → Maybe (List (Fin 4))
edgeOrderingForSimplex currentTriangulation simplexIndex edgeNumber
  with orientationForSimplex simplexIndex
    (simplexOrientationLabels3 currentTriangulation)
... | nothing = nothing
... | just sourceOrientation = orientEdgeOrdering sourceOrientation
  (evenEdgeOrdering edgeNumber)

edgeFaceFromOrdering : Fin simplex_count → List (Fin 4) →
  LocalFace 3 simplex_count
edgeFaceFromOrdering simplexIndex orderingVertices =
  Subfaces.localFaceFromVertices simplexIndex
    (Subfaces.takeElements 2 orderingVertices)

initialEdgeEmbeddingAfterOrdering : Fin simplex_count →
  Maybe (List (Fin 4)) →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count)
initialEdgeEmbeddingAfterOrdering simplexIndex nothing = nothing
initialEdgeEmbeddingAfterOrdering simplexIndex (just orderingVertices) = just
  (Embeddings.face_embedding
    (edgeFaceFromOrdering simplexIndex orderingVertices)
    orderingVertices)

initialEdgeEmbedding : Triangulation 3 simplex_count →
  Fin simplex_count → Nat →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count)
initialEdgeEmbedding currentTriangulation simplexIndex edgeNumber =
  initialEdgeEmbeddingAfterOrdering simplexIndex
    (edgeOrderingForSimplex currentTriangulation simplexIndex edgeNumber)

data EdgeWalkMode3 : Set where
  edge_walk_forward : EdgeWalkMode3
  edge_walk_backward : EdgeWalkMode3

exitPosition : EdgeWalkMode3 → Nat
exitPosition edge_walk_forward = 2
exitPosition edge_walk_backward = 3

data EdgeWalkStep3 (simplex_count : Nat) : Set where
  edge_step_boundary : Facet 3 simplex_count → EdgeWalkStep3 simplex_count
  edge_step_crossed : Embeddings.FaceEmbedding 3 simplex_count →
    EdgeWalkStep3 simplex_count
  edge_step_invalid : EdgeWalkStep3 simplex_count

edgeStepAfterExitVertex : Triangulation 3 simplex_count →
  Embeddings.FaceEmbedding 3 simplex_count →
  Maybe (Fin 4) → EdgeWalkStep3 simplex_count
edgeStepAfterExitVertex currentTriangulation currentEmbedding nothing =
  edge_step_invalid
edgeStepAfterExitVertex currentTriangulation currentEmbedding
  (just exitFacet)
  with lookup_vector
    (face_vertices (Embeddings.embedded_local_face currentEmbedding))
    exitFacet
... | true = edge_step_invalid
... | false with adjacency (raw_state currentTriangulation)
  (facet
    (face_simplex (Embeddings.embedded_local_face currentEmbedding))
    exitFacet)
... | nothing = edge_step_boundary
  (facet
    (face_simplex (Embeddings.embedded_local_face currentEmbedding))
    exitFacet)
... | just outwardGluing
  with FaceLinks.crossFaceLinkEmbedding 3 1 currentTriangulation
    currentEmbedding exitFacet
...   | nothing = edge_step_invalid
...   | just crossedEmbedding = edge_step_crossed crossedEmbedding

edgeWalkStep : EdgeWalkMode3 → Triangulation 3 simplex_count →
  Embeddings.FaceEmbedding 3 simplex_count → EdgeWalkStep3 simplex_count
edgeWalkStep walkMode currentTriangulation currentEmbedding =
  edgeStepAfterExitVertex currentTriangulation currentEmbedding
    (lookupList (exitPosition walkMode)
      (Embeddings.ordered_simplex_vertices currentEmbedding))

insertWalkEmbedding : EdgeWalkMode3 →
  Embeddings.FaceEmbedding 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (Embeddings.FaceEmbedding 3 simplex_count)
insertWalkEmbedding edge_walk_forward newEmbedding existingEmbeddings =
  appendElement existingEmbeddings newEmbedding
insertWalkEmbedding edge_walk_backward newEmbedding existingEmbeddings =
  newEmbedding ∷ existingEmbeddings

record EdgeDirectionResult3 (simplex_count : Nat) : Set where
  constructor edge_direction_result_three
  field
    direction_embeddings :
      List (Embeddings.FaceEmbedding 3 simplex_count)
    direction_boundary_facet : Maybe (Facet 3 simplex_count)
    direction_revisited : Bool
    direction_bad_identification : Bool
    direction_complete : Bool
open EdgeDirectionResult3 public

finishBoundaryWalk :
  List (Embeddings.FaceEmbedding 3 simplex_count) → Bool →
  Facet 3 simplex_count → EdgeDirectionResult3 simplex_count
finishBoundaryWalk currentEmbeddings badIdentification boundaryFacet =
  edge_direction_result_three currentEmbeddings
    (just boundaryFacet) false badIdentification true

finishRevisitedWalk :
  List (Embeddings.FaceEmbedding 3 simplex_count) → Bool →
  Embeddings.FaceEmbedding 3 simplex_count →
  Embeddings.FaceEmbedding 3 simplex_count →
  EdgeDirectionResult3 simplex_count
finishRevisitedWalk currentEmbeddings badIdentification
  previousEmbedding returnedEmbedding = edge_direction_result_three
  currentEmbeddings nothing true
  (badIdentification or not
    (FaceLinks.vertexListsEqual
      (Embeddings.ordered_simplex_vertices previousEmbedding)
      (Embeddings.ordered_simplex_vertices returnedEmbedding)))
  true

walkEdgeByFuel : Nat → EdgeWalkMode3 →
  Triangulation 3 simplex_count →
  Embeddings.FaceEmbedding 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Bool →
  EdgeDirectionResult3 simplex_count
walkEdgeByFuel zero walkMode currentTriangulation activeEmbedding
  visitedEmbeddings badIdentification = edge_direction_result_three
  visitedEmbeddings nothing false badIdentification false
walkEdgeByFuel (suc remainingFuel) walkMode currentTriangulation
  activeEmbedding visitedEmbeddings badIdentification
  with edgeWalkStep walkMode currentTriangulation activeEmbedding
... | edge_step_invalid = edge_direction_result_three
  visitedEmbeddings nothing false badIdentification false
... | edge_step_boundary boundaryFacet = finishBoundaryWalk
  visitedEmbeddings badIdentification boundaryFacet
... | edge_step_crossed crossedEmbedding
  with Embeddings.findEmbeddingForFace
    (Embeddings.embedded_local_face crossedEmbedding) visitedEmbeddings
...   | just previousEmbedding = finishRevisitedWalk
  visitedEmbeddings badIdentification previousEmbedding crossedEmbedding
...   | nothing = walkEdgeByFuel remainingFuel walkMode currentTriangulation
  crossedEmbedding
  (insertWalkEmbedding walkMode crossedEmbedding visitedEmbeddings)
  badIdentification

data EdgeLinkShape3 : Set where
  edge_link_path : EdgeLinkShape3
  edge_link_cycle : EdgeLinkShape3
  edge_link_incomplete : EdgeLinkShape3

shapeFromTerminations : Maybe (Facet 3 simplex_count) → Bool →
  Maybe (Facet 3 simplex_count) → Bool → EdgeLinkShape3
shapeFromTerminations (just firstBoundary) false
  (just lastBoundary) false = edge_link_path
shapeFromTerminations nothing true nothing true = edge_link_cycle
shapeFromTerminations firstBoundary firstRevisited
  lastBoundary lastRevisited = edge_link_incomplete

shapeComplete : EdgeLinkShape3 → Bool
shapeComplete edge_link_path = true
shapeComplete edge_link_cycle = true
shapeComplete edge_link_incomplete = false

record OrderedEdgeLink3 (simplex_count : Nat) : Set where
  constructor ordered_edge_link_three
  field
    ordered_edge_class_number : Nat
    ordered_edge_seed_simplex : Fin simplex_count
    ordered_edge_seed_number : Nat
    ordered_edge_embeddings :
      List (Embeddings.FaceEmbedding 3 simplex_count)
    ordered_edge_first_boundary : Maybe (Facet 3 simplex_count)
    ordered_edge_last_boundary : Maybe (Facet 3 simplex_count)
    ordered_edge_shape : EdgeLinkShape3
    ordered_edge_bad_identification : Bool
    ordered_edge_walk_complete : Bool
open OrderedEdgeLink3 public

assembleOrderedEdgeLink : Nat → Fin simplex_count → Nat →
  EdgeDirectionResult3 simplex_count →
  EdgeDirectionResult3 simplex_count → OrderedEdgeLink3 simplex_count
assembleOrderedEdgeLink classNumber seedSimplex seedEdgeNumber
  forwardResult backwardResult = ordered_edge_link_three
  classNumber seedSimplex seedEdgeNumber
  (direction_embeddings backwardResult)
  (direction_boundary_facet backwardResult)
  (direction_boundary_facet forwardResult)
  currentShape
  (direction_bad_identification forwardResult or
   direction_bad_identification backwardResult)
  (direction_complete forwardResult and
   direction_complete backwardResult and shapeComplete currentShape)
  where
  currentShape : EdgeLinkShape3
  currentShape = shapeFromTerminations
    (direction_boundary_facet backwardResult)
    (direction_revisited backwardResult)
    (direction_boundary_facet forwardResult)
    (direction_revisited forwardResult)

buildOrderedEdgeLink : Nat → Nat → Triangulation 3 simplex_count →
  Fin simplex_count → Nat →
  Embeddings.FaceEmbedding 3 simplex_count → OrderedEdgeLink3 simplex_count
buildOrderedEdgeLink {simplex_count = numberOfSimplices}
  classNumber walkFuel currentTriangulation seedSimplex seedEdgeNumber
  initialEmbedding = assembleOrderedEdgeLink classNumber seedSimplex
  seedEdgeNumber forwardResult backwardResult
  where
  forwardResult : EdgeDirectionResult3 numberOfSimplices
  forwardResult = walkEdgeByFuel walkFuel edge_walk_forward
    currentTriangulation initialEmbedding (initialEmbedding ∷ []) false

  backwardResult : EdgeDirectionResult3 numberOfSimplices
  backwardResult = walkEdgeByFuel walkFuel edge_walk_backward
    currentTriangulation initialEmbedding
    (direction_embeddings forwardResult)
    (direction_bad_identification forwardResult)

edgeFaceSeenInClass : LocalFace 3 simplex_count →
  OrderedEdgeLink3 simplex_count → Bool
edgeFaceSeenInClass requestedFace currentClass = any
  (λ currentEmbedding → local_face_equal requestedFace
    (Embeddings.embedded_local_face currentEmbedding))
  (ordered_edge_embeddings currentClass)

edgeFaceSeen : LocalFace 3 simplex_count →
  List (OrderedEdgeLink3 simplex_count) → Bool
edgeFaceSeen requestedFace classes = any
  (edgeFaceSeenInClass requestedFace) classes

record OrderedEdgePartitionState3 (simplex_count : Nat) : Set where
  constructor ordered_edge_partition_state_three
  field
    partition_edge_classes : List (OrderedEdgeLink3 simplex_count)
    partition_next_class_number : Nat
    partition_edge_complete : Bool
open OrderedEdgePartitionState3 public

processEdgeSeedAfterEmbedding : Nat → Triangulation 3 simplex_count →
  Fin simplex_count → Nat → OrderedEdgePartitionState3 simplex_count →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count) →
  OrderedEdgePartitionState3 simplex_count
processEdgeSeedAfterEmbedding {simplex_count = numberOfSimplices}
  walkFuel currentTriangulation simplexIndex edgeNumber currentState nothing =
  ordered_edge_partition_state_three
    (partition_edge_classes currentState)
    (partition_next_class_number currentState)
    false
processEdgeSeedAfterEmbedding {simplex_count = numberOfSimplices}
  walkFuel currentTriangulation simplexIndex edgeNumber currentState
  (just seedEmbedding)
  with edgeFaceSeen (Embeddings.embedded_local_face seedEmbedding)
    (partition_edge_classes currentState)
... | true = currentState
... | false = ordered_edge_partition_state_three
  (appendElement (partition_edge_classes currentState) newClass)
  (suc (partition_next_class_number currentState))
  (partition_edge_complete currentState and
    ordered_edge_walk_complete newClass)
  where
  newClass : OrderedEdgeLink3 numberOfSimplices
  newClass = buildOrderedEdgeLink
    (partition_next_class_number currentState)
    walkFuel currentTriangulation simplexIndex edgeNumber seedEmbedding

processEdgeSeed : Nat → Triangulation 3 simplex_count →
  Fin simplex_count → Nat → OrderedEdgePartitionState3 simplex_count →
  OrderedEdgePartitionState3 simplex_count
processEdgeSeed walkFuel currentTriangulation simplexIndex edgeNumber
  currentState = processEdgeSeedAfterEmbedding walkFuel currentTriangulation
  simplexIndex edgeNumber currentState
  (initialEdgeEmbedding currentTriangulation simplexIndex edgeNumber)

processSimplexEdges : Nat → Triangulation 3 simplex_count →
  Fin simplex_count → List Nat → OrderedEdgePartitionState3 simplex_count →
  OrderedEdgePartitionState3 simplex_count
processSimplexEdges walkFuel currentTriangulation simplexIndex [] currentState =
  currentState
processSimplexEdges walkFuel currentTriangulation simplexIndex
  (edgeNumber ∷ remainingEdgeNumbers) currentState =
  processSimplexEdges walkFuel currentTriangulation simplexIndex
    remainingEdgeNumbers
    (processEdgeSeed walkFuel currentTriangulation simplexIndex edgeNumber
      currentState)

processAllSimplexEdges : Nat → Triangulation 3 simplex_count →
  List (Fin simplex_count) → OrderedEdgePartitionState3 simplex_count →
  OrderedEdgePartitionState3 simplex_count
processAllSimplexEdges walkFuel currentTriangulation [] currentState =
  currentState
processAllSimplexEdges walkFuel currentTriangulation
  (simplexIndex ∷ remainingSimplices) currentState =
  processAllSimplexEdges walkFuel currentTriangulation remainingSimplices
    (processSimplexEdges walkFuel currentTriangulation simplexIndex
      (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) currentState)

orderedEdgePartitionState3 : Triangulation 3 simplex_count →
  OrderedEdgePartitionState3 simplex_count
orderedEdgePartitionState3 {simplex_count = numberOfSimplices}
  currentTriangulation = processAllSimplexEdges (numberOfSimplices * 6)
  currentTriangulation (all_fin numberOfSimplices)
  (ordered_edge_partition_state_three [] 0 true)

orderedEdgeLinks3 : Triangulation 3 simplex_count →
  List (OrderedEdgeLink3 simplex_count)
orderedEdgeLinks3 currentTriangulation =
  partition_edge_classes (orderedEdgePartitionState3 currentTriangulation)

orderedEdgeDegrees : Triangulation 3 simplex_count → List Nat
orderedEdgeDegrees currentTriangulation = map
  (λ currentClass → length (ordered_edge_embeddings currentClass))
  (orderedEdgeLinks3 currentTriangulation)

orderedEdgeShapes : Triangulation 3 simplex_count → List EdgeLinkShape3
orderedEdgeShapes currentTriangulation = map ordered_edge_shape
  (orderedEdgeLinks3 currentTriangulation)

orderedEdgeSeedNumbers : Triangulation 3 simplex_count → List Nat
orderedEdgeSeedNumbers currentTriangulation = map ordered_edge_seed_number
  (orderedEdgeLinks3 currentTriangulation)

orderedEdgeBadIdentificationCount : Triangulation 3 simplex_count → Nat
orderedEdgeBadIdentificationCount currentTriangulation = count_matching
  ordered_edge_bad_identification (orderedEdgeLinks3 currentTriangulation)

allOrderedEdgeWalksComplete : Triangulation 3 simplex_count → Bool
allOrderedEdgeWalksComplete currentTriangulation =
  partition_edge_complete (orderedEdgePartitionState3 currentTriangulation) and
  all ordered_edge_walk_complete (orderedEdgeLinks3 currentTriangulation)

sumNaturals : List Nat → Nat
sumNaturals [] = zero
sumNaturals (headValue ∷ remainingValues) =
  headValue + sumNaturals remainingValues

orderedEdgeOccurrencesComplete : Triangulation 3 simplex_count → Bool
orderedEdgeOccurrencesComplete {simplex_count = numberOfSimplices}
  currentTriangulation = nat_equal
  (sumNaturals (orderedEdgeDegrees currentTriangulation))
  (numberOfSimplices * 6)

embeddingEqual : Embeddings.FaceEmbedding 3 simplex_count →
  Embeddings.FaceEmbedding 3 simplex_count → Bool
embeddingEqual firstEmbedding secondEmbedding =
  local_face_equal
    (Embeddings.embedded_local_face firstEmbedding)
    (Embeddings.embedded_local_face secondEmbedding) and
  FaceLinks.vertexListsEqual
    (Embeddings.ordered_simplex_vertices firstEmbedding)
    (Embeddings.ordered_simplex_vertices secondEmbedding)

stepCrossesTo : Triangulation 3 simplex_count →
  EdgeWalkMode3 → Embeddings.FaceEmbedding 3 simplex_count →
  Embeddings.FaceEmbedding 3 simplex_count → Bool
stepCrossesTo currentTriangulation walkMode firstEmbedding secondEmbedding
  with edgeWalkStep walkMode currentTriangulation firstEmbedding
... | edge_step_crossed crossedEmbedding =
  embeddingEqual crossedEmbedding secondEmbedding
... | edge_step_boundary boundaryFacet = false
... | edge_step_invalid = false

consecutiveForwardCompatible : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Bool
consecutiveForwardCompatible currentTriangulation [] = true
consecutiveForwardCompatible currentTriangulation (onlyEmbedding ∷ []) = true
consecutiveForwardCompatible currentTriangulation
  (firstEmbedding ∷ secondEmbedding ∷ remainingEmbeddings) =
  stepCrossesTo currentTriangulation edge_walk_forward
    firstEmbedding secondEmbedding and
  consecutiveForwardCompatible currentTriangulation
    (secondEmbedding ∷ remainingEmbeddings)

firstEmbeddingOf : List (Embeddings.FaceEmbedding 3 simplex_count) →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count)
firstEmbeddingOf [] = nothing
firstEmbeddingOf (firstEmbedding ∷ remainingEmbeddings) = just firstEmbedding

lastEmbeddingOf : List (Embeddings.FaceEmbedding 3 simplex_count) →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count)
lastEmbeddingOf [] = nothing
lastEmbeddingOf (onlyEmbedding ∷ []) = just onlyEmbedding
lastEmbeddingOf (firstEmbedding ∷ secondEmbedding ∷ remainingEmbeddings) =
  lastEmbeddingOf (secondEmbedding ∷ remainingEmbeddings)

maybeFacetEqual : Maybe (Facet 3 simplex_count) →
  Maybe (Facet 3 simplex_count) → Bool
maybeFacetEqual nothing nothing = true
maybeFacetEqual nothing (just rightFacet) = false
maybeFacetEqual (just leftFacet) nothing = false
maybeFacetEqual (just leftFacet) (just rightFacet) =
  facet_equal leftFacet rightFacet

stepBoundaryMatches : Triangulation 3 simplex_count →
  EdgeWalkMode3 → Maybe (Embeddings.FaceEmbedding 3 simplex_count) →
  Maybe (Facet 3 simplex_count) → Bool
stepBoundaryMatches currentTriangulation walkMode nothing boundaryFacet = false
stepBoundaryMatches currentTriangulation walkMode
  (just currentEmbedding) boundaryFacet
  with edgeWalkStep walkMode currentTriangulation currentEmbedding
... | edge_step_boundary actualBoundary =
  maybeFacetEqual (just actualBoundary) boundaryFacet
... | edge_step_crossed crossedEmbedding = false
... | edge_step_invalid = false

cycleClosureMatches : Triangulation 3 simplex_count →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count) →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count) → Bool
cycleClosureMatches currentTriangulation nothing lastEmbedding = false
cycleClosureMatches currentTriangulation firstEmbedding nothing = false
cycleClosureMatches currentTriangulation (just firstEmbedding)
  (just lastEmbedding) =
  stepCrossesTo currentTriangulation edge_walk_forward
    lastEmbedding firstEmbedding and
  stepCrossesTo currentTriangulation edge_walk_backward
    firstEmbedding lastEmbedding

validateStructureByShape : EdgeLinkShape3 →
  Triangulation 3 simplex_count → OrderedEdgeLink3 simplex_count →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count) →
  Maybe (Embeddings.FaceEmbedding 3 simplex_count) → Bool → Bool
validateStructureByShape edge_link_path currentTriangulation currentClass
  firstEmbedding lastEmbedding consecutive = consecutive and
  stepBoundaryMatches currentTriangulation edge_walk_backward firstEmbedding
    (ordered_edge_first_boundary currentClass) and
  stepBoundaryMatches currentTriangulation edge_walk_forward lastEmbedding
    (ordered_edge_last_boundary currentClass)
validateStructureByShape edge_link_cycle currentTriangulation currentClass
  firstEmbedding lastEmbedding consecutive = consecutive and
  cycleClosureMatches currentTriangulation firstEmbedding lastEmbedding
validateStructureByShape edge_link_incomplete currentTriangulation currentClass
  firstEmbedding lastEmbedding consecutive = false

orderedEdgeClassStructureValid : Triangulation 3 simplex_count →
  OrderedEdgeLink3 simplex_count → Bool
orderedEdgeClassStructureValid {simplex_count = numberOfSimplices}
  currentTriangulation currentClass = validateStructureByShape
  (ordered_edge_shape currentClass) currentTriangulation currentClass
  firstEmbedding lastEmbedding consecutive
  where
  currentEmbeddings : List (Embeddings.FaceEmbedding 3 numberOfSimplices)
  currentEmbeddings = ordered_edge_embeddings currentClass

  consecutive : Bool
  consecutive = consecutiveForwardCompatible currentTriangulation
    currentEmbeddings

  firstEmbedding : Maybe (Embeddings.FaceEmbedding 3 numberOfSimplices)
  firstEmbedding = firstEmbeddingOf currentEmbeddings

  lastEmbedding : Maybe (Embeddings.FaceEmbedding 3 numberOfSimplices)
  lastEmbedding = lastEmbeddingOf currentEmbeddings

allOrderedEdgeStructuresValid : Triangulation 3 simplex_count → Bool
allOrderedEdgeStructuresValid currentTriangulation = all
  (orderedEdgeClassStructureValid currentTriangulation)
  (orderedEdgeLinks3 currentTriangulation)

embeddingOrderingEven : Embeddings.FaceEmbedding 3 simplex_count → Bool
embeddingOrderingEven currentEmbedding = not
  (Components.oddPermutationImages
    (map fin_to_nat
      (Embeddings.ordered_simplex_vertices currentEmbedding)))

embeddingOrientationMatchesLookup :
  Embeddings.FaceEmbedding 3 simplex_count →
  Maybe Components.Orientation → Bool
embeddingOrientationMatchesLookup currentEmbedding nothing = false
embeddingOrientationMatchesLookup currentEmbedding
  (just Components.positive) = embeddingOrderingEven currentEmbedding
embeddingOrientationMatchesLookup currentEmbedding
  (just Components.negative) = not (embeddingOrderingEven currentEmbedding)

orderedEmbeddingMatchesOrientation :
  List (SimplexOrientationLabel3 simplex_count) →
  Embeddings.FaceEmbedding 3 simplex_count → Bool
orderedEmbeddingMatchesOrientation orientationLabels currentEmbedding =
  embeddingOrientationMatchesLookup currentEmbedding
    (orientationForSimplex
      (face_simplex (Embeddings.embedded_local_face currentEmbedding))
      orientationLabels)

allOrderedMappingsMatchSimplexOrientations :
  Triangulation 3 simplex_count → Bool
allOrderedMappingsMatchSimplexOrientations currentTriangulation = all
  (λ currentClass → all
    (orderedEmbeddingMatchesOrientation
      (simplexOrientationLabels3 currentTriangulation))
    (ordered_edge_embeddings currentClass))
  (orderedEdgeLinks3 currentTriangulation)

genericClassForFace : LocalFace 3 simplex_count →
  List (FaceLinks.FaceLinkClass 3 simplex_count) →
  Maybe (FaceLinks.FaceLinkClass 3 simplex_count)
genericClassForFace requestedFace [] = nothing
genericClassForFace requestedFace (currentClass ∷ remainingClasses)
  with Embeddings.findEmbeddingForFace requestedFace
    (FaceLinks.face_link_embeddings currentClass)
... | just matchingEmbedding = just currentClass
... | nothing = genericClassForFace requestedFace remainingClasses

allEmbeddingFacesInGenericClass :
  FaceLinks.FaceLinkClass 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Bool
allEmbeddingFacesInGenericClass genericClass exactEmbeddings = all
  (λ exactEmbedding →
    FaceLinks.faceReachedByLinkEmbeddings
      (Embeddings.embedded_local_face exactEmbedding)
      (FaceLinks.face_link_embeddings genericClass))
  exactEmbeddings

orderedClassMatchesGenericAfterLookup : OrderedEdgeLink3 simplex_count →
  Maybe (FaceLinks.FaceLinkClass 3 simplex_count) → Bool
orderedClassMatchesGenericAfterLookup currentClass nothing = false
orderedClassMatchesGenericAfterLookup currentClass (just genericClass) =
  nat_equal
    (length (ordered_edge_embeddings currentClass))
    (length (FaceLinks.face_link_embeddings genericClass)) and
  allEmbeddingFacesInGenericClass genericClass
    (ordered_edge_embeddings currentClass) and
  bool_equal
    (ordered_edge_bad_identification currentClass)
    (FaceLinks.face_has_bad_identification genericClass)

orderedClassMatchesGeneric :
  List (FaceLinks.FaceLinkClass 3 simplex_count) →
  OrderedEdgeLink3 simplex_count → Bool
orderedClassMatchesGeneric genericClasses currentClass
  with firstEmbeddingOf (ordered_edge_embeddings currentClass)
... | nothing = false
... | just firstEmbedding = orderedClassMatchesGenericAfterLookup currentClass
  (genericClassForFace
    (Embeddings.embedded_local_face firstEmbedding) genericClasses)

allOrderedEdgeClassesMatchGeneric : Triangulation 3 simplex_count → Bool
allOrderedEdgeClassesMatchGeneric currentTriangulation = all
  (orderedClassMatchesGeneric
    (FaceLinks.faceLinkClasses currentTriangulation 1))
  (orderedEdgeLinks3 currentTriangulation)

orderedEdgeEmbeddingSimplexNumbers : OrderedEdgeLink3 simplex_count → List Nat
orderedEdgeEmbeddingSimplexNumbers currentClass = map
  (λ currentEmbedding → fin_to_nat
    (face_simplex (Embeddings.embedded_local_face currentEmbedding)))
  (ordered_edge_embeddings currentClass)

orderedEdgeEmbeddingTables : OrderedEdgeLink3 simplex_count →
  List (List Nat)
orderedEdgeEmbeddingTables currentClass = map Embeddings.embeddingVertexTable
  (ordered_edge_embeddings currentClass)

boundaryFacetNumber : Maybe (Facet 3 simplex_count) → Maybe Nat
boundaryFacetNumber nothing = nothing
boundaryFacetNumber (just currentFacet) =
  just (fin_to_nat (opposite_vertex currentFacet))

orderedEdgeFirstBoundaryNumbers : Triangulation 3 simplex_count →
  List (Maybe Nat)
orderedEdgeFirstBoundaryNumbers currentTriangulation = map
  (λ currentClass → boundaryFacetNumber
    (ordered_edge_first_boundary currentClass))
  (orderedEdgeLinks3 currentTriangulation)

orderedEdgeLastBoundaryNumbers : Triangulation 3 simplex_count →
  List (Maybe Nat)
orderedEdgeLastBoundaryNumbers currentTriangulation = map
  (λ currentClass → boundaryFacetNumber
    (ordered_edge_last_boundary currentClass))
  (orderedEdgeLinks3 currentTriangulation)
