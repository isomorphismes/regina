{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- Explicit two-dimensional vertex links for three-dimensional triangulations.
-- Derived from engine/triangulation/dim3/vertex3.cpp at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.VertexLinks3 where

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

selectedVertexFromEmbedding :
  Embeddings.FaceEmbedding 3 simplex_count → Maybe (Fin 4)
selectedVertexFromEmbedding currentEmbedding =
  find
    (λ localVertex → lookup_vector
      (face_vertices (Embeddings.embedded_local_face currentEmbedding))
      localVertex)
    (all_fin 4)

verticesDifferentFrom : Fin 4 → Fin 4 → Bool
verticesDifferentFrom firstVertex secondVertex =
  not (fin_equal firstVertex secondVertex)

complementVertices :
  Embeddings.FaceEmbedding 3 simplex_count → List (Fin 4)
complementVertices currentEmbedding
  with selectedVertexFromEmbedding currentEmbedding
... | nothing = []
... | just selectedVertex = filterElements
  (λ localVertex → verticesDifferentFrom localVertex selectedVertex)
  (all_fin 4)

verticesDifferentFromBoth : Fin 4 → Fin 4 → Fin 4 → Bool
verticesDifferentFromBoth firstExcluded secondExcluded candidateVertex =
  not
    (fin_equal candidateVertex firstExcluded or
     fin_equal candidateVertex secondExcluded)

sideEndpointVertices : Fin 4 → Fin 4 → List (Fin 4)
sideEndpointVertices selectedVertex exitFacet = filterElements
  (verticesDifferentFromBoth selectedVertex exitFacet) (all_fin 4)

edgeMask : Fin 4 → Fin 4 → Vector Bool 4
edgeMask firstVertex secondVertex = tabulate_vector 4
  (λ localVertex →
    fin_equal localVertex firstVertex or fin_equal localVertex secondVertex)

localEdgeFace : Fin simplex_count → Fin 4 → Fin 4 →
  LocalFace 3 simplex_count
localEdgeFace simplexIndex firstVertex secondVertex =
  local_face simplexIndex (edgeMask firstVertex secondVertex)

edgeClassForCorner : List (FaceLinkClass 3 simplex_count) →
  Embeddings.FaceEmbedding 3 simplex_count → Fin 4 → Maybe Nat
edgeClassForCorner edgeClasses currentEmbedding otherVertex
  with selectedVertexFromEmbedding currentEmbedding
... | nothing = nothing
... | just selectedVertex = Link3.findFaceLinkClassIndex
  (localEdgeFace
    (face_simplex (Embeddings.embedded_local_face currentEmbedding))
    selectedVertex otherVertex)
  edgeClasses

edgeClassesForVertices : List (FaceLinkClass 3 simplex_count) →
  Embeddings.FaceEmbedding 3 simplex_count → List (Fin 4) →
  List (Maybe Nat)
edgeClassesForVertices edgeClasses currentEmbedding localVertices =
  map (edgeClassForCorner edgeClasses currentEmbedding) localVertices

record VertexLinkTriangle (simplex_count : Nat) : Set where
  constructor vertex_link_triangle
  field
    link_triangle_number : Nat
    link_triangle_embedding : Embeddings.FaceEmbedding 3 simplex_count
    link_triangle_original_edge_classes : List (Maybe Nat)
open VertexLinkTriangle public

buildLinkTrianglesFrom : List (FaceLinkClass 3 simplex_count) → Nat →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (VertexLinkTriangle simplex_count)
buildLinkTrianglesFrom edgeClasses nextTriangleNumber [] = []
buildLinkTrianglesFrom edgeClasses nextTriangleNumber
  (currentEmbedding ∷ remainingEmbeddings) =
  vertex_link_triangle nextTriangleNumber currentEmbedding
    (edgeClassesForVertices edgeClasses currentEmbedding
      (complementVertices currentEmbedding)) ∷
  buildLinkTrianglesFrom edgeClasses (suc nextTriangleNumber)
    remainingEmbeddings

buildLinkTriangles : List (FaceLinkClass 3 simplex_count) →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (VertexLinkTriangle simplex_count)
buildLinkTriangles edgeClasses embeddings =
  buildLinkTrianglesFrom edgeClasses zero embeddings

findEmbeddingIndexFrom : Nat → LocalFace 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Maybe Nat
findEmbeddingIndexFrom currentIndex targetFace [] = nothing
findEmbeddingIndexFrom currentIndex targetFace
  (currentEmbedding ∷ remainingEmbeddings)
  with local_face_equal targetFace
    (Embeddings.embedded_local_face currentEmbedding)
... | true = just currentIndex
... | false = findEmbeddingIndexFrom (suc currentIndex)
  targetFace remainingEmbeddings

findEmbeddingIndex : LocalFace 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Maybe Nat
findEmbeddingIndex targetFace embeddings =
  findEmbeddingIndexFrom zero targetFace embeddings

singletonVertexMask : Fin 4 → Vector Bool 4
singletonVertexMask selectedVertex = tabulate_vector 4
  (λ localVertex → fin_equal localVertex selectedVertex)

localVertexFace : Fin simplex_count → Fin 4 → LocalFace 3 simplex_count
localVertexFace simplexIndex localVertex =
  local_face simplexIndex (singletonVertexMask localVertex)

record LinkSideAddress : Set where
  constructor link_side_address
  field
    addressed_triangle_number : Nat
    addressed_exit_facet_number : Nat
open LinkSideAddress public

data LinkSideDestination : Set where
  boundary_link_side : LinkSideDestination
  paired_link_side : Maybe LinkSideAddress → List Nat → LinkSideDestination

record VertexLinkSide (simplex_count : Nat) : Set where
  constructor vertex_link_side
  field
    side_source_triangle_number : Nat
    side_source_exit_facet_number : Nat
    side_endpoint_original_edge_classes : List (Maybe Nat)
    side_destination : LinkSideDestination
open VertexLinkSide public

makeSideAddress : Maybe Nat → Fin 4 → Maybe LinkSideAddress
makeSideAddress nothing targetExitFacet = nothing
makeSideAddress (just targetTriangleNumber) targetExitFacet =
  just (link_side_address targetTriangleNumber
    (fin_to_nat targetExitFacet))

transportEndpointVertices : Permutation 4 → List (Fin 4) → List Nat
transportEndpointVertices gluingPermutation endpointVertices =
  map
    (λ endpointVertex →
      fin_to_nat (image gluingPermutation endpointVertex))
    endpointVertices

pairedSideDestination :
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  Fin 4 → Fin 4 → List (Fin 4) → Gluing 3 simplex_count →
  LinkSideDestination
pairedSideDestination embeddings selectedVertex exitFacet endpointVertices
  outwardGluing = paired_link_side
  (makeSideAddress
    (findEmbeddingIndex
      (localVertexFace
        (adjacent_simplex outwardGluing)
        (image (vertex_permutation outwardGluing) selectedVertex))
      embeddings)
    (image (vertex_permutation outwardGluing) exitFacet))
  (transportEndpointVertices
    (vertex_permutation outwardGluing) endpointVertices)

linkSideDestinationAfterLookup :
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  Fin 4 → Fin 4 → List (Fin 4) → Maybe (Gluing 3 simplex_count) →
  LinkSideDestination
linkSideDestinationAfterLookup embeddings selectedVertex exitFacet
  endpointVertices nothing = boundary_link_side
linkSideDestinationAfterLookup embeddings selectedVertex exitFacet
  endpointVertices (just outwardGluing) =
  pairedSideDestination embeddings selectedVertex exitFacet endpointVertices
    outwardGluing

buildLinkSide : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Nat →
  Embeddings.FaceEmbedding 3 simplex_count → Fin 4 → Fin 4 →
  VertexLinkSide simplex_count
buildLinkSide currentTriangulation edgeClasses embeddings triangleNumber
  currentEmbedding selectedVertex exitFacet = vertex_link_side
  triangleNumber
  (fin_to_nat exitFacet)
  (edgeClassesForVertices edgeClasses currentEmbedding endpointVertices)
  (linkSideDestinationAfterLookup embeddings selectedVertex exitFacet
    endpointVertices
    (adjacency (raw_state currentTriangulation)
      (facet
        (face_simplex (Embeddings.embedded_local_face currentEmbedding))
        exitFacet)))
  where
  endpointVertices : List (Fin 4)
  endpointVertices = sideEndpointVertices selectedVertex exitFacet

buildLinkSidesForFacets : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Nat →
  Embeddings.FaceEmbedding 3 simplex_count → Fin 4 → List (Fin 4) →
  List (VertexLinkSide simplex_count)
buildLinkSidesForFacets currentTriangulation edgeClasses embeddings
  triangleNumber currentEmbedding selectedVertex [] = []
buildLinkSidesForFacets currentTriangulation edgeClasses embeddings
  triangleNumber currentEmbedding selectedVertex
  (exitFacet ∷ remainingFacets)
  with fin_equal exitFacet selectedVertex
... | true = buildLinkSidesForFacets currentTriangulation edgeClasses
  embeddings triangleNumber currentEmbedding selectedVertex remainingFacets
... | false = buildLinkSide currentTriangulation edgeClasses embeddings
  triangleNumber currentEmbedding selectedVertex exitFacet ∷
  buildLinkSidesForFacets currentTriangulation edgeClasses embeddings
    triangleNumber currentEmbedding selectedVertex remainingFacets

buildLinkSidesForEmbedding : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Nat →
  Embeddings.FaceEmbedding 3 simplex_count →
  List (VertexLinkSide simplex_count)
buildLinkSidesForEmbedding currentTriangulation edgeClasses embeddings
  triangleNumber currentEmbedding
  with selectedVertexFromEmbedding currentEmbedding
... | nothing = []
... | just selectedVertex = buildLinkSidesForFacets
  currentTriangulation edgeClasses embeddings triangleNumber currentEmbedding
  selectedVertex (all_fin 4)

buildLinkSidesFrom : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) →
  List (Embeddings.FaceEmbedding 3 simplex_count) → Nat →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (VertexLinkSide simplex_count)
buildLinkSidesFrom currentTriangulation edgeClasses allEmbeddings
  nextTriangleNumber [] = []
buildLinkSidesFrom currentTriangulation edgeClasses allEmbeddings
  nextTriangleNumber (currentEmbedding ∷ remainingEmbeddings) =
  buildLinkSidesForEmbedding currentTriangulation edgeClasses allEmbeddings
    nextTriangleNumber currentEmbedding ++
  buildLinkSidesFrom currentTriangulation edgeClasses allEmbeddings
    (suc nextTriangleNumber) remainingEmbeddings

buildLinkSides : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (VertexLinkSide simplex_count)
buildLinkSides currentTriangulation edgeClasses embeddings =
  buildLinkSidesFrom currentTriangulation edgeClasses embeddings zero embeddings

record LinkCornerAddress : Set where
  constructor link_corner_address
  field
    addressed_corner_triangle_number : Nat
    addressed_corner_vertex_number : Nat
open LinkCornerAddress public

record VertexLinkCorner (simplex_count : Nat) : Set where
  constructor vertex_link_corner
  field
    corner_triangle_number : Nat
    corner_embedding : Embeddings.FaceEmbedding 3 simplex_count
    corner_other_vertex : Fin 4
    corner_original_edge_class : Maybe Nat
open VertexLinkCorner public

cornerAddress : VertexLinkCorner simplex_count → LinkCornerAddress
cornerAddress currentCorner = link_corner_address
  (corner_triangle_number currentCorner)
  (fin_to_nat (corner_other_vertex currentCorner))

cornerAddressEqual : LinkCornerAddress → LinkCornerAddress → Bool
cornerAddressEqual firstAddress secondAddress =
  nat_equal
    (addressed_corner_triangle_number firstAddress)
    (addressed_corner_triangle_number secondAddress) and
  nat_equal
    (addressed_corner_vertex_number firstAddress)
    (addressed_corner_vertex_number secondAddress)

cornerEqual : VertexLinkCorner simplex_count →
  VertexLinkCorner simplex_count → Bool
cornerEqual firstCorner secondCorner =
  cornerAddressEqual (cornerAddress firstCorner) (cornerAddress secondCorner)

buildCornersForVertices : List (FaceLinkClass 3 simplex_count) → Nat →
  Embeddings.FaceEmbedding 3 simplex_count → List (Fin 4) →
  List (VertexLinkCorner simplex_count)
buildCornersForVertices edgeClasses triangleNumber currentEmbedding [] = []
buildCornersForVertices edgeClasses triangleNumber currentEmbedding
  (otherVertex ∷ remainingVertices) =
  vertex_link_corner triangleNumber currentEmbedding otherVertex
    (edgeClassForCorner edgeClasses currentEmbedding otherVertex) ∷
  buildCornersForVertices edgeClasses triangleNumber currentEmbedding
    remainingVertices

buildLinkCornersFrom : List (FaceLinkClass 3 simplex_count) → Nat →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (VertexLinkCorner simplex_count)
buildLinkCornersFrom edgeClasses nextTriangleNumber [] = []
buildLinkCornersFrom edgeClasses nextTriangleNumber
  (currentEmbedding ∷ remainingEmbeddings) =
  buildCornersForVertices edgeClasses nextTriangleNumber currentEmbedding
    (complementVertices currentEmbedding) ++
  buildLinkCornersFrom edgeClasses (suc nextTriangleNumber)
    remainingEmbeddings

buildLinkCorners : List (FaceLinkClass 3 simplex_count) →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (VertexLinkCorner simplex_count)
buildLinkCorners edgeClasses embeddings =
  buildLinkCornersFrom edgeClasses zero embeddings

makeCornerTargetAddress : Maybe Nat → Fin 4 → Maybe LinkCornerAddress
makeCornerTargetAddress nothing targetOtherVertex = nothing
makeCornerTargetAddress (just targetTriangleNumber) targetOtherVertex =
  just (link_corner_address targetTriangleNumber
    (fin_to_nat targetOtherVertex))

cornerTargetAfterLookup :
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  Fin 4 → Fin 4 → Maybe (Gluing 3 simplex_count) →
  Maybe LinkCornerAddress
cornerTargetAfterLookup embeddings selectedVertex otherVertex nothing = nothing
cornerTargetAfterLookup embeddings selectedVertex otherVertex
  (just outwardGluing) = makeCornerTargetAddress
  (findEmbeddingIndex
    (localVertexFace
      (adjacent_simplex outwardGluing)
      (image (vertex_permutation outwardGluing) selectedVertex))
    embeddings)
  (image (vertex_permutation outwardGluing) otherVertex)

cornerTargetAcrossFacet : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  VertexLinkCorner simplex_count → Fin 4 → Maybe LinkCornerAddress
cornerTargetAcrossFacet currentTriangulation embeddings currentCorner exitFacet
  with selectedVertexFromEmbedding (corner_embedding currentCorner)
... | nothing = nothing
... | just selectedVertex
  with fin_equal exitFacet selectedVertex or
       fin_equal exitFacet (corner_other_vertex currentCorner)
... | true = nothing
... | false = cornerTargetAfterLookup embeddings selectedVertex
  (corner_other_vertex currentCorner)
  (adjacency (raw_state currentTriangulation)
    (facet
      (face_simplex
        (Embeddings.embedded_local_face (corner_embedding currentCorner)))
      exitFacet))

collectCornerTargets : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  VertexLinkCorner simplex_count → List (Fin 4) →
  List LinkCornerAddress
collectCornerTargets currentTriangulation embeddings currentCorner [] = []
collectCornerTargets currentTriangulation embeddings currentCorner
  (exitFacet ∷ remainingFacets)
  with cornerTargetAcrossFacet currentTriangulation embeddings currentCorner
    exitFacet
... | nothing = collectCornerTargets currentTriangulation embeddings
  currentCorner remainingFacets
... | just targetAddress = targetAddress ∷
  collectCornerTargets currentTriangulation embeddings currentCorner
    remainingFacets

cornerTargets : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  VertexLinkCorner simplex_count → List LinkCornerAddress
cornerTargets currentTriangulation embeddings currentCorner =
  collectCornerTargets currentTriangulation embeddings currentCorner
    (all_fin 4)

cornerAddressMember : LinkCornerAddress → List LinkCornerAddress → Bool
cornerAddressMember targetAddress [] = false
cornerAddressMember targetAddress (currentAddress ∷ remainingAddresses) =
  cornerAddressEqual targetAddress currentAddress or
  cornerAddressMember targetAddress remainingAddresses

directlyConnectedCorners : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  VertexLinkCorner simplex_count → VertexLinkCorner simplex_count → Bool
directlyConnectedCorners currentTriangulation embeddings firstCorner secondCorner =
  cornerEqual firstCorner secondCorner or
  cornerAddressMember (cornerAddress secondCorner)
    (cornerTargets currentTriangulation embeddings firstCorner)

expandCornerReachableOnce : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (VertexLinkCorner simplex_count) →
  List (VertexLinkCorner simplex_count) →
  List (VertexLinkCorner simplex_count)
expandCornerReachableOnce currentTriangulation embeddings cornerUniverse
  reachedCorners = filterElements
  (λ candidateCorner → any
    (λ knownCorner → directlyConnectedCorners currentTriangulation embeddings
      knownCorner candidateCorner)
    reachedCorners)
  cornerUniverse

expandCornerReachable : Nat → Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (VertexLinkCorner simplex_count) →
  List (VertexLinkCorner simplex_count) →
  List (VertexLinkCorner simplex_count)
expandCornerReachable zero currentTriangulation embeddings cornerUniverse
  reachedCorners = reachedCorners
expandCornerReachable (suc fuel) currentTriangulation embeddings cornerUniverse
  reachedCorners = expandCornerReachable fuel currentTriangulation embeddings
  cornerUniverse
  (expandCornerReachableOnce currentTriangulation embeddings cornerUniverse
    reachedCorners)

cornerClassFromSeed : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (VertexLinkCorner simplex_count) → VertexLinkCorner simplex_count →
  List (VertexLinkCorner simplex_count)
cornerClassFromSeed currentTriangulation embeddings cornerUniverse seedCorner =
  expandCornerReachable (length cornerUniverse) currentTriangulation embeddings
    cornerUniverse (seedCorner ∷ [])

cornerMember : VertexLinkCorner simplex_count →
  List (VertexLinkCorner simplex_count) → Bool
cornerMember targetCorner [] = false
cornerMember targetCorner (currentCorner ∷ remainingCorners) =
  cornerEqual targetCorner currentCorner or
  cornerMember targetCorner remainingCorners

removeCorners : List (VertexLinkCorner simplex_count) →
  List (VertexLinkCorner simplex_count) →
  List (VertexLinkCorner simplex_count)
removeCorners removedCorners = filterElements
  (λ candidateCorner → not (cornerMember candidateCorner removedCorners))

partitionCornerClasses : Nat → Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (VertexLinkCorner simplex_count) →
  List (VertexLinkCorner simplex_count) →
  List (List (VertexLinkCorner simplex_count))
partitionCornerClasses zero currentTriangulation embeddings cornerUniverse
  remainingCorners = []
partitionCornerClasses (suc fuel) currentTriangulation embeddings cornerUniverse
  [] = []
partitionCornerClasses (suc fuel) currentTriangulation embeddings cornerUniverse
  (seedCorner ∷ remainingCorners)
  with cornerClassFromSeed currentTriangulation embeddings cornerUniverse
    seedCorner
... | discoveredClass = discoveredClass ∷
  partitionCornerClasses fuel currentTriangulation embeddings cornerUniverse
    (removeCorners discoveredClass remainingCorners)

linkCornerClasses : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (List (VertexLinkCorner simplex_count))
linkCornerClasses currentTriangulation edgeClasses embeddings
  with buildLinkCorners edgeClasses embeddings
... | cornerUniverse = partitionCornerClasses (length cornerUniverse)
  currentTriangulation embeddings cornerUniverse cornerUniverse

record ExplicitVertexLink (simplex_count : Nat) : Set where
  constructor explicit_vertex_link
  field
    original_vertex_class_number : Nat
    original_vertex_class_embeddings :
      List (Embeddings.FaceEmbedding 3 simplex_count)
    link_triangles : List (VertexLinkTriangle simplex_count)
    link_sides : List (VertexLinkSide simplex_count)
    link_corner_classes : List (List (VertexLinkCorner simplex_count))
    explicit_link_has_bad_identification : Bool
    explicit_link_is_orientable : Bool
open ExplicitVertexLink public

buildExplicitVertexLinkWithEmbeddings : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) → Nat →
  FaceLinkClass 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  ExplicitVertexLink simplex_count
buildExplicitVertexLinkWithEmbeddings currentTriangulation edgeClasses
  vertexClassNumber originalVertexClass embeddings = explicit_vertex_link
  vertexClassNumber
  embeddings
  (buildLinkTriangles edgeClasses embeddings)
  (buildLinkSides currentTriangulation edgeClasses embeddings)
  (linkCornerClasses currentTriangulation edgeClasses embeddings)
  (face_has_bad_identification originalVertexClass)
  (face_link_is_orientable originalVertexClass)

buildExplicitVertexLink : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) → Nat →
  FaceLinkClass 3 simplex_count → ExplicitVertexLink simplex_count
buildExplicitVertexLink currentTriangulation edgeClasses vertexClassNumber
  originalVertexClass = buildExplicitVertexLinkWithEmbeddings
  currentTriangulation edgeClasses vertexClassNumber originalVertexClass
  (face_link_embeddings originalVertexClass)

buildExplicitVertexLinksFrom : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) → Nat →
  List (FaceLinkClass 3 simplex_count) →
  List (ExplicitVertexLink simplex_count)
buildExplicitVertexLinksFrom currentTriangulation edgeClasses
  nextVertexClassNumber [] = []
buildExplicitVertexLinksFrom currentTriangulation edgeClasses
  nextVertexClassNumber (currentVertexClass ∷ remainingVertexClasses) =
  buildExplicitVertexLink currentTriangulation edgeClasses
    nextVertexClassNumber currentVertexClass ∷
  buildExplicitVertexLinksFrom currentTriangulation edgeClasses
    (suc nextVertexClassNumber) remainingVertexClasses

explicitVertexLinks : Triangulation 3 simplex_count →
  List (ExplicitVertexLink simplex_count)
explicitVertexLinks currentTriangulation = buildExplicitVertexLinksFrom
  currentTriangulation
  (faceLinkClasses currentTriangulation 1)
  zero
  (faceLinkClasses currentTriangulation 0)

sideIsBoundary : VertexLinkSide simplex_count → Bool
sideIsBoundary currentSide
  with side_destination currentSide
... | boundary_link_side = true
... | paired_link_side targetAddress transportedEndpoints = false

sideIsPaired : VertexLinkSide simplex_count → Bool
sideIsPaired currentSide
  with side_destination currentSide
... | boundary_link_side = false
... | paired_link_side targetAddress transportedEndpoints = true

sideIsResolved : VertexLinkSide simplex_count → Bool
sideIsResolved currentSide
  with side_destination currentSide
... | boundary_link_side = true
... | paired_link_side nothing transportedEndpoints = false
... | paired_link_side (just targetAddress) transportedEndpoints = true

halfNatural : Nat → Nat
halfNatural zero = zero
halfNatural (suc zero) = zero
halfNatural (suc (suc remaining)) = suc (halfNatural remaining)

explicitLinkTriangleCount : ExplicitVertexLink simplex_count → Nat
explicitLinkTriangleCount currentLink = length (link_triangles currentLink)

explicitLinkVertexCount : ExplicitVertexLink simplex_count → Nat
explicitLinkVertexCount currentLink = length (link_corner_classes currentLink)

explicitLinkBoundaryEdgeCount : ExplicitVertexLink simplex_count → Nat
explicitLinkBoundaryEdgeCount currentLink = count_matching sideIsBoundary
  (link_sides currentLink)

explicitLinkPairedSideCount : ExplicitVertexLink simplex_count → Nat
explicitLinkPairedSideCount currentLink = count_matching sideIsPaired
  (link_sides currentLink)

explicitLinkEdgeCount : ExplicitVertexLink simplex_count → Nat
explicitLinkEdgeCount currentLink =
  explicitLinkBoundaryEdgeCount currentLink +
  halfNatural (explicitLinkPairedSideCount currentLink)

explicitLinkEulerCharacteristic : ExplicitVertexLink simplex_count →
  Link3.SignedInteger
explicitLinkEulerCharacteristic currentLink = Link3.naturalDifference
  (explicitLinkVertexCount currentLink + explicitLinkTriangleCount currentLink)
  (explicitLinkEdgeCount currentLink)

linkSideAddressEqual : LinkSideAddress → LinkSideAddress → Bool
linkSideAddressEqual firstAddress secondAddress =
  nat_equal
    (addressed_triangle_number firstAddress)
    (addressed_triangle_number secondAddress) and
  nat_equal
    (addressed_exit_facet_number firstAddress)
    (addressed_exit_facet_number secondAddress)

sideSourceAddress : VertexLinkSide simplex_count → LinkSideAddress
sideSourceAddress currentSide = link_side_address
  (side_source_triangle_number currentSide)
  (side_source_exit_facet_number currentSide)

findSideByAddress : LinkSideAddress → List (VertexLinkSide simplex_count) →
  Maybe (VertexLinkSide simplex_count)
findSideByAddress targetAddress [] = nothing
findSideByAddress targetAddress (currentSide ∷ remainingSides)
  with linkSideAddressEqual targetAddress (sideSourceAddress currentSide)
... | true = just currentSide
... | false = findSideByAddress targetAddress remainingSides

destinationReturnsTo : LinkSideAddress → LinkSideDestination → Bool
destinationReturnsTo sourceAddress boundary_link_side = false
destinationReturnsTo sourceAddress
  (paired_link_side nothing transportedEndpoints) = false
destinationReturnsTo sourceAddress
  (paired_link_side (just returnedAddress) transportedEndpoints) =
  linkSideAddressEqual sourceAddress returnedAddress

sidePairingIsReciprocal : List (VertexLinkSide simplex_count) →
  VertexLinkSide simplex_count → Bool
sidePairingIsReciprocal allSides currentSide
  with side_destination currentSide
... | boundary_link_side = true
... | paired_link_side nothing transportedEndpoints = false
... | paired_link_side (just targetAddress) transportedEndpoints
  with findSideByAddress targetAddress allSides
... | nothing = false
... | just targetSide = destinationReturnsTo
  (sideSourceAddress currentSide) (side_destination targetSide)

explicitLinkPairingsResolved : ExplicitVertexLink simplex_count → Bool
explicitLinkPairingsResolved currentLink = all sideIsResolved
  (link_sides currentLink)

explicitLinkPairingsReciprocal : ExplicitVertexLink simplex_count → Bool
explicitLinkPairingsReciprocal currentLink = all
  (sidePairingIsReciprocal (link_sides currentLink))
  (link_sides currentLink)
