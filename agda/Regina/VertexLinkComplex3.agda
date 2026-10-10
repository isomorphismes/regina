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

sideEndpointVertices : Fin 4 → Fin 4 → List (Fin 4)
sideEndpointVertices selectedLocalVertex exitFacet = filterElements
  (λ localVertex → not
    (fin_equal localVertex selectedLocalVertex or
     fin_equal localVertex exitFacet))
  (all_fin 4)

singletonVertexMask : Fin 4 → Vector Bool 4
singletonVertexMask selectedLocalVertex = tabulate_vector 4
  (λ localVertex → fin_equal localVertex selectedLocalVertex)

localVertexFace : Fin simplex_count → Fin 4 → LocalFace 3 simplex_count
localVertexFace simplexIndex localVertex =
  local_face simplexIndex (singletonVertexMask localVertex)

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

record LinkCornerAddress : Set where
  constructor link_corner_address
  field
    corner_triangle_number : Nat
    corner_other_vertex_number : Nat
open LinkCornerAddress public

record LinkTriangleCorner (simplex_count : Nat) : Set where
  constructor link_triangle_corner
  field
    containing_triangle_number : Nat
    containing_occurrence : Embeddings.FaceEmbedding 3 simplex_count
    other_local_vertex : Fin 4
open LinkTriangleCorner public

cornerAddress : LinkTriangleCorner simplex_count → LinkCornerAddress
cornerAddress currentCorner = link_corner_address
  (containing_triangle_number currentCorner)
  (fin_to_nat (other_local_vertex currentCorner))

cornerAddressEqual : LinkCornerAddress → LinkCornerAddress → Bool
cornerAddressEqual firstAddress secondAddress =
  nat_equal (corner_triangle_number firstAddress)
    (corner_triangle_number secondAddress) and
  nat_equal (corner_other_vertex_number firstAddress)
    (corner_other_vertex_number secondAddress)

cornerEqual : LinkTriangleCorner simplex_count →
  LinkTriangleCorner simplex_count → Bool
cornerEqual firstCorner secondCorner =
  cornerAddressEqual (cornerAddress firstCorner) (cornerAddress secondCorner)

buildCornersForVertices : Nat →
  Embeddings.FaceEmbedding 3 simplex_count → List (Fin 4) →
  List (LinkTriangleCorner simplex_count)
buildCornersForVertices triangleNumber currentOccurrence [] = []
buildCornersForVertices triangleNumber currentOccurrence
  (otherLocalVertex ∷ remainingVertices) =
  link_triangle_corner triangleNumber currentOccurrence otherLocalVertex ∷
  buildCornersForVertices triangleNumber currentOccurrence remainingVertices

buildAllCornersFrom : Nat →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (LinkTriangleCorner simplex_count)
buildAllCornersFrom nextTriangleNumber [] = []
buildAllCornersFrom nextTriangleNumber
  (currentOccurrence ∷ remainingOccurrences) =
  buildCornersForVertices nextTriangleNumber currentOccurrence
    (otherVertices currentOccurrence) ++
  buildAllCornersFrom (suc nextTriangleNumber) remainingOccurrences

buildAllCorners : List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (LinkTriangleCorner simplex_count)
buildAllCorners triangleOccurrences = buildAllCornersFrom zero triangleOccurrences

cornerTargetAddress : Maybe Nat → Fin 4 → Maybe LinkCornerAddress
cornerTargetAddress nothing targetOtherVertex = nothing
cornerTargetAddress (just targetTriangleNumber) targetOtherVertex =
  just (link_corner_address targetTriangleNumber
    (fin_to_nat targetOtherVertex))

cornerTargetAfterLookup :
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  Fin 4 → Fin 4 → Maybe (Gluing 3 simplex_count) →
  Maybe LinkCornerAddress
cornerTargetAfterLookup triangleOccurrences selectedLocalVertex
  otherLocalVertex nothing = nothing
cornerTargetAfterLookup triangleOccurrences selectedLocalVertex
  otherLocalVertex (just outwardGluing) = cornerTargetAddress
  (findOccurrenceIndex
    (localVertexFace
      (adjacent_simplex outwardGluing)
      (image (vertex_permutation outwardGluing) selectedLocalVertex))
    triangleOccurrences)
  (image (vertex_permutation outwardGluing) otherLocalVertex)

cornerTargetAcrossFacet : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  LinkTriangleCorner simplex_count → Fin 4 → Maybe LinkCornerAddress
cornerTargetAcrossFacet currentTriangulation triangleOccurrences
  currentCorner exitFacet with selectedVertex (containing_occurrence currentCorner)
... | nothing = nothing
... | just selectedLocalVertex = cornerTargetAcrossFacetAfterSelection
  currentTriangulation triangleOccurrences currentCorner exitFacet
  selectedLocalVertex

cornerTargetAcrossFacetAfterSelection : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  LinkTriangleCorner simplex_count → Fin 4 → Fin 4 →
  Maybe LinkCornerAddress
cornerTargetAcrossFacetAfterSelection currentTriangulation
  triangleOccurrences currentCorner exitFacet selectedLocalVertex
  with fin_equal exitFacet selectedLocalVertex or
       fin_equal exitFacet (other_local_vertex currentCorner)
... | true = nothing
... | false = cornerTargetAfterLookup triangleOccurrences selectedLocalVertex
  (other_local_vertex currentCorner)
  (adjacency (raw_state currentTriangulation)
    (facet
      (face_simplex
        (Embeddings.embedded_local_face
          (containing_occurrence currentCorner)))
      exitFacet))

collectCornerTargets : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  LinkTriangleCorner simplex_count → List (Fin 4) → List LinkCornerAddress
collectCornerTargets currentTriangulation triangleOccurrences currentCorner [] = []
collectCornerTargets currentTriangulation triangleOccurrences currentCorner
  (exitFacet ∷ remainingFacets)
  with cornerTargetAcrossFacet currentTriangulation triangleOccurrences
    currentCorner exitFacet
... | nothing = collectCornerTargets currentTriangulation triangleOccurrences
  currentCorner remainingFacets
... | just targetAddress = targetAddress ∷
  collectCornerTargets currentTriangulation triangleOccurrences currentCorner
    remainingFacets

cornerTargets : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  LinkTriangleCorner simplex_count → List LinkCornerAddress
cornerTargets currentTriangulation triangleOccurrences currentCorner =
  collectCornerTargets currentTriangulation triangleOccurrences currentCorner
    (all_fin 4)

addressMember : LinkCornerAddress → List LinkCornerAddress → Bool
addressMember targetAddress [] = false
addressMember targetAddress (currentAddress ∷ remainingAddresses) =
  cornerAddressEqual targetAddress currentAddress or
  addressMember targetAddress remainingAddresses

directlyConnected : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  LinkTriangleCorner simplex_count → LinkTriangleCorner simplex_count → Bool
directlyConnected currentTriangulation triangleOccurrences
  firstCorner secondCorner = cornerEqual firstCorner secondCorner or
  addressMember (cornerAddress secondCorner)
    (cornerTargets currentTriangulation triangleOccurrences firstCorner)

expandOnce : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (LinkTriangleCorner simplex_count) →
  List (LinkTriangleCorner simplex_count) →
  List (LinkTriangleCorner simplex_count)
expandOnce currentTriangulation triangleOccurrences cornerUniverse
  reachedCorners = filterElements
  (λ candidateCorner → any
    (λ knownCorner → directlyConnected currentTriangulation
      triangleOccurrences knownCorner candidateCorner)
    reachedCorners)
  cornerUniverse

expandCorners : Nat → Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (LinkTriangleCorner simplex_count) →
  List (LinkTriangleCorner simplex_count) →
  List (LinkTriangleCorner simplex_count)
expandCorners zero currentTriangulation triangleOccurrences cornerUniverse
  reachedCorners = reachedCorners
expandCorners (suc fuel) currentTriangulation triangleOccurrences cornerUniverse
  reachedCorners = expandCorners fuel currentTriangulation triangleOccurrences
  cornerUniverse
  (expandOnce currentTriangulation triangleOccurrences cornerUniverse
    reachedCorners)

cornerClassFromSeed : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (LinkTriangleCorner simplex_count) → LinkTriangleCorner simplex_count →
  List (LinkTriangleCorner simplex_count)
cornerClassFromSeed currentTriangulation triangleOccurrences cornerUniverse
  seedCorner = expandCorners (length cornerUniverse) currentTriangulation
  triangleOccurrences cornerUniverse (seedCorner ∷ [])

cornerMember : LinkTriangleCorner simplex_count →
  List (LinkTriangleCorner simplex_count) → Bool
cornerMember targetCorner [] = false
cornerMember targetCorner (currentCorner ∷ remainingCorners) =
  cornerEqual targetCorner currentCorner or
  cornerMember targetCorner remainingCorners

removeCorners : List (LinkTriangleCorner simplex_count) →
  List (LinkTriangleCorner simplex_count) →
  List (LinkTriangleCorner simplex_count)
removeCorners removedCorners = filterElements
  (λ candidateCorner → not (cornerMember candidateCorner removedCorners))

partitionCornerClasses : Nat → Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (LinkTriangleCorner simplex_count) →
  List (LinkTriangleCorner simplex_count) →
  List (List (LinkTriangleCorner simplex_count))
partitionCornerClasses zero currentTriangulation triangleOccurrences
  cornerUniverse remainingCorners = []
partitionCornerClasses (suc fuel) currentTriangulation triangleOccurrences
  cornerUniverse [] = []
partitionCornerClasses (suc fuel) currentTriangulation triangleOccurrences
  cornerUniverse (seedCorner ∷ remainingCorners)
  with cornerClassFromSeed currentTriangulation triangleOccurrences
    cornerUniverse seedCorner
... | discoveredClass = discoveredClass ∷
  partitionCornerClasses fuel currentTriangulation triangleOccurrences
    cornerUniverse (removeCorners discoveredClass remainingCorners)

cornerClasses : Triangulation 3 simplex_count →
  List (Embeddings.FaceEmbedding 3 simplex_count) →
  List (List (LinkTriangleCorner simplex_count))
cornerClasses currentTriangulation triangleOccurrences
  with buildAllCorners triangleOccurrences
... | cornerUniverse = partitionCornerClasses (length cornerUniverse)
  currentTriangulation triangleOccurrences cornerUniverse cornerUniverse

record ExplicitVertexLink (simplex_count : Nat) : Set where
  constructor explicit_vertex_link
  field
    source_vertex_class_number : Nat
    triangle_occurrences : List (Embeddings.FaceEmbedding 3 simplex_count)
    triangle_sides : List LinkTriangleSide
    triangle_corner_classes :
      List (List (LinkTriangleCorner simplex_count))
    explicit_link_has_bad_identification : Bool
    explicit_link_is_orientable : Bool
open ExplicitVertexLink public

buildExplicitLink : Triangulation 3 simplex_count → Nat →
  FaceLinkClass 3 simplex_count → ExplicitVertexLink simplex_count
buildExplicitLink currentTriangulation vertexClassNumber currentVertexClass =
  explicit_vertex_link
    vertexClassNumber
    (face_link_embeddings currentVertexClass)
    (buildAllSides currentTriangulation
      (face_link_embeddings currentVertexClass))
    (cornerClasses currentTriangulation
      (face_link_embeddings currentVertexClass))
    (face_has_bad_identification currentVertexClass)
    (face_link_is_orientable currentVertexClass)

buildExplicitLinksFrom : Triangulation 3 simplex_count → Nat →
  List (FaceLinkClass 3 simplex_count) →
  List (ExplicitVertexLink simplex_count)
buildExplicitLinksFrom currentTriangulation nextClassNumber [] = []
buildExplicitLinksFrom currentTriangulation nextClassNumber
  (currentVertexClass ∷ remainingVertexClasses) =
  buildExplicitLink currentTriangulation nextClassNumber currentVertexClass ∷
  buildExplicitLinksFrom currentTriangulation (suc nextClassNumber)
    remainingVertexClasses

explicitVertexLinks : Triangulation 3 simplex_count →
  List (ExplicitVertexLink simplex_count)
explicitVertexLinks currentTriangulation = buildExplicitLinksFrom
  currentTriangulation zero (faceLinkClasses currentTriangulation 0)

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
explicitLinkTriangleCount currentLink = length (triangle_occurrences currentLink)

explicitLinkVertexCount : ExplicitVertexLink simplex_count → Nat
explicitLinkVertexCount currentLink = length (triangle_corner_classes currentLink)

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
