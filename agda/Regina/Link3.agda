{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- Three-dimensional vertex-link Euler characteristics and classifications.
-- Derived from engine/triangulation/dim3/skeleton.cpp at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.Link3 where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks
import Regina.Embeddings as Embeddings

private
  variable
    simplex_count : Nat

-- A small signed integer representation is sufficient for Euler
-- characteristics and avoids adding a library dependency.
data SignedInteger : Set where
  signed_zero : SignedInteger
  signed_positive : Nat → SignedInteger
  signed_negative : Nat → SignedInteger

-- signed_positive n represents +(n+1); signed_negative n represents -(n+1).
naturalDifference : Nat → Nat → SignedInteger
naturalDifference zero zero = signed_zero
naturalDifference (suc positiveRemainder) zero =
  signed_positive positiveRemainder
naturalDifference zero (suc negativeRemainder) =
  signed_negative negativeRemainder
naturalDifference (suc leftRemainder) (suc rightRemainder) =
  naturalDifference leftRemainder rightRemainder

halfNatural : Nat → Nat
halfNatural zero = zero
halfNatural (suc zero) = zero
halfNatural (suc (suc remaining)) = suc (halfNatural remaining)

naturalAsSigned : Nat → SignedInteger
naturalAsSigned zero = signed_zero
naturalAsSigned (suc magnitudeRemainder) =
  signed_positive magnitudeRemainder

negativeMagnitudeAsSigned : Nat → SignedInteger
negativeMagnitudeAsSigned zero = signed_zero
negativeMagnitudeAsSigned (suc magnitudeRemainder) =
  signed_negative magnitudeRemainder

halfSignedTowardZero : SignedInteger → SignedInteger
halfSignedTowardZero signed_zero = signed_zero
halfSignedTowardZero (signed_positive magnitudeRemainder) =
  naturalAsSigned (halfNatural (suc magnitudeRemainder))
halfSignedTowardZero (signed_negative magnitudeRemainder) =
  negativeMagnitudeAsSigned (halfNatural (suc magnitudeRemainder))

subtractThenHalf : Nat → Nat → SignedInteger
subtractThenHalf leftNatural rightNatural =
  halfSignedTowardZero (naturalDifference leftNatural rightNatural)

absoluteDifference : Nat → Nat → Nat
absoluteDifference zero rightNatural = rightNatural
absoluteDifference leftNatural zero = leftNatural
absoluteDifference (suc leftRemainder) (suc rightRemainder) =
  absoluteDifference leftRemainder rightRemainder

naturalIsEven : Nat → Bool
naturalIsEven zero = true
naturalIsEven (suc zero) = false
naturalIsEven (suc (suc remaining)) = naturalIsEven remaining

differenceIsEven : Nat → Nat → Bool
differenceIsEven leftNatural rightNatural =
  naturalIsEven (absoluteDifference leftNatural rightNatural)

signedEqualsNatural : SignedInteger → Nat → Bool
signedEqualsNatural signed_zero zero = true
signedEqualsNatural signed_zero (suc requestedRemainder) = false
signedEqualsNatural (signed_positive magnitudeRemainder) requestedNatural =
  nat_equal (suc magnitudeRemainder) requestedNatural
signedEqualsNatural (signed_negative magnitudeRemainder) requestedNatural = false

localFaceBoundaryAtFacet : Triangulation 3 simplex_count →
  LocalFace 3 simplex_count → Fin 4 → Bool
localFaceBoundaryAtFacet currentTriangulation currentFace localFacet
  with lookup_vector (face_vertices currentFace) localFacet
... | true = false
... | false with adjacency (raw_state currentTriangulation)
  (facet (face_simplex currentFace) localFacet)
... | nothing = true
... | just outwardGluing = false

localFaceTouchesBoundary : Triangulation 3 simplex_count →
  LocalFace 3 simplex_count → Bool
localFaceTouchesBoundary currentTriangulation currentFace =
  any (localFaceBoundaryAtFacet currentTriangulation currentFace) (all_fin 4)

embeddingTouchesBoundary : Triangulation 3 simplex_count →
  Embeddings.FaceEmbedding 3 simplex_count → Bool
embeddingTouchesBoundary currentTriangulation currentEmbedding =
  localFaceTouchesBoundary currentTriangulation
    (Embeddings.embedded_local_face currentEmbedding)

faceLinkClassTouchesBoundary : Triangulation 3 simplex_count →
  FaceLinkClass 3 simplex_count → Bool
faceLinkClassTouchesBoundary currentTriangulation currentClass =
  any (embeddingTouchesBoundary currentTriangulation)
    (face_link_embeddings currentClass)

faceLinkClassContains : LocalFace 3 simplex_count →
  FaceLinkClass 3 simplex_count → Bool
faceLinkClassContains targetFace currentClass =
  any
    (λ currentEmbedding → local_face_equal targetFace
      (Embeddings.embedded_local_face currentEmbedding))
    (face_link_embeddings currentClass)

findFaceLinkClassIndexFrom : Nat → LocalFace 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) → Maybe Nat
findFaceLinkClassIndexFrom currentIndex targetFace [] = nothing
findFaceLinkClassIndexFrom currentIndex targetFace
  (currentClass ∷ remainingClasses)
  with faceLinkClassContains targetFace currentClass
... | true = just currentIndex
... | false = findFaceLinkClassIndexFrom
  (suc currentIndex) targetFace remainingClasses

findFaceLinkClassIndex : LocalFace 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) → Maybe Nat
findFaceLinkClassIndex targetFace classes =
  findFaceLinkClassIndexFrom zero targetFace classes

singletonVertexMask : Fin 4 → Vector Bool 4
singletonVertexMask selectedVertex =
  tabulate_vector 4 (λ localVertex → fin_equal localVertex selectedVertex)

localVertexFace : Fin simplex_count → Fin 4 → LocalFace 3 simplex_count
localVertexFace simplexIndex localVertex =
  local_face simplexIndex (singletonVertexMask localVertex)

record LocalEdgeEndpoints (simplex_count : Nat) : Set where
  constructor local_edge_endpoints
  field
    endpoint_simplex : Fin simplex_count
    first_endpoint_vertex : Fin 4
    second_endpoint_vertex : Fin 4
open LocalEdgeEndpoints public

localEdgeEndpointsFromEmbedding :
  Embeddings.FaceEmbedding 3 simplex_count →
  Maybe (LocalEdgeEndpoints simplex_count)
localEdgeEndpointsFromEmbedding currentEmbedding
  with Embeddings.ordered_simplex_vertices currentEmbedding
... | [] = nothing
... | firstVertex ∷ [] = nothing
... | firstVertex ∷ secondVertex ∷ remainingVertices =
  just (local_edge_endpoints
    (face_simplex (Embeddings.embedded_local_face currentEmbedding))
    firstVertex secondVertex)

localEdgeEndpointsFromClass : FaceLinkClass 3 simplex_count →
  Maybe (LocalEdgeEndpoints simplex_count)
localEdgeEndpointsFromClass currentEdgeClass
  with face_link_embeddings currentEdgeClass
... | [] = nothing
... | firstEmbedding ∷ remainingEmbeddings =
  localEdgeEndpointsFromEmbedding firstEmbedding

record EdgeEndpointClasses : Set where
  constructor edge_endpoint_classes
  field
    first_endpoint_class : Nat
    second_endpoint_class : Nat
open EdgeEndpointClasses public

combineEndpointClassLookups : Maybe Nat → Maybe Nat →
  Maybe EdgeEndpointClasses
combineEndpointClassLookups nothing secondLookup = nothing
combineEndpointClassLookups (just firstClass) nothing = nothing
combineEndpointClassLookups (just firstClass) (just secondClass) =
  just (edge_endpoint_classes firstClass secondClass)

edgeEndpointClassesFromLocal :
  List (FaceLinkClass 3 simplex_count) →
  LocalEdgeEndpoints simplex_count → Maybe EdgeEndpointClasses
edgeEndpointClassesFromLocal vertexClasses localEndpoints =
  combineEndpointClassLookups
    (findFaceLinkClassIndex
      (localVertexFace
        (endpoint_simplex localEndpoints)
        (first_endpoint_vertex localEndpoints))
      vertexClasses)
    (findFaceLinkClassIndex
      (localVertexFace
        (endpoint_simplex localEndpoints)
        (second_endpoint_vertex localEndpoints))
      vertexClasses)

edgeEndpointClasses : List (FaceLinkClass 3 simplex_count) →
  FaceLinkClass 3 simplex_count → Maybe EdgeEndpointClasses
edgeEndpointClasses vertexClasses currentEdgeClass
  with localEdgeEndpointsFromClass currentEdgeClass
... | nothing = nothing
... | just localEndpoints =
  edgeEndpointClassesFromLocal vertexClasses localEndpoints

naturalWhen : Bool → Nat → Nat
naturalWhen false value = zero
naturalWhen true value = value

contributionForClassIndex : Nat → Nat → Nat → Nat
contributionForClassIndex requestedClass currentClass contribution =
  naturalWhen (nat_equal requestedClass currentClass) contribution

edgeContributionFromEndpoints : Nat → Nat → Bool →
  EdgeEndpointClasses → Nat
edgeContributionFromEndpoints requestedVertexClass contribution
  edgeIsValid endpointClasses =
  contributionForClassIndex requestedVertexClass
    (first_endpoint_class endpointClasses) contribution +
  naturalWhen edgeIsValid
    (contributionForClassIndex requestedVertexClass
      (second_endpoint_class endpointClasses) contribution)

edgeContributionToVertex : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) → Nat →
  FaceLinkClass 3 simplex_count → Nat
edgeContributionToVertex currentTriangulation vertexClasses
  requestedVertexClass currentEdgeClass
  with edgeEndpointClasses vertexClasses currentEdgeClass
... | nothing = zero
... | just endpointClasses = edgeContributionFromEndpoints
  requestedVertexClass
  (naturalWhen
    (faceLinkClassTouchesBoundary currentTriangulation currentEdgeClass)
    1 +
   naturalWhen
    (not (faceLinkClassTouchesBoundary currentTriangulation currentEdgeClass))
    2)
  (not (face_has_bad_identification currentEdgeClass))
  endpointClasses

sumEdgeContributions : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) → Nat →
  List (FaceLinkClass 3 simplex_count) → Nat
sumEdgeContributions currentTriangulation vertexClasses
  requestedVertexClass [] = zero
sumEdgeContributions currentTriangulation vertexClasses
  requestedVertexClass (currentEdgeClass ∷ remainingEdgeClasses) =
  edgeContributionToVertex currentTriangulation vertexClasses
    requestedVertexClass currentEdgeClass +
  sumEdgeContributions currentTriangulation vertexClasses
    requestedVertexClass remainingEdgeClasses

data VertexLinkKind : Set where
  real_boundary_link : VertexLinkKind
  finite_interior_link : VertexLinkKind
  ideal_link : VertexLinkKind
  invalid_boundary_link : VertexLinkKind
  indeterminate_link : VertexLinkKind

classifyInteriorLink : SignedInteger → VertexLinkKind
classifyInteriorLink linkEuler
  with signedEqualsNatural linkEuler 2
... | true = finite_interior_link
... | false = ideal_link

classifyBoundaryLink : SignedInteger → VertexLinkKind
classifyBoundaryLink linkEuler
  with signedEqualsNatural linkEuler 1
... | true = real_boundary_link
... | false = invalid_boundary_link

classifyVertexLinkAfterArithmetic : Bool → SignedInteger → Bool →
  VertexLinkKind
classifyVertexLinkAfterArithmetic false linkEuler touchesBoundary =
  indeterminate_link
classifyVertexLinkAfterArithmetic true linkEuler false =
  classifyInteriorLink linkEuler
classifyVertexLinkAfterArithmetic true linkEuler true =
  classifyBoundaryLink linkEuler

record VertexLinkSummary : Set where
  constructor vertex_link_summary
  field
    vertex_class_number : Nat
    vertex_embedding_degree : Nat
    vertex_touches_boundary : Bool
    vertex_link_orientable : Bool
    vertex_link_numerator_even : Bool
    vertex_link_euler_characteristic : SignedInteger
    vertex_link_kind : VertexLinkKind
open VertexLinkSummary public

summariseVertexLink : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) →
  List (FaceLinkClass 3 simplex_count) → Nat →
  FaceLinkClass 3 simplex_count → VertexLinkSummary
summariseVertexLink currentTriangulation vertexClasses edgeClasses
  currentVertexClassNumber currentVertexClass = vertex_link_summary
  currentVertexClassNumber
  vertexDegree
  touchesBoundary
  (face_link_is_orientable currentVertexClass)
  numeratorEven
  linkEuler
  (classifyVertexLinkAfterArithmetic numeratorEven linkEuler touchesBoundary)
  where
  vertexDegree : Nat
  vertexDegree = length (face_link_embeddings currentVertexClass)

  edgeContribution : Nat
  edgeContribution = sumEdgeContributions currentTriangulation vertexClasses
    currentVertexClassNumber edgeClasses

  numeratorEven : Bool
  numeratorEven = differenceIsEven edgeContribution vertexDegree

  linkEuler : SignedInteger
  linkEuler = subtractThenHalf edgeContribution vertexDegree

  touchesBoundary : Bool
  touchesBoundary = faceLinkClassTouchesBoundary
    currentTriangulation currentVertexClass

buildVertexLinkSummaries : Triangulation 3 simplex_count →
  List (FaceLinkClass 3 simplex_count) →
  List (FaceLinkClass 3 simplex_count) → Nat →
  List (FaceLinkClass 3 simplex_count) → List VertexLinkSummary
buildVertexLinkSummaries currentTriangulation allVertexClasses edgeClasses
  currentIndex [] = []
buildVertexLinkSummaries currentTriangulation allVertexClasses edgeClasses
  currentIndex (currentVertexClass ∷ remainingVertexClasses) =
  summariseVertexLink currentTriangulation allVertexClasses edgeClasses
    currentIndex currentVertexClass ∷
  buildVertexLinkSummaries currentTriangulation allVertexClasses edgeClasses
    (suc currentIndex) remainingVertexClasses

threeDimensionalVertexLinkSummaries : Triangulation 3 simplex_count →
  List VertexLinkSummary
threeDimensionalVertexLinkSummaries currentTriangulation =
  buildVertexLinkSummaries currentTriangulation vertexClasses edgeClasses
    zero vertexClasses
  where
  vertexClasses : List (FaceLinkClass 3 simplex_count)
  vertexClasses = faceLinkClasses currentTriangulation 0

  edgeClasses : List (FaceLinkClass 3 simplex_count)
  edgeClasses = faceLinkClasses currentTriangulation 1

summaryIsInvalid : VertexLinkSummary → Bool
summaryIsInvalid currentSummary
  with vertex_link_kind currentSummary
... | invalid_boundary_link = true
... | indeterminate_link = true
... | real_boundary_link = false
... | finite_interior_link = false
... | ideal_link = false

summaryIsIdeal : VertexLinkSummary → Bool
summaryIsIdeal currentSummary
  with vertex_link_kind currentSummary
... | ideal_link = true
... | real_boundary_link = false
... | finite_interior_link = false
... | invalid_boundary_link = false
... | indeterminate_link = false

summaryIsStandard : VertexLinkSummary → Bool
summaryIsStandard currentSummary
  with vertex_link_kind currentSummary
... | real_boundary_link = true
... | finite_interior_link = true
... | ideal_link = signedEqualsNatural
  (vertex_link_euler_characteristic currentSummary) 0
... | invalid_boundary_link = false
... | indeterminate_link = false

threeDimensionalHasInvalidVertexLink : Triangulation 3 simplex_count → Bool
threeDimensionalHasInvalidVertexLink currentTriangulation =
  any summaryIsInvalid
    (threeDimensionalVertexLinkSummaries currentTriangulation)

threeDimensionalIsIdeal : Triangulation 3 simplex_count → Bool
threeDimensionalIsIdeal currentTriangulation =
  any summaryIsIdeal
    (threeDimensionalVertexLinkSummaries currentTriangulation)

threeDimensionalIsStandard : Triangulation 3 simplex_count → Bool
threeDimensionalIsStandard currentTriangulation =
  all summaryIsStandard
    (threeDimensionalVertexLinkSummaries currentTriangulation)

threeDimensionalHasBadIdentification : Triangulation 3 simplex_count → Bool
threeDimensionalHasBadIdentification currentTriangulation =
  hasBadIdentification currentTriangulation 0 or
  hasBadIdentification currentTriangulation 1 or
  hasBadIdentification currentTriangulation 2

-- This reproduces the translated local combinatorial checks used here:
-- reciprocal facet data is already certified by Triangulation; lower-face
-- self-identifications and invalid real-boundary vertex Euler data fail.
-- It is deliberately not named isValid(), since Regina's complete contract
-- also includes machinery that this Agda development has not yet translated.
threeDimensionalLocallyValid : Triangulation 3 simplex_count → Bool
threeDimensionalLocallyValid currentTriangulation =
  not (threeDimensionalHasBadIdentification currentTriangulation) and
  not (threeDimensionalHasInvalidVertexLink currentTriangulation)
