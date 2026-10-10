{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- Dimension-three Face API properties, including Regina's exact private
-- Validity and VertexFlags bit values from engine/triangulation/face.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.FaceProperties3 where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks
import Regina.Embeddings as Embeddings
import Regina.Link3 as Link3
import Regina.DualForest as DualForest

private
  variable
    simplex_count : Nat

-- Exact numeric values of Face<dim,subdim>::Validity.
valid_face_code : Nat
valid_face_code = 0

invalid_identification_code : Nat
invalid_identification_code = 1

invalid_link_code : Nat
invalid_link_code = 2

record FaceInvalidityBits : Set where
  constructor face_invalidity_bits
  field
    invalid_identification_bit : Bool
    invalid_link_bit : Bool
open FaceInvalidityBits public

faceInvalidityCode : FaceInvalidityBits → Nat
faceInvalidityCode currentBits
  with invalid_identification_bit currentBits |
       invalid_link_bit currentBits
... | false | false = valid_face_code
... | true | false = invalid_identification_code
... | false | true = invalid_link_code
... | true | true = invalid_identification_code + invalid_link_code

faceValidityValue : FaceInvalidityBits → Bool
faceValidityValue currentBits = not
  (invalid_identification_bit currentBits or invalid_link_bit currentBits)

faceHasBadIdentification : FaceInvalidityBits → Bool
faceHasBadIdentification = invalid_identification_bit

faceHasBadLink : FaceInvalidityBits → Bool
faceHasBadLink = invalid_link_bit

-- Exact numeric values of Face<4,0>::VertexFlags are also the conventions
-- Regina uses conceptually in dimension three: ideal = 1, real boundary = 2.
ideal_vertex_flag : Nat
ideal_vertex_flag = 1

real_boundary_vertex_flag : Nat
real_boundary_vertex_flag = 2

boolWeight : Bool → Nat → Nat
boolWeight false weight = zero
boolWeight true weight = weight

vertexFlagsCode : Bool → Bool → Nat
vertexFlagsCode idealValue realBoundaryValue =
  boolWeight idealValue ideal_vertex_flag +
  boolWeight realBoundaryValue real_boundary_vertex_flag

record FaceCoreProperties3 : Set where
  constructor face_core_properties_3
  field
    core_face_dimension : Nat
    core_face_class_number : Nat
    core_face_degree : Nat
    core_link_orientable : Bool
    core_touches_real_boundary : Bool
    core_is_boundary : Bool
    core_is_internal : Bool
    core_invalidity_bits : FaceInvalidityBits
open FaceCoreProperties3 public

coreWhyInvalidCode : FaceCoreProperties3 → Nat
coreWhyInvalidCode currentProperties =
  faceInvalidityCode (core_invalidity_bits currentProperties)

coreIsValid : FaceCoreProperties3 → Bool
coreIsValid currentProperties =
  faceValidityValue (core_invalidity_bits currentProperties)

coreHasBadIdentification : FaceCoreProperties3 → Bool
coreHasBadIdentification currentProperties =
  faceHasBadIdentification (core_invalidity_bits currentProperties)

coreHasBadLink : FaceCoreProperties3 → Bool
coreHasBadLink currentProperties =
  faceHasBadLink (core_invalidity_bits currentProperties)

makeCoreProperties : Nat → Nat → Nat → Bool → Bool → Bool →
  FaceInvalidityBits → FaceCoreProperties3
makeCoreProperties faceDimension classNumber faceDegree linkOrientable
  touchesRealBoundary boundaryValue invalidityBits = face_core_properties_3
  faceDimension
  classNumber
  faceDegree
  linkOrientable
  touchesRealBoundary
  boundaryValue
  (faceValidityValue invalidityBits and not boundaryValue)
  invalidityBits

record VertexProperties3 : Set where
  constructor vertex_properties_3
  field
    vertex_core : FaceCoreProperties3
    vertex_link_closed : Bool
    vertex_is_ideal : Bool
    vertex_is_standard : Bool
    vertex_link_euler_characteristic : Link3.SignedInteger
    vertex_flags_code : Nat
open VertexProperties3 public

makeVertexProperties : FaceLinkClass 3 simplex_count →
  Link3.VertexLinkSummary → VertexProperties3
makeVertexProperties currentClass currentSummary = vertex_properties_3
  (makeCoreProperties 0
    (Link3.vertex_class_number currentSummary)
    (length (face_link_embeddings currentClass))
    (face_link_is_orientable currentClass)
    touchesRealBoundary
    boundaryValue
    invalidityBits)
  (not touchesRealBoundary)
  idealValue
  (Link3.summaryIsStandard currentSummary)
  (Link3.vertex_link_euler_characteristic currentSummary)
  (vertexFlagsCode idealValue touchesRealBoundary)
  where
  touchesRealBoundary : Bool
  touchesRealBoundary = Link3.vertex_touches_boundary currentSummary

  idealValue : Bool
  idealValue = Link3.summaryIsIdeal currentSummary

  badLink : Bool
  badLink = Link3.summaryIsInvalid currentSummary

  invalidityBits : FaceInvalidityBits
  invalidityBits = face_invalidity_bits
    (face_has_bad_identification currentClass) badLink

  boundaryValue : Bool
  boundaryValue = touchesRealBoundary or idealValue or badLink

buildVertexProperties : List (FaceLinkClass 3 simplex_count) →
  List Link3.VertexLinkSummary → List VertexProperties3
buildVertexProperties [] summaries = []
buildVertexProperties classes [] = []
buildVertexProperties (currentClass ∷ remainingClasses)
  (currentSummary ∷ remainingSummaries) =
  makeVertexProperties currentClass currentSummary ∷
  buildVertexProperties remainingClasses remainingSummaries

vertexProperties : Triangulation 3 simplex_count → List VertexProperties3
vertexProperties currentTriangulation = buildVertexProperties
  (faceLinkClasses currentTriangulation 0)
  (Link3.threeDimensionalVertexLinkSummaries currentTriangulation)

record EdgeProperties3 : Set where
  constructor edge_properties_3
  field
    edge_core : FaceCoreProperties3
    edge_link_closed : Bool
open EdgeProperties3 public

makeEdgeProperties : Triangulation 3 simplex_count → Nat →
  FaceLinkClass 3 simplex_count → EdgeProperties3
makeEdgeProperties currentTriangulation classNumber currentClass =
  edge_properties_3
    (makeCoreProperties 1 classNumber
      (length (face_link_embeddings currentClass))
      (face_link_is_orientable currentClass)
      touchesRealBoundary
      touchesRealBoundary
      (face_invalidity_bits
        (face_has_bad_identification currentClass) false))
    (not touchesRealBoundary)
  where
  touchesRealBoundary : Bool
  touchesRealBoundary = Link3.faceLinkClassTouchesBoundary
    currentTriangulation currentClass

buildEdgePropertiesFrom : Triangulation 3 simplex_count → Nat →
  List (FaceLinkClass 3 simplex_count) → List EdgeProperties3
buildEdgePropertiesFrom currentTriangulation nextClassNumber [] = []
buildEdgePropertiesFrom currentTriangulation nextClassNumber
  (currentClass ∷ remainingClasses) =
  makeEdgeProperties currentTriangulation nextClassNumber currentClass ∷
  buildEdgePropertiesFrom currentTriangulation (suc nextClassNumber)
    remainingClasses

edgeProperties : Triangulation 3 simplex_count → List EdgeProperties3
edgeProperties currentTriangulation = buildEdgePropertiesFrom
  currentTriangulation zero (faceLinkClasses currentTriangulation 1)

oppositeVertexOfTriangle : LocalFace 3 simplex_count → Maybe (Fin 4)
oppositeVertexOfTriangle currentFace = find
  (λ localVertex → not
    (lookup_vector (face_vertices currentFace) localVertex))
  (all_fin 4)

embeddingInDualForest : Triangulation 3 simplex_count →
  Embeddings.FaceEmbedding 3 simplex_count → Bool
embeddingInDualForest currentTriangulation currentEmbedding
  with oppositeVertexOfTriangle
    (Embeddings.embedded_local_face currentEmbedding)
... | nothing = false
... | just oppositeVertex = DualForest.facetInDualForest
  currentTriangulation
  (facet
    (face_simplex (Embeddings.embedded_local_face currentEmbedding))
    oppositeVertex)

triangleClassInDualForest : Triangulation 3 simplex_count →
  FaceLinkClass 3 simplex_count → Bool
triangleClassInDualForest currentTriangulation currentClass = any
  (embeddingInDualForest currentTriangulation)
  (face_link_embeddings currentClass)

record TriangleProperties3 : Set where
  constructor triangle_properties_3
  field
    triangle_core : FaceCoreProperties3
    triangle_in_maximal_forest : Bool
open TriangleProperties3 public

makeTriangleProperties : Triangulation 3 simplex_count → Nat →
  FaceLinkClass 3 simplex_count → TriangleProperties3
makeTriangleProperties currentTriangulation classNumber currentClass =
  triangle_properties_3
    (makeCoreProperties 2 classNumber
      (length (face_link_embeddings currentClass))
      (face_link_is_orientable currentClass)
      touchesRealBoundary
      touchesRealBoundary
      (face_invalidity_bits false false))
    (triangleClassInDualForest currentTriangulation currentClass)
  where
  touchesRealBoundary : Bool
  touchesRealBoundary = Link3.faceLinkClassTouchesBoundary
    currentTriangulation currentClass

buildTrianglePropertiesFrom : Triangulation 3 simplex_count → Nat →
  List (FaceLinkClass 3 simplex_count) → List TriangleProperties3
buildTrianglePropertiesFrom currentTriangulation nextClassNumber [] = []
buildTrianglePropertiesFrom currentTriangulation nextClassNumber
  (currentClass ∷ remainingClasses) =
  makeTriangleProperties currentTriangulation nextClassNumber currentClass ∷
  buildTrianglePropertiesFrom currentTriangulation (suc nextClassNumber)
    remainingClasses

triangleProperties : Triangulation 3 simplex_count → List TriangleProperties3
triangleProperties currentTriangulation = buildTrianglePropertiesFrom
  currentTriangulation zero (faceLinkClasses currentTriangulation 2)
