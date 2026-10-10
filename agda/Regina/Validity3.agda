{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- A reasoned three-dimensional validity report matching Regina's translated
-- skeleton checks. Sources: detail/skeleton-impl.h and dim3/skeleton.cpp at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.Validity3 where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.FaceLinks
import Regina.Components as Components
import Regina.ExactEdgeLinks3 as ExactEdges
import Regina.Link3 as Link3
import Regina.TetrahedronFaces3 as TetrahedronFaces
import Regina.VertexLinkSurface3 as VertexLinks
import Regina.BoundaryLabels3 as BoundaryLabels

data InvalidityReason3 : Set where
  inconsistent_facet_pairings : InvalidityReason3
  reversed_edge_identification : InvalidityReason3
  invalid_real_boundary_vertex_link : InvalidityReason3

reasonEqual : InvalidityReason3 → InvalidityReason3 → Bool
reasonEqual inconsistent_facet_pairings inconsistent_facet_pairings = true
reasonEqual reversed_edge_identification reversed_edge_identification = true
reasonEqual invalid_real_boundary_vertex_link
  invalid_real_boundary_vertex_link = true
reasonEqual firstReason secondReason = false

reasonMember : InvalidityReason3 → List InvalidityReason3 → Bool
reasonMember requestedReason [] = false
reasonMember requestedReason (currentReason ∷ remainingReasons) =
  reasonEqual requestedReason currentReason or
  reasonMember requestedReason remainingReasons

reasonWhenFalse : Bool → InvalidityReason3 → List InvalidityReason3
reasonWhenFalse true reason = []
reasonWhenFalse false reason = reason ∷ []

facetPairingsValid : {simplex_count : Nat} →
  Triangulation 3 simplex_count → Bool
facetPairingsValid currentTriangulation =
  pairings_pass (raw_state currentTriangulation)

edgeIdentificationsValid : {simplex_count : Nat} →
  Triangulation 3 simplex_count → Bool
edgeIdentificationsValid currentTriangulation =
  not (hasBadIdentification currentTriangulation 1)

realBoundaryVertexLinksValid : {simplex_count : Nat} →
  Triangulation 3 simplex_count → Bool
realBoundaryVertexLinksValid currentTriangulation =
  not (Link3.threeDimensionalHasInvalidVertexLink currentTriangulation)

threeDimensionalInvalidityReasons : {simplex_count : Nat} →
  Triangulation 3 simplex_count → List InvalidityReason3
threeDimensionalInvalidityReasons currentTriangulation =
  reasonWhenFalse
    (facetPairingsValid currentTriangulation)
    inconsistent_facet_pairings ++
  reasonWhenFalse
    (edgeIdentificationsValid currentTriangulation)
    reversed_edge_identification ++
  reasonWhenFalse
    (realBoundaryVertexLinksValid currentTriangulation)
    invalid_real_boundary_vertex_link

threeDimensionalValidityValue : {simplex_count : Nat} →
  Triangulation 3 simplex_count → Bool
threeDimensionalValidityValue currentTriangulation =
  facetPairingsValid currentTriangulation and
  edgeIdentificationsValid currentTriangulation and
  realBoundaryVertexLinksValid currentTriangulation

exactEdgeLinkAnalysisComplete : {simplex_count : Nat} →
  Triangulation 3 simplex_count → Bool
exactEdgeLinkAnalysisComplete currentTriangulation =
  ExactEdges.allOrderedEdgeWalksComplete currentTriangulation and
  ExactEdges.orderedEdgeOccurrencesComplete currentTriangulation and
  ExactEdges.allOrderedEdgeStructuresValid currentTriangulation and
  ExactEdges.allOrderedMappingsMatchSimplexOrientations currentTriangulation and
  ExactEdges.allOrderedEdgeClassesMatchGeneric currentTriangulation

tetrahedronFaceAnalysisComplete : {simplex_count : Nat} →
  Triangulation 3 simplex_count → Bool
tetrahedronFaceAnalysisComplete currentTriangulation =
  TetrahedronFaces.allTetrahedronFaceReferencesResolved
    currentTriangulation and
  TetrahedronFaces.allTetrahedronMappingsValid
    currentTriangulation and
  TetrahedronFaces.tetrahedronIncidencesMatchFaceDegrees
    currentTriangulation and
  TetrahedronFaces.allFacetMappingsCompatible
    currentTriangulation

explicitVertexLinkComplete : {simplex_count : Nat} →
  VertexLinks.ExplicitVertexLink simplex_count → Bool
explicitVertexLinkComplete currentLink =
  VertexLinks.explicitLinkCornersResolved currentLink and
  VertexLinks.explicitLinkPairingsResolved currentLink and
  VertexLinks.explicitLinkPairingsReciprocal currentLink

explicitVertexLinkAnalysisComplete : {simplex_count : Nat} →
  Triangulation 3 simplex_count → Bool
explicitVertexLinkAnalysisComplete currentTriangulation = all
  explicitVertexLinkComplete
  (VertexLinks.explicitVertexLinks currentTriangulation)

realBoundaryOrientationAnalysisComplete : {simplex_count : Nat} →
  Triangulation 3 simplex_count → Bool
realBoundaryOrientationAnalysisComplete currentTriangulation = all
  BoundaryLabels.orientation_assignment_complete
  (BoundaryLabels.realBoundaryOrientationAssignments currentTriangulation)

record ThreeDimensionalValidityReport : Set where
  constructor three_dimensional_validity_report
  field
    report_facet_pairings_valid : Bool
    report_edge_identifications_valid : Bool
    report_real_boundary_vertex_links_valid : Bool
    report_validity_value : Bool
    report_triangulation_orientable : Bool
    report_triangulation_ideal : Bool
    report_triangulation_standard : Bool
    report_exact_edge_link_order_complete : Bool
    report_tetrahedron_face_mappings_complete : Bool
    report_explicit_vertex_links_complete : Bool
    report_real_boundary_orientations_complete : Bool
    report_invalidity_reasons : List InvalidityReason3
open ThreeDimensionalValidityReport public

threeDimensionalValidityReport : {simplex_count : Nat} →
  Triangulation 3 simplex_count → ThreeDimensionalValidityReport
threeDimensionalValidityReport currentTriangulation =
  three_dimensional_validity_report
    (facetPairingsValid currentTriangulation)
    (edgeIdentificationsValid currentTriangulation)
    (realBoundaryVertexLinksValid currentTriangulation)
    (threeDimensionalValidityValue currentTriangulation)
    (Components.triangulationOrientable currentTriangulation)
    (Link3.threeDimensionalIsIdeal currentTriangulation)
    (Link3.threeDimensionalIsStandard currentTriangulation)
    (exactEdgeLinkAnalysisComplete currentTriangulation)
    (tetrahedronFaceAnalysisComplete currentTriangulation)
    (explicitVertexLinkAnalysisComplete currentTriangulation)
    (realBoundaryOrientationAnalysisComplete currentTriangulation)
    (threeDimensionalInvalidityReasons currentTriangulation)
