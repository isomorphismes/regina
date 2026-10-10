{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- Canonical per-facet orientation labels for real boundary components.
-- Derived from calculateRealBoundary() in
-- engine/triangulation/detail/skeleton-impl.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.BoundaryLabels3 where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.FaceLinks
import Regina.Boundary3 as Boundary
import Regina.BoundaryClassification3 as Classification

private
  variable
    simplex_count : Nat

data BoundaryFacetOrientationStatus : Set where
  boundary_facet_positive : BoundaryFacetOrientationStatus
  boundary_facet_negative : BoundaryFacetOrientationStatus
  boundary_facet_conflicting : BoundaryFacetOrientationStatus
  boundary_facet_unreachable : BoundaryFacetOrientationStatus

statusFromReachability : Bool → Bool → BoundaryFacetOrientationStatus
statusFromReachability true false = boundary_facet_positive
statusFromReachability false true = boundary_facet_negative
statusFromReachability true true = boundary_facet_conflicting
statusFromReachability false false = boundary_facet_unreachable

record BoundaryFacetOrientationLabel : Set where
  constructor boundary_facet_orientation_label
  field
    labelled_boundary_facet_number : Nat
    labelled_boundary_facet_status : BoundaryFacetOrientationStatus
open BoundaryFacetOrientationLabel public

facetStatus : List Classification.OrientedBoundaryFacet →
  Boundary.IndexedBoundaryFacet simplex_count →
  BoundaryFacetOrientationStatus
facetStatus reachedFacetStates currentFacet = statusFromReachability
  (Classification.orientedFacetMember
    (Classification.oriented_boundary_facet
      (Boundary.boundary_facet_class_number currentFacet) true)
    reachedFacetStates)
  (Classification.orientedFacetMember
    (Classification.oriented_boundary_facet
      (Boundary.boundary_facet_class_number currentFacet) false)
    reachedFacetStates)

labelFacet : List Classification.OrientedBoundaryFacet →
  Boundary.IndexedBoundaryFacet simplex_count →
  BoundaryFacetOrientationLabel
labelFacet reachedFacetStates currentFacet =
  boundary_facet_orientation_label
    (Boundary.boundary_facet_class_number currentFacet)
    (facetStatus reachedFacetStates currentFacet)

unreachableFacetLabel : Boundary.IndexedBoundaryFacet simplex_count →
  BoundaryFacetOrientationLabel
unreachableFacetLabel currentFacet = boundary_facet_orientation_label
  (Boundary.boundary_facet_class_number currentFacet)
  boundary_facet_unreachable

statusResolved : BoundaryFacetOrientationStatus → Bool
statusResolved boundary_facet_positive = true
statusResolved boundary_facet_negative = true
statusResolved boundary_facet_conflicting = false
statusResolved boundary_facet_unreachable = false

labelResolved : BoundaryFacetOrientationLabel → Bool
labelResolved currentLabel =
  statusResolved (labelled_boundary_facet_status currentLabel)

labelPositive : BoundaryFacetOrientationLabel → Bool
labelPositive currentLabel
  with labelled_boundary_facet_status currentLabel
... | boundary_facet_positive = true
... | boundary_facet_negative = false
... | boundary_facet_conflicting = false
... | boundary_facet_unreachable = false

record RealBoundaryOrientationAssignment : Set where
  constructor real_boundary_orientation_assignment
  field
    assigned_boundary_facet_labels : List BoundaryFacetOrientationLabel
    orientation_assignment_complete : Bool
    orientation_assignment_value : Bool
open RealBoundaryOrientationAssignment public

assignmentFromReachedStates :
  List (Boundary.IndexedBoundaryFacet simplex_count) →
  List Classification.BoundaryDirectedSide →
  List Classification.OrientedBoundaryFacet →
  RealBoundaryOrientationAssignment
assignmentFromReachedStates currentComponent resolvedSides reachedFacetStates =
  real_boundary_orientation_assignment labels
    (all labelResolved labels)
    (Classification.componentOrientationValue currentComponent resolvedSides)
  where
  labels : List BoundaryFacetOrientationLabel
  labels = map (labelFacet reachedFacetStates) currentComponent

assignmentAfterResolution :
  List (Boundary.IndexedBoundaryFacet simplex_count) →
  List Classification.BoundaryDirectedSide → Bool →
  RealBoundaryOrientationAssignment
assignmentAfterResolution currentComponent resolvedSides false =
  real_boundary_orientation_assignment
    (map unreachableFacetLabel currentComponent) false false
assignmentAfterResolution currentComponent resolvedSides true =
  assignmentFromReachedStates currentComponent resolvedSides
    (Classification.reachableFacetStates currentComponent resolvedSides)

assignmentFromCandidates :
  List (Boundary.IndexedBoundaryFacet simplex_count) →
  List (Maybe Classification.BoundaryDirectedSide) →
  RealBoundaryOrientationAssignment
assignmentFromCandidates currentComponent sideCandidates =
  assignmentFromResolvedSides currentComponent sideCandidates
    (Classification.collectResolvedSides sideCandidates)
  where
  assignmentFromResolvedSides :
    List (Boundary.IndexedBoundaryFacet simplex_count) →
    List (Maybe Classification.BoundaryDirectedSide) →
    List Classification.BoundaryDirectedSide →
    RealBoundaryOrientationAssignment
  assignmentFromResolvedSides component candidates resolvedSides =
    assignmentAfterResolution component resolvedSides
      (Classification.orientationDataResolved component candidates resolvedSides)

assignRealBoundaryComponent :
  List (FaceLinkClass 3 simplex_count) →
  List (Boundary.IndexedBoundaryFacet simplex_count) →
  RealBoundaryOrientationAssignment
assignRealBoundaryComponent edgeClasses currentComponent =
  assignmentFromCandidates currentComponent
    (Classification.componentSideCandidates edgeClasses currentComponent)

realBoundaryOrientationAssignments : Triangulation 3 simplex_count →
  List RealBoundaryOrientationAssignment
realBoundaryOrientationAssignments
  {simplex_count = numberOfSimplices} currentTriangulation = map
  (assignRealBoundaryComponent edgeClasses)
  (Boundary.realBoundaryFacetComponents currentTriangulation)
  where
  edgeClasses : List (FaceLinkClass 3 numberOfSimplices)
  edgeClasses = faceLinkClasses currentTriangulation 1

assignmentFacetCount : RealBoundaryOrientationAssignment → Nat
assignmentFacetCount currentAssignment =
  length (assigned_boundary_facet_labels currentAssignment)

assignmentRootPositive : RealBoundaryOrientationAssignment → Bool
assignmentRootPositive currentAssignment
  with assigned_boundary_facet_labels currentAssignment
... | [] = false
... | rootLabel ∷ remainingLabels = labelPositive rootLabel

assignmentHasConflict : RealBoundaryOrientationAssignment → Bool
assignmentHasConflict currentAssignment = any
  (λ currentLabel → statusIsConflict
    (labelled_boundary_facet_status currentLabel))
  (assigned_boundary_facet_labels currentAssignment)
  where
  statusIsConflict : BoundaryFacetOrientationStatus → Bool
  statusIsConflict boundary_facet_conflicting = true
  statusIsConflict boundary_facet_positive = false
  statusIsConflict boundary_facet_negative = false
  statusIsConflict boundary_facet_unreachable = false
