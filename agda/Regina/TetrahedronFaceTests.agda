{-# OPTIONS --safe --without-K #-}

-- Reduction tests for dimension-three simplex face lookup and mappings.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-10.

module Regina.TetrahedronFaceTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.TetrahedronFaces3

private
  record TetrahedronLookupSummary : Set where
    constructor tetrahedron_lookup_summary
    field
      all_references_resolved : Bool
      all_active_mappings_valid : Bool
      all_incidence_counts_match : Bool
      all_facet_mappings_compatible : Bool

  observeLookup : {simplex_count : Nat} →
    Triangulation 3 simplex_count → TetrahedronLookupSummary
  observeLookup currentTriangulation = tetrahedron_lookup_summary
    (allTetrahedronFaceReferencesResolved currentTriangulation)
    (allTetrahedronMappingsValid currentTriangulation)
    (tetrahedronIncidencesMatchFaceDegrees currentTriangulation)
    (allFacetMappingsCompatible currentTriangulation)

  referenceClassNumbers :
    List (Maybe TetrahedronFaceReference3) → List (Maybe Nat)
  referenceClassNumbers = map referenceClassNumber

  mappingImages : Maybe TetrahedronFaceReference3 → Maybe (List Nat)
  mappingImages nothing = nothing
  mappingImages (just currentReference) =
    just (tetrahedronFaceMappingImages currentReference)

  activeImages : Maybe TetrahedronFaceReference3 → Maybe (List Nat)
  activeImages nothing = nothing
  activeImages (just currentReference) =
    just (tetrahedronFaceActiveImages currentReference)

ballLookupSummaryChecked :
  observeLookup (ball 3) ≡
    tetrahedron_lookup_summary true true true true
ballLookupSummaryChecked = refl

sphereLookupSummaryChecked :
  map_outcome observeLookup (sphere 3) ≡
    accepted (tetrahedron_lookup_summary true true true true)
sphereLookupSummaryChecked = refl

ballBundleLookupSummaryChecked :
  map_outcome observeLookup three_dimensional_ball_bundle ≡
    accepted (tetrahedron_lookup_summary true true true true)
ballBundleLookupSummaryChecked = refl

figureEightLookupSummaryChecked :
  map_outcome observeLookup figure_eight_knot_complement ≡
    accepted (tetrahedron_lookup_summary true true true true)
figureEightLookupSummaryChecked = refl

ballVertexClassNumberingChecked :
  referenceClassNumbers (tetrahedronVertexReferences (ball 3) 0) ≡
    (just 3 ∷ just 2 ∷ just 1 ∷ just 0 ∷ [])
ballVertexClassNumberingChecked = refl

ballEdgeClassNumberingChecked :
  referenceClassNumbers (tetrahedronEdgeReferences (ball 3) 0) ≡
    (just 5 ∷ just 4 ∷ just 3 ∷ just 2 ∷ just 1 ∷ just 0 ∷ [])
ballEdgeClassNumberingChecked = refl

ballTriangleClassNumberingChecked :
  referenceClassNumbers (tetrahedronTriangleReferences (ball 3) 0) ≡
    (just 0 ∷ just 1 ∷ just 2 ∷ just 3 ∷ [])
ballTriangleClassNumberingChecked = refl

ballTriangleMappingsMatchReginaOrdering :
  map mappingImages (tetrahedronTriangleReferences (ball 3) 0) ≡
    (just (1 ∷ 2 ∷ 3 ∷ 0 ∷ []) ∷
     just (0 ∷ 2 ∷ 3 ∷ 1 ∷ []) ∷
     just (0 ∷ 1 ∷ 3 ∷ 2 ∷ []) ∷
     just (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ∷ [])
ballTriangleMappingsMatchReginaOrdering = refl

ballEdgeActiveImagesMatchReginaNumbering :
  map activeImages (tetrahedronEdgeReferences (ball 3) 0) ≡
    (just (0 ∷ 1 ∷ []) ∷
     just (0 ∷ 2 ∷ []) ∷
     just (0 ∷ 3 ∷ []) ∷
     just (1 ∷ 2 ∷ []) ∷
     just (1 ∷ 3 ∷ []) ∷
     just (2 ∷ 3 ∷ []) ∷ [])
ballEdgeActiveImagesMatchReginaNumbering = refl

sphereIdentityGluingPreservesClassTables :
  map_outcome
    (λ currentTriangulation →
      tetrahedronClassTablesEqual currentTriangulation 0 1)
    (sphere 3) ≡ accepted true
sphereIdentityGluingPreservesClassTables = refl

invalidTetrahedronFaceInputsFailClosed :
  (tetrahedronVertexReference (ball 3) 1 0 ∷
   tetrahedronVertexReference (ball 3) 0 4 ∷
   tetrahedronEdgeReference (ball 3) 0 6 ∷
   tetrahedronTriangleReference (ball 3) 0 4 ∷ []) ≡
    (nothing ∷ nothing ∷ nothing ∷ nothing ∷ [])
invalidTetrahedronFaceInputsFailClosed = refl

tetrahedronIncidenceCountsRecoverBallDegrees :
  (tetrahedronVertexIncidenceCounts (ball 3) ∷
   tetrahedronEdgeIncidenceCounts (ball 3) ∷
   tetrahedronTriangleIncidenceCounts (ball 3) ∷ []) ≡
    ((1 ∷ 1 ∷ 1 ∷ 1 ∷ []) ∷
     (1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []) ∷
     (1 ∷ 1 ∷ 1 ∷ 1 ∷ []) ∷ [])
tetrahedronIncidenceCountsRecoverBallDegrees = refl

tetrahedronIncidenceCountsRecoverFigureEightDegrees :
  map_outcome
    (λ currentTriangulation →
      tetrahedronVertexIncidenceCounts currentTriangulation ∷
      tetrahedronEdgeIncidenceCounts currentTriangulation ∷
      tetrahedronTriangleIncidenceCounts currentTriangulation ∷ [])
    figure_eight_knot_complement ≡ accepted
      ((8 ∷ []) ∷
       (6 ∷ 6 ∷ []) ∷
       (2 ∷ 2 ∷ 2 ∷ 2 ∷ []) ∷ [])
tetrahedronIncidenceCountsRecoverFigureEightDegrees = refl
