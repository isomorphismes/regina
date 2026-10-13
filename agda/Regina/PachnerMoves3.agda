{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-13. License: ../../LICENSE.txt.
-- Immutable 1-4, 2-3, 3-2 and 4-1 Pachner transitions, including exterior
-- self-gluings, reverse creation order, and transferred facet locks.
-- Source: engine/triangulation/detail/moves-impl.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.PachnerMoves3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton using (LocalFace; local_face; tabulate_vector; filter_list; less_than)
open import Regina.PachnerRegion3
open import Agda.Builtin.Nat using (_-_)
import Regina.SubfaceIncidence3 as Lists
import Regina.DualPresentation3 as Sequence
import Regina.ChainHomology as Indexed

private
  variable
    tetrahedra : Nat

data ChamberOrigin (tetrahedra : Nat) : Set where
  retained_chamber : Fin tetrahedra → ChamberOrigin tetrahedra
  replacement_chamber : Nat → ChamberOrigin tetrahedra

origin_equal : ChamberOrigin tetrahedra → ChamberOrigin tetrahedra → Bool
origin_equal (retained_chamber firstNumber) (retained_chamber secondNumber) =
  fin_equal firstNumber secondNumber
origin_equal (replacement_chamber firstNumber) (replacement_chamber secondNumber) =
  nat_equal firstNumber secondNumber
origin_equal _ _ = false

reverse_list : {element : Set} → List element → List element
reverse_list [] = []
reverse_list (headElement ∷ tailElements) = reverse_list tailElements ++ (headElement ∷ [])

chamber_origins : {currentTriangulation : Triangulation 3 tetrahedra} →
  PachnerRegion currentTriangulation → List (ChamberOrigin tetrahedra)
chamber_origins {tetrahedra = tetrahedra} regionValue =
  map retained_chamber (filter_list (λ tetrahedronNumber → not (any
    (λ oldChamber → fin_equal tetrahedronNumber (old_tetrahedron oldChamber))
    (old_chambers regionValue))) (all_fin tetrahedra)) ++
  map (λ newNumber → replacement_chamber (fin_to_nat newNumber))
    (reverse_list (all_fin (new_chamber_count (central_face_dimension regionValue))))

find_origin : (originValues : List (ChamberOrigin tetrahedra)) → ChamberOrigin tetrahedra →
  Maybe (Fin (length originValues))
find_origin [] wantedOrigin = nothing
find_origin (headOrigin ∷ remainingOrigins) wantedOrigin with origin_equal headOrigin wantedOrigin
... | true = just fzero
... | false with find_origin remainingOrigins wantedOrigin
... | nothing = nothing
... | just positionNumber = just (fsuc positionNumber)

find_old_chamber : List (OldChamber tetrahedra) → Fin tetrahedra → Nat → Maybe Nat
find_old_chamber [] wantedTetrahedron nextNumber = nothing
find_old_chamber (headChamber ∷ remainingChambers) wantedTetrahedron nextNumber
  with fin_equal (old_tetrahedron headChamber) wantedTetrahedron
... | true = just nextNumber
... | false = find_old_chamber remainingChambers wantedTetrahedron (suc nextNumber)

record FacetReplacement (outputTetrahedra : Nat) : Set where
  constructor facet_replacement
  field
    replacement_facet : Facet 3 outputTetrahedra
    replacement_vertex_mapping : Permutation 4
open FacetReplacement public

translate_old_facet : {currentTriangulation : Triangulation 3 tetrahedra} →
  (regionValue : PachnerRegion currentTriangulation) →
  (originValues : List (ChamberOrigin tetrahedra)) → Facet 3 tetrahedra →
  Maybe (FacetReplacement (length originValues))
translate_old_facet regionValue originValues oldFacet with
  find_old_chamber (old_chambers regionValue) (simplex_number oldFacet) zero
... | nothing with find_origin originValues (retained_chamber (simplex_number oldFacet))
... | nothing = nothing
... | just newIndex = just (facet_replacement (facet newIndex (opposite_vertex oldFacet)) identity)
translate_old_facet regionValue originValues oldFacet | just chamberNumber
  with Lists.lookupList chamberNumber (old_chambers regionValue)
... | nothing = nothing
... | just oldChamber with external_old_facet (central_face_dimension regionValue)
    chamberNumber (preimage (old_vertex_frame oldChamber) (opposite_vertex oldFacet))
... | false = nothing
... | true with move_permutation (central_face_dimension regionValue) chamberNumber newNumber |
    find_origin originValues (replacement_chamber newNumber)
  where
  conceptualFacet = fin_to_nat
    (preimage (old_vertex_frame oldChamber) (opposite_vertex oldFacet))
  newNumber : Nat
  newNumber with less_than conceptualFacet (fin_to_nat (central_face_dimension regionValue))
  ... | true = conceptualFacet
  ... | false = fin_to_nat (central_face_dimension regionValue)
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just conceptualMapping | just newIndex = just (facet_replacement
    (facet newIndex (image oldToNew (opposite_vertex oldFacet))) oldToNew)
  where
  oldToNew = compose conceptualMapping (inverse (old_vertex_frame oldChamber))

-- Express a new exterior facet in the old chamber that supplied it.
complement_dimension : {currentTriangulation : Triangulation 3 tetrahedra} →
  PachnerRegion currentTriangulation → Nat
complement_dimension regionValue = 3 - fin_to_nat (central_face_dimension regionValue)

selected_old_number : {currentTriangulation : Triangulation 3 tetrahedra} →
  PachnerRegion currentTriangulation → Fin 4 → Nat
selected_old_number regionValue facetNumber
  with less_than (fin_to_nat facetNumber) (complement_dimension regionValue)
... | true = fin_to_nat facetNumber
... | false = complement_dimension regionValue

old_conceptual_facet : {currentTriangulation : Triangulation 3 tetrahedra} →
  PachnerRegion currentTriangulation → Nat → Fin 4 → Nat
old_conceptual_facet regionValue newNumber facetNumber
  with less_than newNumber (fin_to_nat (central_face_dimension regionValue))
... | true = newNumber
... | false = fin_to_nat (central_face_dimension regionValue) +
    selected_old_number regionValue facetNumber

old_source_for_facet : {currentTriangulation : Triangulation 3 tetrahedra} →
  PachnerRegion currentTriangulation → ChamberOrigin tetrahedra → Fin 4 →
  Maybe (Facet 3 tetrahedra)
old_source_for_facet regionValue (retained_chamber oldIndex) facetNumber =
  just (facet oldIndex facetNumber)
old_source_for_facet regionValue (replacement_chamber newNumber) facetNumber
  with less_than (fin_to_nat facetNumber) (complement_dimension regionValue) or
    nat_equal (fin_to_nat facetNumber) (complement_dimension regionValue + newNumber)
... | false = nothing
... | true with Lists.lookupList (selected_old_number regionValue facetNumber)
    (old_chambers regionValue)
... | nothing = nothing
... | just oldChamber with fin_from_nat 4
    (old_conceptual_facet regionValue newNumber facetNumber)
... | nothing = nothing
... | just boundedFacet = just (facet (old_tetrahedron oldChamber)
    (image (old_vertex_frame oldChamber) boundedFacet))

-- Three cases remain explicit: old exterior adjacency, new interior
-- adjacency, and a real boundary. A malformed replacement is a failure.
exterior_adjacency : (currentTriangulation : Triangulation 3 tetrahedra) →
  (regionValue : PachnerRegion currentTriangulation) →
  (originValues : List (ChamberOrigin tetrahedra)) → Facet 3 tetrahedra →
  Maybe (Maybe (Gluing 3 (length originValues)))
exterior_adjacency currentTriangulation regionValue originValues oldFacet
  with translate_old_facet regionValue originValues oldFacet |
    adjacency (raw_state currentTriangulation) oldFacet
... | nothing | _ = nothing
... | just _ | nothing = just nothing
... | just sourceReplacement | just outward
  with translate_old_facet regionValue originValues (destination oldFacet outward)
... | nothing = nothing
... | just targetReplacement = just (just (gluing
    (simplex_number (replacement_facet targetReplacement))
    (compose (replacement_vertex_mapping targetReplacement)
      (compose (vertex_permutation outward)
        (inverse (replacement_vertex_mapping sourceReplacement))))))

replacement_adjacency : (currentTriangulation : Triangulation 3 tetrahedra) →
  (regionValue : PachnerRegion currentTriangulation) →
  (originValues : List (ChamberOrigin tetrahedra)) → ChamberOrigin tetrahedra → Fin 4 →
  Maybe (Maybe (Gluing 3 (length originValues)))
replacement_adjacency currentTriangulation regionValue originValues chamberOrigin facetNumber
  with old_source_for_facet regionValue chamberOrigin facetNumber
... | just oldFacet = exterior_adjacency currentTriangulation regionValue originValues oldFacet
... | nothing with chamberOrigin
... | retained_chamber _ = nothing
... | replacement_chamber newNumber with fin_from_nat 4 (complementDimension + newNumber) |
    find_origin originValues (replacement_chamber (fin_to_nat facetNumber - complementDimension))
  where
  complementDimension = 3 - fin_to_nat (central_face_dimension regionValue)
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just sourceCentralVertex | just targetIndex with swap_vertices sourceCentralVertex facetNumber
... | nothing = nothing
... | just swapMapping = just (just (gluing targetIndex swapMapping))

facet_lock_after_move : (currentTriangulation : Triangulation 3 tetrahedra) →
  PachnerRegion currentTriangulation → ChamberOrigin tetrahedra → Fin 4 → Bool
facet_lock_after_move currentTriangulation regionValue chamberOrigin facetNumber
  with old_source_for_facet regionValue chamberOrigin facetNumber
... | nothing = false
... | just oldFacet = facet_is_locked (raw_state currentTriangulation) oldFacet

simplex_lock_after_move : Triangulation 3 tetrahedra → ChamberOrigin tetrahedra → Bool
simplex_lock_after_move currentTriangulation (retained_chamber oldIndex) =
  simplex_is_locked (raw_state currentTriangulation) oldIndex
simplex_lock_after_move currentTriangulation (replacement_chamber _) = false

record PachnerResult : Set where
  constructor pachner_result
  field
    resulting_tetrahedron_count : Nat
    resulting_triangulation : Triangulation 3 resulting_tetrahedron_count
open PachnerResult public

perform_region : (currentTriangulation : Triangulation 3 tetrahedra) →
  PachnerRegion currentTriangulation → Maybe PachnerResult
perform_region currentTriangulation regionValue with chamber_origins regionValue
... | originValues with Sequence.sequence (map
    (λ currentFacet → replacement_adjacency currentTriangulation regionValue originValues
      (Indexed.lookup originValues (simplex_number currentFacet)) (opposite_vertex currentFacet))
    (all_facets 3 (length originValues)))
... | nothing = nothing
... | just adjacencies with certify (raw_triangulation
    (λ currentFacet → read_adjacency currentFacet)
    (λ currentFacet → facet_lock_after_move currentTriangulation regionValue
      (Indexed.lookup originValues (simplex_number currentFacet)) (opposite_vertex currentFacet))
    (λ simplexIndex → simplex_lock_after_move currentTriangulation (Indexed.lookup originValues simplexIndex)))
  where
  read_adjacency : Facet 3 (length originValues) → Maybe (Gluing 3 (length originValues))
  read_adjacency currentFacet with Lists.lookupList
    (fin_to_nat (simplex_number currentFacet) * 4 + fin_to_nat (opposite_vertex currentFacet)) adjacencies
  ... | nothing = nothing
  ... | just storedAdjacency = storedAdjacency
... | rejected _ = nothing
... | accepted checkedTriangulation = just (pachner_result (length originValues) checkedTriangulation)

perform_pachner_move : (currentTriangulation : Triangulation 3 tetrahedra) →
  LocalFace 3 tetrahedra → Maybe PachnerResult
perform_pachner_move currentTriangulation localFaceValue with prepare_region currentTriangulation localFaceValue
... | nothing = nothing
... | just regionValue = perform_region currentTriangulation regionValue

subdivide_tetrahedron : Triangulation 3 tetrahedra → Fin tetrahedra → Maybe PachnerResult
subdivide_tetrahedron currentTriangulation tetrahedronIndex = perform_pachner_move currentTriangulation
  (local_face tetrahedronIndex (tabulate_vector 4 (λ _ → true)))
