{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-13. License: ../../LICENSE.txt.
-- TriangulationBase<3>::internalPachner(), detail/moves-impl.h, 220-701.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.PachnerRegion3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton using (LocalFace; face_simplex; face_vertices;
  true_count; filter_list; less_than)
open import Agda.Builtin.Nat using (_-_)
import Regina.Components as Components
import Regina.SubfaceIncidence3 as Lists
import Regina.DualPresentation3 as Sequence

private
  variable
    tetrahedra : Nat

swap_vertices : Fin 4 → Fin 4 → Maybe (Permutation 4)
swap_vertices firstVertex secondVertex = from_image_list 4 (map
  (λ currentVertex → fin_to_nat (swapped currentVertex)) (all_fin 4))
  where
  swapped : Fin 4 → Fin 4
  swapped currentVertex with fin_equal currentVertex firstVertex
  ... | true = secondVertex
  ... | false with fin_equal currentVertex secondVertex
  ... | true = firstVertex
  ... | false = currentVertex

record OldChamber (tetrahedra : Nat) : Set where
  constructor old_chamber
  field
    old_tetrahedron : Fin tetrahedra
    old_vertex_frame : Permutation 4
open OldChamber public

old_chamber_count : Fin 4 → Nat
old_chamber_count faceDimension = 4 - fin_to_nat faceDimension

new_chamber_count : Fin 4 → Nat
new_chamber_count faceDimension = suc (fin_to_nat faceDimension)

external_old_facet : Fin 4 → Nat → Fin 4 → Bool
external_old_facet faceDimension chamberNumber facetNumber =
  less_than (fin_to_nat facetNumber) (fin_to_nat faceDimension) or
  nat_equal (fin_to_nat facetNumber) (fin_to_nat faceDimension + chamberNumber)

chambers_distinct : List (OldChamber tetrahedra) → Bool
chambers_distinct [] = true
chambers_distinct (headChamber ∷ remainingChambers) = all
  (λ otherChamber → not (fin_equal (old_tetrahedron headChamber)
    (old_tetrahedron otherChamber))) remainingChambers and chambers_distinct remainingChambers

internal_facet_correct : Triangulation 3 tetrahedra → Fin 4 →
  List (OldChamber tetrahedra) → Nat → OldChamber tetrahedra → Fin 4 → Bool
internal_facet_correct currentTriangulation faceDimension chamberValues chamberNumber
  currentChamber conceptualFacet with external_old_facet faceDimension chamberNumber conceptualFacet
... | true = true
... | false with Lists.lookupList (fin_to_nat conceptualFacet - fin_to_nat faceDimension) chamberValues |
    fin_from_nat 4 (fin_to_nat faceDimension + chamberNumber)
... | nothing | _ = false
... | just _ | nothing = false
... | just otherChamber | just sourceCentralVertex with
    adjacency (raw_state currentTriangulation)
      (facet (old_tetrahedron currentChamber)
        (image (old_vertex_frame currentChamber) conceptualFacet)) |
    swap_vertices sourceCentralVertex conceptualFacet
... | nothing | _ = false
... | just _ | nothing = false
... | just outward | just swapMapping =
    fin_equal (adjacent_simplex outward) (old_tetrahedron otherChamber) and
    decision_bool (permutation_dec_equal (vertex_permutation outward)
      (compose (old_vertex_frame otherChamber)
        (compose swapMapping (inverse (old_vertex_frame currentChamber)))))

numbered_chambers_valid : Triangulation 3 tetrahedra → Fin 4 →
  List (OldChamber tetrahedra) → Nat → List (OldChamber tetrahedra) → Bool
numbered_chambers_valid currentTriangulation faceDimension allChambers nextNumber [] = true
numbered_chambers_valid currentTriangulation faceDimension allChambers nextNumber
  (currentChamber ∷ remainingChambers) =
  not (simplex_is_locked (raw_state currentTriangulation) (old_tetrahedron currentChamber)) and
  all (λ conceptualFacet →
    (external_old_facet faceDimension nextNumber conceptualFacet or
      not (facet_is_locked (raw_state currentTriangulation)
        (facet (old_tetrahedron currentChamber)
          (image (old_vertex_frame currentChamber) conceptualFacet)))) and
    internal_facet_correct currentTriangulation faceDimension allChambers
      nextNumber currentChamber conceptualFacet) (all_fin 4) and
  numbered_chambers_valid currentTriangulation faceDimension allChambers
    (suc nextNumber) remainingChambers

region_legal : Triangulation 3 tetrahedra → Fin 4 → List (OldChamber tetrahedra) → Bool
region_legal currentTriangulation faceDimension chamberValues =
  nat_equal (length chamberValues) (old_chamber_count faceDimension) and
  chambers_distinct chamberValues and
  numbered_chambers_valid currentTriangulation faceDimension chamberValues zero chamberValues

record PachnerRegion (currentTriangulation : Triangulation 3 tetrahedra) : Set where
  constructor pachner_region
  field
    central_face_dimension : Fin 4
    old_chambers : List (OldChamber tetrahedra)
    region_checked : region_legal currentTriangulation central_face_dimension old_chambers ≡ true
open PachnerRegion public

orient_seed_frame : Fin 4 → Permutation 4 → Maybe (Permutation 4)
orient_seed_frame faceDimension seedFrame with nat_equal (fin_to_nat faceDimension) 3
... | true = just seedFrame
... | false with Components.permutationEven seedFrame
... | true = just seedFrame
... | false with nat_equal (fin_to_nat faceDimension) 2
... | true with swap_vertices fzero (fsuc fzero)
... | nothing = nothing
... | just swapMapping = just (compose seedFrame swapMapping)
orient_seed_frame faceDimension seedFrame | false | false | false
  with swap_vertices (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc fzero)))
... | nothing = nothing
... | just swapMapping = just (compose seedFrame swapMapping)

seed_chamber : Fin 4 → LocalFace 3 tetrahedra → Maybe (OldChamber tetrahedra)
seed_chamber faceDimension localFaceValue with from_image_list 4
  (map fin_to_nat (filter_list (lookup_vector (face_vertices localFaceValue)) (all_fin 4)) ++
   map fin_to_nat (filter_list (λ vertexNumber → not
     (lookup_vector (face_vertices localFaceValue) vertexNumber)) (all_fin 4)))
... | nothing = nothing
... | just seedFrame with orient_seed_frame faceDimension seedFrame
... | nothing = nothing
... | just orientedFrame = just (old_chamber (face_simplex localFaceValue) orientedFrame)

neighbor_chamber : Triangulation 3 tetrahedra → Fin 4 → OldChamber tetrahedra → Nat →
  Maybe (OldChamber tetrahedra)
neighbor_chamber currentTriangulation faceDimension seedChamber zero = just seedChamber
neighbor_chamber currentTriangulation faceDimension seedChamber (suc chamberNumber)
  with fin_from_nat 4 (fin_to_nat faceDimension + suc chamberNumber)
... | nothing = nothing
... | just conceptualFacet with
    adjacency (raw_state currentTriangulation) (facet (old_tetrahedron seedChamber)
      (image (old_vertex_frame seedChamber) conceptualFacet)) |
    swap_vertices faceDimension conceptualFacet
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just outward | just swapMapping = just (old_chamber (adjacent_simplex outward)
    (compose (vertex_permutation outward) (compose (old_vertex_frame seedChamber) swapMapping)))

prepare_region : (currentTriangulation : Triangulation 3 tetrahedra) →
  LocalFace 3 tetrahedra → Maybe (PachnerRegion currentTriangulation)
prepare_region currentTriangulation localFaceValue
  with true_count (face_vertices localFaceValue)
... | zero = nothing
... | suc faceDimensionNumber with fin_from_nat 4 faceDimensionNumber
... | nothing = nothing
... | just faceDimension with seed_chamber faceDimension localFaceValue
... | nothing = nothing
... | just seedChamber with Sequence.sequence (map
    (λ chamberNumber → neighbor_chamber currentTriangulation faceDimension seedChamber
      (fin_to_nat chamberNumber)) (all_fin (old_chamber_count faceDimension)))
... | nothing = nothing
... | just chamberValues with bool_dec_equal
    (region_legal currentTriangulation faceDimension chamberValues) true
... | no _ = nothing
... | yes regionProof = just (pachner_region faceDimension chamberValues regionProof)

-- Regina's six exact movePerm<3,1> and six movePerm<3,2> tables.
-- These maps carry all exterior-facet vertices from the old conceptual
-- frame into the new one, and map the missing vertex to the new missing one.
move_permutation : Fin 4 → Nat → Nat → Maybe (Permutation 4)
move_permutation fzero oldNumber newNumber = just identity
move_permutation (fsuc (fsuc (fsuc fzero))) oldNumber newNumber = just identity
move_permutation (fsuc fzero) 0 0 = from_image_list 4 (0 ∷ 3 ∷ 1 ∷ 2 ∷ [])
move_permutation (fsuc fzero) 0 1 = from_image_list 4 (2 ∷ 0 ∷ 1 ∷ 3 ∷ [])
move_permutation (fsuc fzero) 1 0 = from_image_list 4 (1 ∷ 0 ∷ 3 ∷ 2 ∷ [])
move_permutation (fsuc fzero) 1 1 = from_image_list 4 (2 ∷ 0 ∷ 1 ∷ 3 ∷ [])
move_permutation (fsuc fzero) 2 0 = from_image_list 4 (2 ∷ 0 ∷ 1 ∷ 3 ∷ [])
move_permutation (fsuc fzero) 2 1 = from_image_list 4 (2 ∷ 0 ∷ 1 ∷ 3 ∷ [])
move_permutation (fsuc (fsuc fzero)) 0 0 = from_image_list 4 (0 ∷ 2 ∷ 3 ∷ 1 ∷ [])
move_permutation (fsuc (fsuc fzero)) 0 1 = from_image_list 4 (1 ∷ 0 ∷ 3 ∷ 2 ∷ [])
move_permutation (fsuc (fsuc fzero)) 0 2 = from_image_list 4 (1 ∷ 2 ∷ 0 ∷ 3 ∷ [])
move_permutation (fsuc (fsuc fzero)) 1 0 = from_image_list 4 (1 ∷ 2 ∷ 0 ∷ 3 ∷ [])
move_permutation (fsuc (fsuc fzero)) 1 1 = from_image_list 4 (1 ∷ 2 ∷ 0 ∷ 3 ∷ [])
move_permutation (fsuc (fsuc fzero)) 1 2 = from_image_list 4 (1 ∷ 2 ∷ 0 ∷ 3 ∷ [])
move_permutation _ _ _ = nothing
