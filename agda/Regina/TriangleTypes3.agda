{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- Triangle type, subtype, formsMobiusBand(), and formsCone(), from
-- engine/triangulation/face.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950, lines 2037-2131.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission.

module Regina.TriangleTypes3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Components using (permutationEven)
open import Regina.FaceLinks
open import Regina.SubfaceIncidence3

private
  variable
    simplex_count : Nat

-- These are the three inherent positions in the triangle, not vertex
-- numbers in the containing tetrahedron.
record ThreeEntries (element : Set) : Set where
  constructor three_entries
  field
    entry_zero entry_one entry_two : element
open ThreeEntries public

record TriangleIncidence : Set where
  constructor triangle_incidence
  field
    vertex_classes : ThreeEntries Nat
    edge_classes : ThreeEntries Nat
    edge_mapping_even : ThreeEntries Bool
open TriangleIncidence public

-- Store the special role only for the five types that have one. The
-- constructors rule out Unknown and out-of-range subtype values.
data TriangleClassification : Set where
  ordinary_triangle : TriangleClassification
  scarf : Fin 3 → TriangleClassification
  parachute : TriangleClassification
  cone : Fin 3 → TriangleClassification
  mobius_band : Fin 3 → TriangleClassification
  horn : Fin 3 → TriangleClassification
  dunce_hat : Fin 3 → TriangleClassification
  lens_space_three_one_spine : TriangleClassification

triangleTypeCode : TriangleClassification → Nat
triangleTypeCode ordinary_triangle = 1
triangleTypeCode (scarf _) = 2
triangleTypeCode parachute = 3
triangleTypeCode (cone _) = 4
triangleTypeCode (mobius_band _) = 5
triangleTypeCode (horn _) = 6
triangleTypeCode (dunce_hat _) = 7
triangleTypeCode lens_space_three_one_spine = 8

-- nothing corresponds to Regina's -1 sentinel, not to failed recognition.
triangleSubtype : TriangleClassification → Maybe (Fin 3)
triangleSubtype ordinary_triangle = nothing
triangleSubtype (scarf special_vertex) = just special_vertex
triangleSubtype parachute = nothing
triangleSubtype (cone unpaired_edge) = just unpaired_edge
triangleSubtype (mobius_band unpaired_edge) = just unpaired_edge
triangleSubtype (horn unpaired_edge) = just unpaired_edge
triangleSubtype (dunce_hat exceptional_edge) = just exceptional_edge
triangleSubtype lens_space_three_one_spine = nothing

formsMobiusBand : TriangleClassification → Bool
formsMobiusBand (mobius_band _) = true
formsMobiusBand (dunce_hat _) = true
formsMobiusBand lens_space_three_one_spine = true
formsMobiusBand _ = false

formsCone : TriangleClassification → Bool
formsCone (cone _) = true
formsCone (horn _) = true
formsCone (dunce_hat _) = true
formsCone _ = false

private
  position_zero position_one position_two : Fin 3
  position_zero = fzero
  position_one = fsuc fzero
  position_two = fsuc (fsuc fzero)

  allClassesEqual : ThreeEntries Nat → Bool
  allClassesEqual current_classes =
    nat_equal (entry_zero current_classes) (entry_one current_classes) and
    nat_equal (entry_one current_classes) (entry_two current_classes)

  distinctClasses : ThreeEntries Nat → Bool
  distinctClasses current_classes =
    not (nat_equal (entry_zero current_classes) (entry_one current_classes)) and
    not (nat_equal (entry_one current_classes) (entry_two current_classes)) and
    not (nat_equal (entry_two current_classes) (entry_zero current_classes))

  classifyDistinctEdges : ThreeEntries Nat → TriangleClassification
  classifyDistinctEdges vertices with allClassesEqual vertices
  ... | true = parachute
  ... | false with nat_equal (entry_one vertices) (entry_two vertices)
  ... | true = scarf position_zero
  ... | false with nat_equal (entry_two vertices) (entry_zero vertices)
  ... | true = scarf position_one
  ... | false with nat_equal (entry_zero vertices) (entry_one vertices)
  ... | true = scarf position_two
  ... | false = ordinary_triangle

  -- This exhausts all eight Boolean triples. For mixed signs, the
  -- exceptional edge is opposite the equal-sign pair, as in Regina.
  classifyAllEdges : ThreeEntries Bool → TriangleClassification
  classifyAllEdges (three_entries false false false) = lens_space_three_one_spine
  classifyAllEdges (three_entries true true true) = lens_space_three_one_spine
  classifyAllEdges (three_entries true false false) = dunce_hat position_zero
  classifyAllEdges (three_entries false true true) = dunce_hat position_zero
  classifyAllEdges (three_entries false true false) = dunce_hat position_one
  classifyAllEdges (three_entries true false true) = dunce_hat position_one
  classifyAllEdges (three_entries false false true) = dunce_hat position_two
  classifyAllEdges (three_entries true true false) = dunce_hat position_two

  classifyEdgePair : Fin 3 → Bool → Bool → Bool → TriangleClassification
  classifyEdgePair unpaired_edge first_even second_even all_vertices_equal
    with bool_equal first_even second_even
  ... | true = mobius_band unpaired_edge
  ... | false with all_vertices_equal
  ... | true = horn unpaired_edge
  ... | false = cone unpaired_edge

  classifyTwoEdges : TriangleIncidence → TriangleClassification
  classifyTwoEdges (triangle_incidence vertices edges parities) with nat_equal
    (entry_one edges) (entry_two edges)
  ... | true = classifyEdgePair position_zero
    (entry_one parities)
    (entry_two parities)
    (allClassesEqual vertices)
  ... | false with nat_equal
    (entry_two edges) (entry_zero edges)
  ... | true = classifyEdgePair position_one
    (entry_two parities)
    (entry_zero parities)
    (allClassesEqual vertices)
  ... | false = classifyEdgePair position_two
    (entry_zero parities)
    (entry_one parities)
    (allClassesEqual vertices)

-- The finite incidence classifier is meaningful for a triangle's actual
-- quotient data. Arbitrary caller-supplied incidences are not certified as
-- realisable triangulations by this function.
classifyTriangleIncidence : TriangleIncidence → TriangleClassification
classifyTriangleIncidence current_incidence with distinctClasses (edge_classes current_incidence)
... | true = classifyDistinctEdges (vertex_classes current_incidence)
... | false with allClassesEqual (edge_classes current_incidence)
... | true = classifyAllEdges (edge_mapping_even current_incidence)
... | false = classifyTwoEdges current_incidence

private
  edgeReferenceDefined : Triangulation 3 simplex_count → SubfaceReference3 → Bool
  edgeReferenceDefined currentTriangulation current_reference
    with lookupList (referenced_face_class_number current_reference)
      (faceLinkClasses currentTriangulation 1)
  ... | nothing = false
  ... | just currentClass = not (face_has_bad_identification currentClass)

  assembleIncidence : Triangulation 3 simplex_count →
    Maybe SubfaceReference3 → Maybe SubfaceReference3 → Maybe SubfaceReference3 →
    Maybe SubfaceReference3 → Maybe SubfaceReference3 → Maybe SubfaceReference3 →
    Maybe TriangleIncidence
  assembleIncidence currentTriangulation
    (just vertex_zero) (just vertex_one) (just vertex_two)
    (just edge_zero) (just edge_one) (just edge_two)
    with edgeReferenceDefined currentTriangulation edge_zero and
      edgeReferenceDefined currentTriangulation edge_one and
      edgeReferenceDefined currentTriangulation edge_two
  ... | false = nothing
  ... | true = just (triangle_incidence
    (three_entries
      (referenced_face_class_number vertex_zero)
      (referenced_face_class_number vertex_one)
      (referenced_face_class_number vertex_two))
    (three_entries
      (referenced_face_class_number edge_zero)
      (referenced_face_class_number edge_one)
      (referenced_face_class_number edge_two))
    (three_entries
      (permutationEven (referenced_face_mapping edge_zero))
      (permutationEven (referenced_face_mapping edge_one))
      (permutationEven (referenced_face_mapping edge_two))))
  assembleIncidence currentTriangulation _ _ _ _ _ _ = nothing

-- Failed lookups and reversed self-identifications are explicit failures.
-- Regina leaves triangleType() undefined for badly identified edges;
-- this interface returns nothing instead of supplying an arbitrary type.
triangleIncidence : Triangulation 3 simplex_count → Nat → Maybe TriangleIncidence
triangleIncidence currentTriangulation triangle_class_number = assembleIncidence
  currentTriangulation
  (triangleVertexReference currentTriangulation triangle_class_number 0)
  (triangleVertexReference currentTriangulation triangle_class_number 1)
  (triangleVertexReference currentTriangulation triangle_class_number 2)
  (triangleEdgeReference currentTriangulation triangle_class_number 0)
  (triangleEdgeReference currentTriangulation triangle_class_number 1)
  (triangleEdgeReference currentTriangulation triangle_class_number 2)

triangleClassification : Triangulation 3 simplex_count → Nat →
  Maybe TriangleClassification
triangleClassification currentTriangulation triangle_class_number
  with triangleIncidence currentTriangulation triangle_class_number
... | nothing = nothing
... | just current_incidence = just (classifyTriangleIncidence current_incidence)

triangleClassifications : Triangulation 3 simplex_count →
  List (Maybe TriangleClassification)
triangleClassifications currentTriangulation = map
  (triangleClassification currentTriangulation)
  (naturalRange (length (faceLinkClasses currentTriangulation 2)))
