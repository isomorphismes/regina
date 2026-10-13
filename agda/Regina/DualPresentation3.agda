{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- TriangulationBase<3>::homology<1>() and group(), from
-- engine/triangulation/detail/algebra-impl.h, lines 53-139 and 185-249.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.DualPresentation3 where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Permutation
open import Regina.Skeleton
open import Regina.FaceLinks
open import Regina.IntegerMatrix
open import Regina.Integer using (Int; pos; negsuc)
open import Regina.AbelianGroup
import Regina.Integer as Integer
import Regina.Embeddings as Embeddings
import Regina.ExactEdgeLinks3 as ExactEdges
import Regina.FacetOperations3 as Frames
import Regina.FaceProperties3 as Properties
import Regina.TetrahedronFaces3 as TetrahedronFaces
import Regina.SubfaceIncidence3 as Subfaces
import Regina.Link3 as Links
import Regina.Components as Components
import Regina.ChainHomology as Lists

private
  variable
    simplex_count : Nat

record DualGenerator3 (simplex_count : Nat) : Set where
  constructor dual_generator_three
  field
    generator_triangle_number : Nat
    generator_triangle_frame : Frames.FacetFrame3 simplex_count
open DualGenerator3 public

generatorCandidates : Triangulation 3 simplex_count → Nat →
  List (FaceLinkClass 3 simplex_count) → List (Maybe (DualGenerator3 simplex_count))
generatorCandidates currentTriangulation nextNumber [] = []
generatorCandidates currentTriangulation nextNumber (triangleClass ∷ remaining)
  with Links.faceLinkClassTouchesBoundary currentTriangulation triangleClass or
    Properties.triangleClassInDualForest currentTriangulation triangleClass
... | true = generatorCandidates currentTriangulation (suc nextNumber) remaining
... | false with Frames.facetFrame currentTriangulation nextNumber
... | rejected _ = nothing ∷ generatorCandidates currentTriangulation (suc nextNumber) remaining
... | accepted frameValue = just (dual_generator_three nextNumber frameValue) ∷
  generatorCandidates currentTriangulation (suc nextNumber) remaining

sequence : {element : Set} → List (Maybe element) → Maybe (List element)
sequence [] = just []
sequence (nothing ∷ tail) = nothing
sequence (just head ∷ tail) with sequence tail
... | nothing = nothing
... | just remaining = just (head ∷ remaining)

record GroupLetter (generators : Nat) : Set where
  constructor group_letter
  field
    letter_generator : Fin generators
    letter_forward : Bool
open GroupLetter public

findGenerator : (generators : List (DualGenerator3 simplex_count)) → Nat →
  Maybe (Fin (length generators))
findGenerator [] wantedNumber = nothing
findGenerator (head ∷ tail) wantedNumber
  with nat_equal (generator_triangle_number head) wantedNumber
... | true = just fzero
... | false with findGenerator tail wantedNumber
... | nothing = nothing
... | just index = just (fsuc index)

letterForEmbedding : Triangulation 3 simplex_count →
  (generators : List (DualGenerator3 simplex_count)) →
  Embeddings.FaceEmbedding 3 simplex_count →
  Maybe (Maybe (GroupLetter (length generators)))
letterForEmbedding currentTriangulation generators currentEmbedding
  with Subfaces.lookupList 2 (Embeddings.ordered_simplex_vertices currentEmbedding)
... | nothing = nothing
... | just exitVertex with TetrahedronFaces.tetrahedronTriangleReference currentTriangulation
    (fin_to_nat (face_simplex (Embeddings.embedded_local_face currentEmbedding)))
    (fin_to_nat exitVertex)
... | nothing = nothing
... | just reference with findGenerator generators
    (TetrahedronFaces.tetrahedron_face_class_number reference)
... | nothing = just nothing
... | just index = just (just (group_letter index
    (facet_equal (facet
      (face_simplex (Embeddings.embedded_local_face currentEmbedding)) exitVertex)
      (Frames.framedFacet (generator_triangle_frame (Lists.lookup generators index))))))

collectLetters : {generators : Nat} →
  List (Maybe (Maybe (GroupLetter generators))) → Maybe (List (GroupLetter generators))
collectLetters [] = just []
collectLetters (nothing ∷ remaining) = nothing
collectLetters (just nothing ∷ remaining) = collectLetters remaining
collectLetters (just (just head) ∷ remaining) with collectLetters remaining
... | nothing = nothing
... | just tail = just (head ∷ tail)

internalEdge : ExactEdges.OrderedEdgeLink3 simplex_count → Bool
internalEdge currentEdge with ExactEdges.ordered_edge_shape currentEdge
... | ExactEdges.edge_link_cycle = true
... | _ = false

record DualPresentation3 : Set where
  constructor dual_presentation_three
  field
    dual_generator_count : Nat
    dual_relations : List (List (GroupLetter dual_generator_count))
open DualPresentation3 public

buildWithGenerators : Triangulation 3 simplex_count →
  List (DualGenerator3 simplex_count) → Maybe DualPresentation3
buildWithGenerators currentTriangulation generators
  with sequence (map (λ currentEdge → collectLetters (map
    (letterForEmbedding currentTriangulation generators)
    (ExactEdges.ordered_edge_embeddings currentEdge)))
    (Lists.filter internalEdge (ExactEdges.orderedEdgeLinks3 currentTriangulation)))
... | nothing = nothing
... | just words = just (dual_presentation_three (length generators) words)

dualPresentation : Triangulation 3 simplex_count → Maybe DualPresentation3
dualPresentation currentTriangulation
  with ExactEdges.allOrderedEdgeWalksComplete currentTriangulation and
    ExactEdges.orderedEdgeOccurrencesComplete currentTriangulation
... | false = nothing
... | true with sequence (generatorCandidates currentTriangulation zero
    (faceLinkClasses currentTriangulation 2))
... | nothing = nothing
... | just generators = buildWithGenerators currentTriangulation generators

coefficientInWord : {generators : Nat} → Fin generators → List (GroupLetter generators) → Int
coefficientInWord generatorNumber [] = pos zero
coefficientInWord generatorNumber (headLetter ∷ remaining)
  with fin_equal generatorNumber (letter_generator headLetter)
... | false = coefficientInWord generatorNumber remaining
... | true with letter_forward headLetter
... | true = Integer.add (pos 1) (coefficientInWord generatorNumber remaining)
... | false = Integer.add (negsuc zero) (coefficientInWord generatorNumber remaining)

abelianPresentation : (presentationValue : DualPresentation3) →
  Matrix (length (dual_relations presentationValue)) (dual_generator_count presentationValue)
abelianPresentation presentationValue = tabulate
  (length (dual_relations presentationValue)) (dual_generator_count presentationValue)
  (λ relationNumber generatorNumber → coefficientInWord generatorNumber
    (Lists.lookup (dual_relations presentationValue) relationNumber))

firstHomology : Nat → Triangulation 3 simplex_count → Maybe AbelianGroup
firstHomology fuel currentTriangulation with dualPresentation currentTriangulation
... | nothing = nothing
... | just presentationValue = groupFromPresentation fuel (abelianPresentation presentationValue)

-- Regina requires at most one connected component for group(). The raw
-- dual presentation precedes its additional Tietze simplification.
fundamentalGroupPresentation : Triangulation 3 simplex_count → Maybe DualPresentation3
fundamentalGroupPresentation currentTriangulation
  with Integer.natural_less 1 (length (Components.simplexComponents currentTriangulation))
... | true = nothing
... | false = dualPresentation currentTriangulation
