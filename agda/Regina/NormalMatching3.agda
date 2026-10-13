{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- makeMatchingEquations(): Standard, AlmostNormal, Quad and QuadOct,
-- engine/surface/matching.cpp, lines 73-176.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.NormalMatching3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.PermutationExtension using (includeInitialIndex)
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks
open import Regina.NormalCoordinates3
open import Regina.IntegerMatrix
open import Regina.Integer using (Int; pos; negsuc)
import Regina.Integer as Integer
import Regina.Embeddings as Embeddings
import Regina.ExactEdgeLinks3 as ExactEdges
import Regina.SubfaceIncidence3 as Subfaces
import Regina.Link3 as Links
import Regina.ChainHomology as Lists
import Regina.DualPresentation3 as Sequence

private
  variable
    tetrahedra : Nat

record CoordinateTerm3 (tetrahedra : Nat) : Set where
  constructor coordinate_term_three
  field
    term_tetrahedron : Fin tetrahedra
    term_disc_type : Nat
    term_coefficient : Int
open CoordinateTerm3 public

arcTerms : NormalCoords → Int → Embeddings.FaceEmbedding 3 tetrahedra →
  Fin 3 → Maybe (List (CoordinateTerm3 tetrahedra))
arcTerms {tetrahedra} encoding coefficientValue currentEmbedding arcType
  with from_image_list 4 (Embeddings.embeddingVertexTable currentEmbedding)
... | nothing = nothing
... | just vertexMapping
  with quadSeparating (image vertexMapping (includeInitialIndex arcType))
    (image vertexMapping ExactEdges.vertexThree)
... | nothing = nothing
... | just separatingType = just
  (coordinate_term_three simplexIndex (fin_to_nat (image vertexMapping (includeInitialIndex arcType)))
    coefficientValue ∷
   coordinate_term_three simplexIndex (4 + fin_to_nat separatingType) coefficientValue ∷
   octagonTerms)
  where
  simplexIndex = face_simplex (Embeddings.embedded_local_face currentEmbedding)
  octagonTerms : List (CoordinateTerm3 tetrahedra)
  octagonTerms with storesOctagons encoding
  ... | false = []
  ... | true = map (λ meetingType → coordinate_term_three simplexIndex
    (7 + fin_to_nat meetingType) coefficientValue) (quadMeeting separatingType)

triangleRows : NormalCoords → FaceLinkClass 3 tetrahedra →
  Maybe (List (List (CoordinateTerm3 tetrahedra)))
triangleRows encoding triangleClass with face_link_embeddings triangleClass
... | firstEmbedding ∷ secondEmbedding ∷ [] = Sequence.sequence (map
  (λ arcType → combine (arcTerms encoding (pos 1) firstEmbedding arcType)
    (arcTerms encoding (negsuc zero) secondEmbedding arcType)) (all_fin 3))
  where
  combine : {element : Set} → Maybe (List element) → Maybe (List element) → Maybe (List element)
  combine (just first) (just second) = just (first ++ second)
  combine _ _ = nothing
... | _ = nothing

standardRows : NormalCoords → Triangulation 3 tetrahedra →
  Maybe (List (List (CoordinateTerm3 tetrahedra)))
standardRows encoding currentTriangulation with Sequence.sequence (map
  (triangleRows encoding) (Lists.filter
    (λ triangleClass → not (Links.faceLinkClassTouchesBoundary currentTriangulation triangleClass))
    (faceLinkClasses currentTriangulation 2)))
... | nothing = nothing
... | just rowBlocks = just (fold_right _++_ [] rowBlocks)

quadTerms : NormalCoords → Embeddings.FaceEmbedding 3 tetrahedra →
  Maybe (List (CoordinateTerm3 tetrahedra))
quadTerms {tetrahedra} encoding currentEmbedding
  with from_image_list 4 (Embeddings.embeddingVertexTable currentEmbedding)
... | nothing = nothing
... | just vertexMapping
  with quadSeparating (image vertexMapping ExactEdges.vertexZero)
    (image vertexMapping ExactEdges.vertexTwo) |
    quadSeparating (image vertexMapping ExactEdges.vertexZero)
    (image vertexMapping ExactEdges.vertexThree)
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just positiveType | just negativeType = just
  (coordinate_term_three simplexIndex (fin_to_nat positiveType) (pos 1) ∷
   coordinate_term_three simplexIndex (fin_to_nat negativeType) (negsuc zero) ∷
   octagonTerms)
  where
  simplexIndex = face_simplex (Embeddings.embedded_local_face currentEmbedding)
  octagonTerms : List (CoordinateTerm3 tetrahedra)
  octagonTerms with storesOctagons encoding
  ... | false = []
  ... | true =
    coordinate_term_three simplexIndex (3 + fin_to_nat positiveType) (negsuc zero) ∷
    coordinate_term_three simplexIndex (3 + fin_to_nat negativeType) (pos 1) ∷ []

quadRow : NormalCoords → ExactEdges.OrderedEdgeLink3 tetrahedra →
  Maybe (List (CoordinateTerm3 tetrahedra))
quadRow encoding currentEdge with Sequence.sequence
  (map (quadTerms encoding) (ExactEdges.ordered_edge_embeddings currentEdge))
... | nothing = nothing
... | just termBlocks = just (fold_right _++_ [] termBlocks)

quadRows : NormalCoords → Triangulation 3 tetrahedra →
  Maybe (List (List (CoordinateTerm3 tetrahedra)))
quadRows encoding currentTriangulation
  with ExactEdges.allOrderedEdgeWalksComplete currentTriangulation and
    ExactEdges.orderedEdgeOccurrencesComplete currentTriangulation
... | false = nothing
... | true = Sequence.sequence (map (quadRow encoding)
  (Lists.filter Sequence.internalEdge (ExactEdges.orderedEdgeLinks3 currentTriangulation)))

matchingRows : NormalCoords → Triangulation 3 tetrahedra →
  Maybe (List (List (CoordinateTerm3 tetrahedra)))
matchingRows standard = standardRows standard
matchingRows almost_normal = standardRows almost_normal
matchingRows quadrilateral = quadRows quadrilateral
matchingRows quadrilateral_octagon = quadRows quadrilateral_octagon

coefficientForColumn : NormalCoords → Nat → List (CoordinateTerm3 tetrahedra) → Int
coefficientForColumn encoding columnIndex [] = pos zero
coefficientForColumn encoding columnIndex (headTerm ∷ remaining)
  with nat_equal columnIndex (fin_to_nat (term_tetrahedron headTerm) * coordinateBlock encoding +
    term_disc_type headTerm)
... | false = coefficientForColumn encoding columnIndex remaining
... | true = Integer.add (term_coefficient headTerm)
  (coefficientForColumn encoding columnIndex remaining)

record MatchingSystem (encoding : NormalCoords) (tetrahedra : Nat) : Set where
  constructor matching_system
  field
    matching_row_count : Nat
    matching_matrix : Matrix matching_row_count (tetrahedra * coordinateBlock encoding)
open MatchingSystem public

makeMatchingEquations : (encoding : NormalCoords) → Triangulation 3 tetrahedra →
  Maybe (MatchingSystem encoding tetrahedra)
makeMatchingEquations {tetrahedra} encoding currentTriangulation
  with matchingRows encoding currentTriangulation
... | nothing = nothing
... | just rowsOfTerms = just (matching_system (length rowsOfTerms)
  (tabulate (length rowsOfTerms) (tetrahedra * coordinateBlock encoding)
    (λ rowIndex columnIndex → coefficientForColumn encoding (fin_to_nat columnIndex)
      (Lists.lookup rowsOfTerms rowIndex))))

satisfiesMatching : {encoding : NormalCoords} {tetrahedra : Nat} →
  MatchingSystem encoding tetrahedra → SurfaceVector encoding tetrahedra → Bool
satisfiesMatching {encoding} {tetrahedra} systemValue currentSurface = all
  (λ rowIndex → Integer.integer_equal (Integer.sum (map
    (λ columnIndex → Integer.multiply
      (entry (matching_matrix systemValue) rowIndex columnIndex)
      (pos (lookup_vector (coordinates currentSurface) columnIndex)))
    (all_fin (tetrahedra * coordinateBlock encoding)))) (pos zero))
  (all_fin (matching_row_count systemValue))
