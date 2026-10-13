{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- TriangulationBase<dim>::boundaryMap<subdim>(), algebra-impl.h, 256-341.
-- Storage-neutral local-face lookup uses selected vertex masks instead of
-- packed face-number tables. All original boundary signs are retained.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.PrimalBoundary where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks
open import Regina.IntegerMatrix
open import Regina.Integer using (Int; pos; negsuc)
open import Regina.AbelianGroup
import Regina.Integer as Integer
import Regina.Embeddings as Embeddings
import Regina.Components as Components
import Regina.ChainHomology as Lists
import Regina.DualPresentation3 as Sequence

private
  variable
    dimension simplices : Nat

representatives : List (FaceLinkClass dimension simplices) →
  List (Embeddings.FaceEmbedding dimension simplices)
representatives [] = []
representatives (headClass ∷ remaining) with face_link_embeddings headClass
... | [] = representatives remaining
... | headEmbedding ∷ tail = headEmbedding ∷ representatives remaining

cellRepresentatives : Triangulation dimension simplices → Nat →
  List (Embeddings.FaceEmbedding dimension simplices)
cellRepresentatives {dimension} {simplices} currentTriangulation cellDimension
  with nat_equal cellDimension dimension
... | false = representatives (faceLinkClasses currentTriangulation cellDimension)
... | true = map (λ simplexIndex → Embeddings.face_embedding
  (local_face simplexIndex (tabulate_vector (suc dimension) (λ _ → true)))
  (all_fin (suc dimension))) (all_fin simplices)

cellCount : Triangulation dimension simplices → Nat → Nat
cellCount currentTriangulation cellDimension = length
  (cellRepresentatives currentTriangulation cellDimension)

lowerCellCount : Triangulation dimension simplices → Nat → Nat
lowerCellCount currentTriangulation zero = zero
lowerCellCount currentTriangulation (suc lowerDimension) = cellCount currentTriangulation lowerDimension

take : {element : Set} → Nat → List element → List element
take zero values = []
take (suc remaining) [] = []
take (suc remaining) (head ∷ tail) = head ∷ take remaining tail

localSelectedFace : Fin simplices → List (Fin (suc dimension)) →
  LocalFace dimension simplices
localSelectedFace {dimension = dimension} simplexIndex selectedVertices = local_face simplexIndex
  (tabulate_vector (suc dimension) (λ vertex → any (fin_equal vertex) selectedVertices))

record IndexedEmbedding (dimension simplices : Nat) : Set where
  constructor indexed_embedding
  field
    class_index : Nat
    class_embedding : Embeddings.FaceEmbedding dimension simplices
open IndexedEmbedding public

findEmbedding : Nat → LocalFace dimension simplices →
  List (FaceLinkClass dimension simplices) → Maybe (IndexedEmbedding dimension simplices)
findEmbedding currentIndex wantedFace [] = nothing
findEmbedding currentIndex wantedFace (headClass ∷ remaining)
  with Embeddings.findEmbeddingForFace wantedFace (face_link_embeddings headClass)
... | nothing = findEmbedding (suc currentIndex) wantedFace remaining
... | just matchingEmbedding = just (indexed_embedding currentIndex matchingEmbedding)

transposition : {degree : Nat} → Fin degree → Fin degree → Maybe (Permutation degree)
transposition {degree} firstIndex secondIndex = from_image_function forwardImage
  where
  forwardImage : Fin degree → Fin degree
  forwardImage currentIndex with fin_equal currentIndex firstIndex
  ... | true = secondIndex
  ... | false with fin_equal currentIndex secondIndex
  ... | true = firstIndex
  ... | false = currentIndex

record BoundaryTerm : Set where
  constructor boundary_term
  field
    term_target_class : Nat
    term_sign : Int
open BoundaryTerm public

isOdd : Nat → Bool
isOdd zero = false
isOdd (suc remaining) = not (isOdd remaining)

signedIncidence : Nat → Nat → Permutation (suc dimension) → Int
signedIncidence lowerVertices removedPosition relativeMapping
  with bool_equal (isOdd removedPosition)
    (Components.oddPermutationImages (take lowerVertices (image_table relativeMapping)))
... | true = pos 1
... | false = negsuc zero

oneBoundaryTerm : Nat → Nat → Fin simplices → Permutation (suc dimension) →
  List (FaceLinkClass dimension simplices) → Maybe BoundaryTerm
oneBoundaryTerm lowerVertices removedPosition simplexIndex cellMapping lowerClasses
  with findEmbedding zero (localSelectedFace simplexIndex
    (take lowerVertices (map (image cellMapping) (all_fin _)))) lowerClasses
... | nothing = nothing
... | just occurrenceValue with from_image_list _
    (Embeddings.embeddingVertexTable (class_embedding occurrenceValue))
... | nothing = nothing
... | just lowerMapping = just (boundary_term (class_index occurrenceValue)
  (signedIncidence lowerVertices removedPosition (compose (inverse lowerMapping) cellMapping)))

boundaryTerms : Nat → Nat → Nat → Fin simplices → Permutation (suc dimension) →
  List (FaceLinkClass dimension simplices) → Maybe (List BoundaryTerm)
boundaryTerms lowerVertices zero removedPosition simplexIndex cellMapping lowerClasses = just []
boundaryTerms {dimension = dimension} lowerVertices (suc remainingSteps) removedPosition
  simplexIndex cellMapping lowerClasses
  with oneBoundaryTerm lowerVertices removedPosition simplexIndex cellMapping lowerClasses
... | nothing = nothing
... | just currentTerm with removedPosition
... | zero = just (currentTerm ∷ [])
... | suc remainingPosition
  with fin_from_nat (suc dimension) remainingPosition |
    fin_from_nat (suc dimension) lowerVertices
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just firstIndex | just secondIndex with transposition firstIndex secondIndex
... | nothing = nothing
... | just swapping with boundaryTerms lowerVertices remainingSteps remainingPosition simplexIndex
    (compose cellMapping swapping) lowerClasses
... | nothing = nothing
... | just remainingTerms = just (currentTerm ∷ remainingTerms)

cellBoundaryTerms : Nat → List (FaceLinkClass dimension simplices) →
  Embeddings.FaceEmbedding dimension simplices → Maybe (List BoundaryTerm)
cellBoundaryTerms lowerVertices lowerClasses currentEmbedding
  with from_image_list _ (Embeddings.embeddingVertexTable currentEmbedding)
... | nothing = nothing
... | just cellMapping = boundaryTerms lowerVertices (suc lowerVertices) lowerVertices
  (face_simplex (Embeddings.embedded_local_face currentEmbedding)) cellMapping lowerClasses

termSum : Nat → List BoundaryTerm → Int
termSum targetClass [] = pos zero
termSum targetClass (headTerm ∷ remaining) with nat_equal targetClass (term_target_class headTerm)
... | true = Integer.add (term_sign headTerm) (termSum targetClass remaining)
... | false = termSum targetClass remaining

boundaryMap : (currentTriangulation : Triangulation dimension simplices) (cellDimension : Nat) →
  Maybe (Matrix (lowerCellCount currentTriangulation cellDimension)
    (cellCount currentTriangulation cellDimension))
boundaryMap currentTriangulation zero = just
  (zeroMatrix zero (cellCount currentTriangulation zero))
boundaryMap currentTriangulation (suc lowerDimension) with Sequence.sequence
  (map (cellBoundaryTerms (suc lowerDimension) (faceLinkClasses currentTriangulation lowerDimension))
    (cellRepresentatives currentTriangulation (suc lowerDimension)))
... | nothing = nothing
... | just columnsOfTerms = just (tabulate
  (cellCount currentTriangulation lowerDimension)
  (cellCount currentTriangulation (suc lowerDimension))
  (λ currentRow currentColumn → termSum (fin_to_nat currentRow)
    (lookupTerms columnsOfTerms (fin_to_nat currentColumn))))
  where
  lookupTerms : List (List BoundaryTerm) → Nat → List BoundaryTerm
  lookupTerms [] currentIndex = []
  lookupTerms (head ∷ tail) zero = head
  lookupTerms (head ∷ tail) (suc currentIndex) = lookupTerms tail currentIndex

-- This computes the homology of the primal quotient, including its ideal
-- vertices. Regina's homology() uses the truncated dual complex instead.
primalHomology : Nat → Triangulation dimension simplices → Nat → Maybe AbelianGroup
primalHomology fuel currentTriangulation cellDimension
  with boundaryMap currentTriangulation cellDimension |
    boundaryMap currentTriangulation (suc cellDimension)
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just firstBoundary | just nextBoundary = Lists.chainHomology fuel firstBoundary nextBoundary
