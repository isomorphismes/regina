{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- TriangulationBase<3>::dualBoundaryMap(), algebra-impl.h, 346-428.
-- Ideal and real-boundary faces are omitted from the dual complex, as in Regina.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.DualBoundary3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks
open import Regina.IntegerMatrix
open import Regina.Integer using (Int; pos; negsuc)
open import Regina.AbelianGroup
import Regina.Integer as Integer
import Regina.Components as Components
import Regina.Embeddings as Embeddings
import Regina.Link3 as Links
import Regina.FaceProperties3 as Properties
import Regina.Validity3 as Validity
import Regina.PrimalBoundary as Primal
import Regina.ChainHomology as Lists
import Regina.DualPresentation3 as Sequence

private
  variable
    simplices : Nat

record IndexedClass3 (simplices : Nat) : Set where
  constructor indexed_class_three
  field
    indexed_number : Nat
    indexed_value : FaceLinkClass 3 simplices
open IndexedClass3 public

indexClasses : Nat → List (FaceLinkClass 3 simplices) → List (IndexedClass3 simplices)
indexClasses nextNumber [] = []
indexClasses nextNumber (head ∷ remaining) = indexed_class_three nextNumber head ∷
  indexClasses (suc nextNumber) remaining

private
  lookupVertex : Nat → List Properties.VertexProperties3 → Maybe Properties.VertexProperties3
  lookupVertex zero [] = nothing
  lookupVertex zero (head ∷ tail) = just head
  lookupVertex (suc requested) [] = nothing
  lookupVertex (suc requested) (head ∷ tail) = lookupVertex requested tail

internalClass : Triangulation 3 simplices → Nat → IndexedClass3 simplices → Bool
internalClass currentTriangulation zero indexedClass
  with lookupVertex (indexed_number indexedClass) (Properties.vertexProperties currentTriangulation)
... | nothing = false
... | just vertexValue = not (Properties.core_is_boundary (Properties.vertex_core vertexValue))
internalClass currentTriangulation (suc requestedDimension) indexedClass = not
  (Links.faceLinkClassTouchesBoundary currentTriangulation (indexed_value indexedClass))

internalClasses : Triangulation 3 simplices → Nat → List (IndexedClass3 simplices)
internalClasses currentTriangulation requestedDimension = Lists.filter
  (internalClass currentTriangulation requestedDimension)
  (indexClasses zero (faceLinkClasses currentTriangulation requestedDimension))

drop : {element : Set} → Nat → List element → List element
drop zero values = values
drop (suc remaining) [] = []
drop (suc remaining) (head ∷ tail) = drop remaining tail

dualTerm : Nat → Fin simplices → Permutation 4 → List (FaceLinkClass 3 simplices) →
  Maybe Primal.BoundaryTerm
dualTerm lowerVertices simplexIndex cellMapping lowerClasses
  with Primal.findEmbedding zero (Primal.localSelectedFace simplexIndex
    (Primal.take lowerVertices (map (image cellMapping) (all_fin 4)))) lowerClasses
... | nothing = nothing
... | just occurrenceValue with from_image_list 4
    (Embeddings.embeddingVertexTable (Primal.class_embedding occurrenceValue))
... | nothing = nothing
... | just lowerMapping with Components.oddPermutationImages
    (drop lowerVertices (image_table (compose (inverse lowerMapping) cellMapping)))
... | false = just (Primal.boundary_term (Primal.class_index occurrenceValue) (pos 1))
... | true = just (Primal.boundary_term (Primal.class_index occurrenceValue) (negsuc zero))

dualTerms : Nat → Nat → Nat → Fin simplices → Permutation 4 →
  List (FaceLinkClass 3 simplices) → Maybe (List Primal.BoundaryTerm)
dualTerms lowerVertices zero removedPosition simplexIndex cellMapping lowerClasses = just []
dualTerms lowerVertices (suc remainingSteps) removedPosition simplexIndex cellMapping lowerClasses
  with dualTerm lowerVertices simplexIndex cellMapping lowerClasses
... | nothing = nothing
... | just currentTerm with removedPosition
... | zero = just (currentTerm ∷ [])
... | suc remainingPosition with fin_from_nat 4 remainingPosition | fin_from_nat 4 lowerVertices
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just firstIndex | just secondIndex with Primal.transposition firstIndex secondIndex
... | nothing = nothing
... | just swapping with dualTerms lowerVertices remainingSteps remainingPosition simplexIndex
    (compose cellMapping swapping) lowerClasses
... | nothing = nothing
... | just remainingTerms = just (currentTerm ∷ remainingTerms)

termsFromClass : Nat → List (FaceLinkClass 3 simplices) → IndexedClass3 simplices →
  Maybe (List Primal.BoundaryTerm)
termsFromClass lowerVertices lowerClasses indexedClass
  with face_link_embeddings (indexed_value indexedClass)
... | [] = nothing
... | firstEmbedding ∷ remaining with from_image_list 4 (Embeddings.embeddingVertexTable firstEmbedding)
... | nothing = nothing
... | just cellMapping = dualTerms lowerVertices (suc lowerVertices) lowerVertices
  (face_simplex (Embeddings.embedded_local_face firstEmbedding)) cellMapping lowerClasses

makeHigherDualBoundary : (currentTriangulation : Triangulation 3 simplices) → (lowerDimension : Nat) →
  Maybe (Matrix (length (internalClasses currentTriangulation (suc lowerDimension)))
    (length (internalClasses currentTriangulation lowerDimension)))
makeHigherDualBoundary currentTriangulation lowerDimension
  with Sequence.sequence (map (termsFromClass (suc lowerDimension)
    (faceLinkClasses currentTriangulation lowerDimension))
    (internalClasses currentTriangulation (suc lowerDimension)))
... | nothing = nothing
... | just rowsOfTerms = just (tabulate
  (length (internalClasses currentTriangulation (suc lowerDimension)))
  (length (internalClasses currentTriangulation lowerDimension))
  (λ currentRow currentColumn → Primal.termSum
    (indexed_number (Lists.lookup (internalClasses currentTriangulation lowerDimension) currentColumn))
    (lookupRow (fin_to_nat currentRow) rowsOfTerms)))
  where
  lookupRow : Nat → List (List Primal.BoundaryTerm) → List Primal.BoundaryTerm
  lookupRow zero [] = []
  lookupRow zero (head ∷ tail) = head
  lookupRow (suc requested) [] = []
  lookupRow (suc requested) (head ∷ tail) = lookupRow requested tail

dualEdgeColumn : IndexedClass3 simplices → Maybe (Fin simplices → Int)
dualEdgeColumn {simplices} indexedClass with face_link_embeddings (indexed_value indexedClass)
... | firstEmbedding ∷ secondEmbedding ∷ [] = just coefficientValue
  where
  coefficientValue : Fin simplices → Int
  coefficientValue simplexIndex = Integer.subtract
    (indicator simplexIndex firstEmbedding) (indicator simplexIndex secondEmbedding)
    where
    indicator : Fin simplices → Embeddings.FaceEmbedding 3 simplices → Int
    indicator simplexIndex currentEmbedding
      with fin_equal simplexIndex (face_simplex (Embeddings.embedded_local_face currentEmbedding))
    ... | true = pos 1
    ... | false = pos zero
... | _ = nothing

dualBoundaryOne : (currentTriangulation : Triangulation 3 simplices) →
  Maybe (Matrix simplices (length (internalClasses currentTriangulation 2)))
dualBoundaryOne {simplices} currentTriangulation with Sequence.sequence
  (map dualEdgeColumn (internalClasses currentTriangulation 2))
... | nothing = nothing
... | just columnsOfCoefficients = just (tabulate simplices
  (length (internalClasses currentTriangulation 2))
  (λ currentRow currentColumn → lookupColumn (fin_to_nat currentColumn) columnsOfCoefficients currentRow))
  where
  lookupColumn : Nat → List (Fin simplices → Int) → Fin simplices → Int
  lookupColumn zero [] simplexIndex = pos zero
  lookupColumn zero (head ∷ tail) simplexIndex = head simplexIndex
  lookupColumn (suc requested) [] simplexIndex = pos zero
  lookupColumn (suc requested) (head ∷ tail) simplexIndex = lookupColumn requested tail simplexIndex

dualHomologyUnchecked : Nat → Triangulation 3 simplices → Nat → Maybe AbelianGroup
dualHomologyUnchecked {simplices} fuel currentTriangulation zero
  with dualBoundaryOne currentTriangulation
... | nothing = nothing
... | just firstBoundary = Lists.chainHomology fuel (zeroMatrix zero simplices) firstBoundary
dualHomologyUnchecked fuel currentTriangulation (suc zero)
  with dualBoundaryOne currentTriangulation | makeHigherDualBoundary currentTriangulation 1
... | just firstBoundary | just nextBoundary = Lists.chainHomology fuel firstBoundary nextBoundary
... | _ | _ = nothing
dualHomologyUnchecked fuel currentTriangulation (suc (suc zero))
  with makeHigherDualBoundary currentTriangulation 1 | makeHigherDualBoundary currentTriangulation 0
... | just firstBoundary | just nextBoundary = Lists.chainHomology fuel firstBoundary nextBoundary
... | _ | _ = nothing
dualHomologyUnchecked fuel currentTriangulation (suc (suc (suc zero)))
  with makeHigherDualBoundary currentTriangulation 0
... | nothing = nothing
... | just firstBoundary = Lists.chainHomology fuel firstBoundary
  (zeroMatrix (length (internalClasses currentTriangulation 0)) zero)
dualHomologyUnchecked fuel currentTriangulation (suc (suc (suc (suc remaining)))) =
  just (abelian_group zero [])

dualHomology : Nat → Triangulation 3 simplices → Nat → Maybe AbelianGroup
dualHomology fuel currentTriangulation homologyDegree
  with Validity.threeDimensionalValidityValue currentTriangulation
... | false = nothing
... | true = dualHomologyUnchecked fuel currentTriangulation homologyDegree
