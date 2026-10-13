{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- NormalSurface::{edgeWeight,arcs,calculateEulerChar}, normalsurface.cpp, 61-103,308-335.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.NormalSurface3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks
open import Regina.NormalCoordinates3
open import Regina.NormalMatching3
open import Regina.Integer using (Int; pos)
import Regina.Integer as Integer
import Regina.Embeddings as Embeddings
import Regina.ExactEdgeLinks3 as ExactEdges
import Regina.DualPresentation3 as Sequence

private
  variable
    encoding : NormalCoords
    tetrahedra : Nat

evaluateTerms : SurfaceVector encoding tetrahedra → List (CoordinateTerm3 tetrahedra) → Maybe Int
evaluateTerms currentSurface [] = just (pos zero)
evaluateTerms currentSurface (headTerm ∷ remaining)
  with discCoordinate currentSurface (term_tetrahedron headTerm) (term_disc_type headTerm) |
    evaluateTerms currentSurface remaining
... | just value | just tailValue = just (Integer.add
  (Integer.multiply (term_coefficient headTerm) (pos value)) tailValue)
... | nothing | _ = nothing
... | just _ | nothing = nothing

edgeTerms : NormalCoords → Embeddings.FaceEmbedding 3 tetrahedra →
  Maybe (List (CoordinateTerm3 tetrahedra))
edgeTerms {tetrahedra = tetrahedra} encodingValue currentEmbedding
  with from_image_list 4 (Embeddings.embeddingVertexTable currentEmbedding)
... | nothing = nothing
... | just vertexMapping with quadSeparating (image vertexMapping ExactEdges.vertexZero)
    (image vertexMapping ExactEdges.vertexOne)
... | nothing = nothing
... | just separatingType = just
  (coordinate_term_three simplexIndex (fin_to_nat (image vertexMapping ExactEdges.vertexZero)) (pos 1) ∷
   coordinate_term_three simplexIndex (fin_to_nat (image vertexMapping ExactEdges.vertexOne)) (pos 1) ∷
   quadTermsForEdge ++ octagonTerms)
  where
  simplexIndex = face_simplex (Embeddings.embedded_local_face currentEmbedding)
  quadTermsForEdge : List (CoordinateTerm3 tetrahedra)
  quadTermsForEdge = map (λ meetingType → coordinate_term_three simplexIndex
    (4 + fin_to_nat meetingType) (pos 1)) (quadMeeting separatingType)
  octagonTerms : List (CoordinateTerm3 tetrahedra)
  octagonTerms with storesOctagons encodingValue
  ... | false = []
  ... | true = map (λ octagonType → coordinate_term_three simplexIndex
      (7 + fin_to_nat octagonType) (pos 1)) (all_fin 3) ++
    (coordinate_term_three simplexIndex (7 + fin_to_nat separatingType) (pos 1) ∷ [])

edgeWeight : SurfaceVector encoding tetrahedra → FaceLinkClass 3 tetrahedra → Maybe Int
edgeWeight {encoding = encodingValue} currentSurface edgeClass
  with face_link_embeddings edgeClass
... | [] = nothing
... | firstEmbedding ∷ remaining with edgeTerms encodingValue firstEmbedding
... | nothing = nothing
... | just terms = evaluateTerms currentSurface terms

arcCount : SurfaceVector encoding tetrahedra → FaceLinkClass 3 tetrahedra → Fin 3 → Maybe Int
arcCount {encoding = encodingValue} currentSurface triangleClass arcType
  with face_link_embeddings triangleClass
... | [] = nothing
... | firstEmbedding ∷ remaining with arcTerms encodingValue (pos 1) firstEmbedding arcType
... | nothing = nothing
... | just terms = evaluateTerms currentSurface terms

discCount : SurfaceVector encoding tetrahedra → Int
discCount {encoding = encodingValue} {tetrahedra} currentSurface = Integer.sum
  (map (λ index → pos (lookup_vector (coordinates currentSurface) index))
    (all_fin (tetrahedra * coordinateBlock encodingValue)))

eulerCharacteristic : Triangulation 3 tetrahedra → SurfaceVector encoding tetrahedra → Maybe Int
eulerCharacteristic {encoding = encodingValue} currentTriangulation currentSurface
  with storesTriangles encodingValue
... | false = nothing
... | true with Sequence.sequence
    (map (edgeWeight currentSurface) (faceLinkClasses currentTriangulation 1)) |
    Sequence.sequence (fold_right (λ triangleClass remaining →
      map (arcCount currentSurface triangleClass) (all_fin 3) ++ remaining)
      [] (faceLinkClasses currentTriangulation 2))
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just vertexWeights | just arcWeights = just
  (Integer.add (Integer.subtract (Integer.sum vertexWeights) (Integer.sum arcWeights))
    (discCount currentSurface))

record AdmissibleSurface (systemValue : MatchingSystem encoding tetrahedra) : Set where
  constructor admissible_surface
  field
    admissible_vector : SurfaceVector encoding tetrahedra
    matching_checked : satisfiesMatching systemValue admissible_vector ≡ true
    admissibility_checked : enumerationAdmissible admissible_vector ≡ true
open AdmissibleSurface public

certifySurface : (systemValue : MatchingSystem encoding tetrahedra) →
  SurfaceVector encoding tetrahedra → Maybe (AdmissibleSurface systemValue)
certifySurface systemValue currentSurface
  with bool_dec_equal (satisfiesMatching systemValue currentSurface) true |
    bool_dec_equal (enumerationAdmissible currentSurface) true
... | yes matchingProof | yes admissibilityProof =
  just (admissible_surface currentSurface matchingProof admissibilityProof)
... | no _ | _ = nothing
... | yes _ | no _ = nothing
