{-# OPTIONS --safe --without-K #-}

-- Agda reference implementation changes: 2026-10-12. License: ../../LICENSE.txt.
-- Mathematical output of Regina's vertex normal-surface enumeration:
-- primitive admissible extreme rays of {x ≥ 0 : matching_matrix x = 0}.
-- Exhaustive support enumeration and certified Smith kernels implement this
-- specification; this is not a translation of Regina's optimized DD engine.
-- Source specification: engine/surface/{enumerator.cpp,matching.cpp} at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.NormalVertices3 where

open import Regina.Foundation
open import Regina.Skeleton using (tabulate_vector)
open import Regina.Triangulation
open import Regina.IntegerMatrix
open import Regina.Integer using (Int; pos; negsuc)
open import Regina.SmithNormalForm
open import Regina.NormalCoordinates3
open import Regina.NormalMatching3
open import Regina.NormalSurface3
import Regina.Integer as Integer
import Regina.ChainHomology as Lists
import Regina.DualPresentation3 as Sequence

private
  variable
    encoding : NormalCoords
    tetrahedra : Nat

subsets : {element : Set} → List element → List (List element)
subsets [] = [] ∷ []
subsets (head ∷ remaining) = tailSubsets ++ map (λ values → head ∷ values) tailSubsets
  where
  tailSubsets = subsets remaining

indexMember : {size : Nat} → Fin size → List (Fin size) → Bool
indexMember wantedIndex = any (fin_equal wantedIndex)

indicator : (support : List (Fin (tetrahedra * coordinateBlock encoding))) →
  SurfaceVector encoding tetrahedra
indicator {tetrahedra = tetrahedra} {encoding = encoding} support = surface_vector
  (tabulate_vector (tetrahedra * coordinateBlock encoding) indicatorValue)
  where
  indicatorValue : Fin (tetrahedra * coordinateBlock encoding) → Nat
  indicatorValue index with indexMember index support
  ... | true = 1
  ... | false = zero

supportMatrix : (systemValue : MatchingSystem encoding tetrahedra) →
  (support : List (Fin (tetrahedra * coordinateBlock encoding))) →
  Matrix (matching_row_count systemValue) (length support)
supportMatrix systemValue support = tabulate (matching_row_count systemValue) (length support)
  (λ currentRow currentColumn → entry (matching_matrix systemValue) currentRow
    (Lists.lookup support currentColumn))

positiveEntry : Int → Bool
positiveEntry (pos zero) = false
positiveEntry (pos (suc magnitude)) = true
positiveEntry (negsuc magnitude) = false

negativeEntry : Int → Bool
negativeEntry (negsuc magnitude) = true
negativeEntry _ = false

supportPosition : {size : Nat} → (support : List (Fin size)) → Fin size →
  Maybe (Fin (length support))
supportPosition [] wantedIndex = nothing
supportPosition (head ∷ remaining) wantedIndex with fin_equal head wantedIndex
... | true = just fzero
... | false with supportPosition remaining wantedIndex
... | nothing = nothing
... | just positionValue = just (fsuc positionValue)

expandKernel : (support : List (Fin (tetrahedra * coordinateBlock encoding))) →
  (Fin (length support) → Int) → SurfaceVector encoding tetrahedra
expandKernel {tetrahedra = tetrahedra} {encoding = encoding} support kernelValue = surface_vector
  (tabulate_vector (tetrahedra * coordinateBlock encoding) valueAt)
  where
  valueAt : Fin (tetrahedra * coordinateBlock encoding) → Nat
  valueAt index with supportPosition support index
  ... | nothing = zero
  ... | just positionValue = Integer.absolute (kernelValue positionValue)

-- A ray with exactly this support is extreme precisely when its supported
-- kernel has dimension one. A column of an integral invertible basis is
-- primitive, so no approximate arithmetic or gcd tolerance is used.
rayFromKernel : (systemValue : MatchingSystem encoding tetrahedra) →
  (support : List (Fin (tetrahedra * coordinateBlock encoding))) →
  (Fin (length support) → Int) → Maybe (Maybe (AdmissibleSurface systemValue))
rayFromKernel systemValue support kernelValue
  with all (λ index → positiveEntry (kernelValue index)) (all_fin (length support)) or
    all (λ index → negativeEntry (kernelValue index)) (all_fin (length support))
... | false = just nothing
... | true with certifySurface systemValue (expandKernel support kernelValue)
... | nothing = nothing
... | just admissibleResult = just (just admissibleResult)

rayFromSmith : (systemValue : MatchingSystem encoding tetrahedra) →
  (support : List (Fin (tetrahedra * coordinateBlock encoding))) →
  SmithCertificate (supportMatrix systemValue support) →
  Maybe (Maybe (AdmissibleSurface systemValue))
rayFromSmith systemValue support smithResult
  with nat_equal (suc (length (smithDiagonal (reduced_matrix (smith_state smithResult)))))
    (length support)
... | false = just nothing
... | true with fin_from_nat (length support)
    (length (smithDiagonal (reduced_matrix (smith_state smithResult))))
... | nothing = nothing
... | just kernelColumn = rayFromKernel systemValue support
  (λ index → entry (right_basis (smith_state smithResult)) index kernelColumn)

rayForSupport : Nat → (systemValue : MatchingSystem encoding tetrahedra) →
  (support : List (Fin (tetrahedra * coordinateBlock encoding))) →
  Maybe (Maybe (AdmissibleSurface systemValue))
rayForSupport fuel systemValue [] = just nothing
rayForSupport {encoding = encoding} {tetrahedra = tetrahedra} fuel systemValue support@(_ ∷ _)
  with enumerationAdmissible (indicator {tetrahedra = tetrahedra} {encoding = encoding} support)
... | false = just nothing
... | true with smithNormalForm fuel (supportMatrix systemValue support)
... | nothing = nothing
... | just smithResult = rayFromSmith systemValue support smithResult

collectRays : {element : Set} → List (Maybe element) → List element
collectRays [] = []
collectRays (nothing ∷ remaining) = collectRays remaining
collectRays (just head ∷ remaining) = head ∷ collectRays remaining

enumerateSystem : Nat → (systemValue : MatchingSystem encoding tetrahedra) →
  Maybe (List (AdmissibleSurface systemValue))
enumerateSystem {encoding} {tetrahedra} fuel systemValue with Sequence.sequence
  (map (rayForSupport fuel systemValue)
    (subsets (all_fin (tetrahedra * coordinateBlock encoding))))
... | nothing = nothing
... | just candidates = just (collectRays candidates)

record VertexSurfaces (encoding : NormalCoords) (tetrahedra : Nat) : Set where
  constructor vertex_surfaces
  field
    vertex_matching_system : MatchingSystem encoding tetrahedra
    vertex_surface_list : List (AdmissibleSurface vertex_matching_system)
open VertexSurfaces public

vertexSurfaces : Nat → (encodingValue : NormalCoords) → Triangulation 3 tetrahedra →
  Maybe (VertexSurfaces encodingValue tetrahedra)
vertexSurfaces fuel encodingValue currentTriangulation
  with makeMatchingEquations encodingValue currentTriangulation
... | nothing = nothing
... | just systemValue with enumerateSystem fuel systemValue
... | nothing = nothing
... | just surfaceList = just (vertex_surfaces systemValue surfaceList)
