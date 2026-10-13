{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- Normal coordinate encodings, quadSeparating/quadMeeting, embedded()
-- and locallyCompatible(), engine/surface/{normalcoords.h,normalsurface.h,normalsurface.cpp}.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.NormalCoordinates3 where

open import Regina.Foundation
open import Regina.Skeleton using (count_matching)
import Regina.Integer as Integer

data NormalCoords : Set where
  standard almost_normal quadrilateral quadrilateral_octagon : NormalCoords

coordinateBlock : NormalCoords → Nat
coordinateBlock standard = 7
coordinateBlock almost_normal = 10
coordinateBlock quadrilateral = 3
coordinateBlock quadrilateral_octagon = 6

storesTriangles : NormalCoords → Bool
storesTriangles standard = true
storesTriangles almost_normal = true
storesTriangles quadrilateral = false
storesTriangles quadrilateral_octagon = false

storesOctagons : NormalCoords → Bool
storesOctagons standard = false
storesOctagons almost_normal = true
storesOctagons quadrilateral = false
storesOctagons quadrilateral_octagon = true

quadOffset : NormalCoords → Nat
quadOffset standard = 4
quadOffset almost_normal = 4
quadOffset quadrilateral = zero
quadOffset quadrilateral_octagon = zero

octagonOffset : NormalCoords → Nat
octagonOffset encoding = quadOffset encoding + 3

quadSeparating : Fin 4 → Fin 4 → Maybe (Fin 3)
quadSeparating fzero fzero = nothing
quadSeparating fzero (fsuc fzero) = just fzero
quadSeparating fzero (fsuc (fsuc fzero)) = just (fsuc fzero)
quadSeparating fzero (fsuc (fsuc (fsuc fzero))) = just (fsuc (fsuc fzero))
quadSeparating (fsuc fzero) fzero = just fzero
quadSeparating (fsuc fzero) (fsuc fzero) = nothing
quadSeparating (fsuc fzero) (fsuc (fsuc fzero)) = just (fsuc (fsuc fzero))
quadSeparating (fsuc fzero) (fsuc (fsuc (fsuc fzero))) = just (fsuc fzero)
quadSeparating (fsuc (fsuc fzero)) fzero = just (fsuc fzero)
quadSeparating (fsuc (fsuc fzero)) (fsuc fzero) = just (fsuc (fsuc fzero))
quadSeparating (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) = nothing
quadSeparating (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) = just fzero
quadSeparating (fsuc (fsuc (fsuc fzero))) fzero = just (fsuc (fsuc fzero))
quadSeparating (fsuc (fsuc (fsuc fzero))) (fsuc fzero) = just (fsuc fzero)
quadSeparating (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero)) = just fzero
quadSeparating (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc fzero))) = nothing

quadMeeting : Fin 3 → List (Fin 3)
quadMeeting fzero = fsuc fzero ∷ fsuc (fsuc fzero) ∷ []
quadMeeting (fsuc fzero) = fzero ∷ fsuc (fsuc fzero) ∷ []
quadMeeting (fsuc (fsuc fzero)) = fzero ∷ fsuc fzero ∷ []

record SurfaceVector (encoding : NormalCoords) (tetrahedra : Nat) : Set where
  constructor surface_vector
  field
    coordinates : Vector Nat (tetrahedra * coordinateBlock encoding)
open SurfaceVector public

readVector : (size : Nat) → List Nat → Maybe (Vector Nat size)
readVector zero [] = just empty_vector
readVector zero (_ ∷ _) = nothing
readVector (suc remaining) [] = nothing
readVector (suc remaining) (head ∷ tail) with readVector remaining tail
... | nothing = nothing
... | just values = just (vector_cons head values)

readSurface : (encoding : NormalCoords) (tetrahedra : Nat) → List Nat →
  Maybe (SurfaceVector encoding tetrahedra)
readSurface encoding tetrahedra values
  with readVector (tetrahedra * coordinateBlock encoding) values
... | nothing = nothing
... | just vectorValue = just (surface_vector vectorValue)

coordinateAt : {encoding : NormalCoords} {tetrahedra : Nat} →
  SurfaceVector encoding tetrahedra → Nat → Maybe Nat
coordinateAt {encoding} {tetrahedra} currentSurface index
  with fin_from_nat (tetrahedra * coordinateBlock encoding) index
... | nothing = nothing
... | just boundedIndex = just (lookup_vector (coordinates currentSurface) boundedIndex)

discCoordinate : {encoding : NormalCoords} {tetrahedra : Nat} →
  SurfaceVector encoding tetrahedra → Fin tetrahedra → Nat → Maybe Nat
discCoordinate {encoding} currentSurface tetrahedronIndex discType = coordinateAt
  currentSurface (fin_to_nat tetrahedronIndex * coordinateBlock encoding + discType)

positiveCoordinate : Maybe Nat → Bool
positiveCoordinate nothing = false
positiveCoordinate (just zero) = false
positiveCoordinate (just (suc value)) = true

quadOctDiscTypes : NormalCoords → List Nat
quadOctDiscTypes encoding with storesOctagons encoding
... | false = map (λ index → quadOffset encoding + fin_to_nat index) (all_fin 3)
... | true = map (λ index → quadOffset encoding + fin_to_nat index) (all_fin 3) ++
  map (λ index → octagonOffset encoding + fin_to_nat index) (all_fin 3)

embedded : {encoding : NormalCoords} {tetrahedra : Nat} →
  SurfaceVector encoding tetrahedra → Bool
embedded {encoding} {tetrahedra} currentSurface = all
  (λ tetrahedronIndex → not (Integer.natural_less 1
    (count_matching (λ discType → positiveCoordinate
      (discCoordinate currentSurface tetrahedronIndex discType))
      (quadOctDiscTypes encoding)))) (all_fin tetrahedra)

locallyCompatible : {encoding : NormalCoords} {tetrahedra : Nat} →
  SurfaceVector encoding tetrahedra → SurfaceVector encoding tetrahedra → Bool
locallyCompatible {encoding} {tetrahedra} firstSurface secondSurface = all
  (λ tetrahedronIndex → not (Integer.natural_less 1
    (count_matching (λ discType → positiveCoordinate
      (discCoordinate firstSurface tetrahedronIndex discType) or positiveCoordinate
      (discCoordinate secondSurface tetrahedronIndex discType))
      (quadOctDiscTypes encoding)))) (all_fin tetrahedra)

-- Enumeration constraints additionally allow at most one octagon *type*
-- globally. embedded() alone has only the local quad/octagon constraint.
octagonTypes : {encoding : NormalCoords} {tetrahedra : Nat} →
  SurfaceVector encoding tetrahedra → List Bool
octagonTypes {encoding} {tetrahedra} currentSurface with storesOctagons encoding
... | false = []
... | true = fold_right (λ tetrahedronIndex remaining → map
  (λ octagonType → positiveCoordinate (discCoordinate currentSurface tetrahedronIndex
    (octagonOffset encoding + fin_to_nat octagonType))) (all_fin 3) ++ remaining)
  [] (all_fin tetrahedra)

enumerationAdmissible : {encoding : NormalCoords} {tetrahedra : Nat} →
  SurfaceVector encoding tetrahedra → Bool
enumerationAdmissible currentSurface = embedded currentSurface and
  not (Integer.natural_less 1 (count_matching (λ value → value) (octagonTypes currentSurface)))
