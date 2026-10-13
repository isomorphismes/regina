{-# OPTIONS --safe --without-K #-}

-- Agda reference implementation changes: 2026-10-12. License: ../../LICENSE.txt.
-- Fundamental normal surfaces: indecomposable admissible integral points
-- of the matching cone. This finite reference enumeration uses the sum of
-- primitive vertex rays as an exact coordinate bound; it does not port
-- Regina's optimized Hilbert-basis/Normaliz implementations.
-- Source specification: engine/surface/{enumerator.cpp,matching.cpp} at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.NormalFundamentals3 where

open import Regina.Foundation
open import Regina.Skeleton using (tabulate_vector)
open import Regina.Triangulation
open import Regina.NormalCoordinates3
open import Regina.NormalMatching3
open import Regina.NormalSurface3
open import Regina.NormalVertices3
import Regina.Integer as Integer
import Regina.ChainHomology as Lists

private
  variable
    encoding : NormalCoords
    tetrahedra size : Nat

allWithinBounds : Vector Nat size → List (Vector Nat size)
allWithinBounds empty_vector = empty_vector ∷ []
allWithinBounds (vector_cons headBound remainingBounds) = fold_right
  (λ value remaining → map (vector_cons (fin_to_nat value)) tailVectors ++ remaining)
  [] (all_fin (suc headBound))
  where
  tailVectors = allWithinBounds remainingBounds

sumNaturals : List Nat → Nat
sumNaturals = fold_right _+_ zero

rayBounds : (systemValue : MatchingSystem encoding tetrahedra) →
  List (AdmissibleSurface systemValue) → Vector Nat (tetrahedra * coordinateBlock encoding)
rayBounds {encoding} {tetrahedra} systemValue rays = tabulate_vector
  (tetrahedra * coordinateBlock encoding)
  (λ index → sumNaturals (map
    (λ ray → lookup_vector (coordinates (admissible_vector ray)) index) rays))

nonzero : SurfaceVector encoding tetrahedra → Bool
nonzero {encoding} {tetrahedra} surfaceValue = any
  (λ index → not (nat_equal (lookup_vector (coordinates surfaceValue) index) zero))
  (all_fin (tetrahedra * coordinateBlock encoding))

coordinatewiseBelow : SurfaceVector encoding tetrahedra → SurfaceVector encoding tetrahedra → Bool
coordinatewiseBelow {encoding} {tetrahedra} firstSurface secondSurface = all
  (λ index → not (Integer.natural_less
    (lookup_vector (coordinates secondSurface) index)
    (lookup_vector (coordinates firstSurface) index)))
  (all_fin (tetrahedra * coordinateBlock encoding))

vectorEqual : SurfaceVector encoding tetrahedra → SurfaceVector encoding tetrahedra → Bool
vectorEqual {encoding} {tetrahedra} firstSurface secondSurface = all
  (λ index → nat_equal (lookup_vector (coordinates firstSurface) index)
    (lookup_vector (coordinates secondSurface) index))
  (all_fin (tetrahedra * coordinateBlock encoding))

collectAdmissible : (systemValue : MatchingSystem encoding tetrahedra) →
  List (Vector Nat (tetrahedra * coordinateBlock encoding)) →
  List (AdmissibleSurface systemValue)
collectAdmissible systemValue [] = []
collectAdmissible {encoding} {tetrahedra} systemValue (head ∷ remaining)
  with nonzero {encoding = encoding} {tetrahedra = tetrahedra} (surface_vector head)
... | false = collectAdmissible systemValue remaining
... | true with certifySurface systemValue (surface_vector head)
... | nothing = collectAdmissible systemValue remaining
... | just result = result ∷ collectAdmissible systemValue remaining

-- If y is a proper nonzero admissible point below x, then x-y is also
-- integral, matching, nonzero and admissible: its support is contained
-- in x's support. Hence this comparison is the exact decomposition test.
indecomposable : (systemValue : MatchingSystem encoding tetrahedra) →
  List (AdmissibleSurface systemValue) → AdmissibleSurface systemValue → Bool
indecomposable systemValue allCandidates candidateValue = not (any
  (λ otherCandidate → coordinatewiseBelow
      (admissible_vector otherCandidate) (admissible_vector candidateValue) and
    not (vectorEqual (admissible_vector otherCandidate) (admissible_vector candidateValue)))
  allCandidates)

fundamentalsFromRays : (systemValue : MatchingSystem encoding tetrahedra) →
  List (AdmissibleSurface systemValue) → List (AdmissibleSurface systemValue)
fundamentalsFromRays systemValue rays = Lists.filter
  (indecomposable systemValue candidates) candidates
  where
  candidates = collectAdmissible systemValue (allWithinBounds (rayBounds systemValue rays))

enumerateFundamentalSystem : Nat → (systemValue : MatchingSystem encoding tetrahedra) →
  Maybe (List (AdmissibleSurface systemValue))
enumerateFundamentalSystem fuel systemValue with enumerateSystem fuel systemValue
... | nothing = nothing
... | just rays = just (fundamentalsFromRays systemValue rays)

record FundamentalSurfaces (encoding : NormalCoords) (tetrahedra : Nat) : Set where
  constructor fundamental_surfaces
  field
    fundamental_matching_system : MatchingSystem encoding tetrahedra
    fundamental_surface_list : List (AdmissibleSurface fundamental_matching_system)
open FundamentalSurfaces public

fundamentalSurfaces : Nat → (encodingValue : NormalCoords) → Triangulation 3 tetrahedra →
  Maybe (FundamentalSurfaces encodingValue tetrahedra)
fundamentalSurfaces fuel encodingValue currentTriangulation
  with makeMatchingEquations encodingValue currentTriangulation
... | nothing = nothing
... | just systemValue with enumerateFundamentalSystem fuel systemValue
... | nothing = nothing
... | just surfaceList = just (fundamental_surfaces systemValue surfaceList)
