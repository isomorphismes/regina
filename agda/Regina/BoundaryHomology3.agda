{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-18. License: ../../LICENSE.txt.
-- Triangulation<3>::homologyBdry(), engine/triangulation/dim3/homology.cpp.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.BoundaryHomology3 where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.AbelianGroup
import Regina.BoundaryClassification3 as Classification
import Regina.Validity3 as Validity

private
  variable
    simplex_count : Nat

directSum : AbelianGroup → AbelianGroup → AbelianGroup
directSum firstGroup secondGroup = abelian_group
  (free_rank firstGroup + free_rank secondGroup)
  (invariant_factors firstGroup ++ invariant_factors secondGroup)

homologyOfClosedSurface : Classification.ClosedSurfaceType → Maybe AbelianGroup
homologyOfClosedSurface (Classification.orientable_genus genusValue) =
  just (abelian_group (2 * genusValue) [])
homologyOfClosedSurface (Classification.nonorientable_genus zero) = nothing
homologyOfClosedSurface (Classification.nonorientable_genus (suc genusRemainder)) =
  just (abelian_group genusRemainder (2 ∷ []))
homologyOfClosedSurface Classification.unclassified_surface = nothing

combineSurfaceHomology : Maybe AbelianGroup → Maybe AbelianGroup →
  Maybe AbelianGroup
combineSurfaceHomology nothing remainingHomology = nothing
combineSurfaceHomology (just currentHomology) nothing = nothing
combineSurfaceHomology (just currentHomology) (just remainingHomology) =
  just (directSum currentHomology remainingHomology)

homologyOfBoundarySurfaces :
  List Classification.ClassifiedBoundarySurface → Maybe AbelianGroup
homologyOfBoundarySurfaces [] = just (abelian_group zero [])
homologyOfBoundarySurfaces (currentSurface ∷ remainingSurfaces) =
  combineSurfaceHomology
    (homologyOfClosedSurface
      (Classification.classified_surface_type currentSurface))
    (homologyOfBoundarySurfaces remainingSurfaces)

-- Regina computes this directly from the orientability and Euler
-- characteristic of each real or ideal boundary component.  The existing
-- classifier has already converted precisely those data into genus.
boundaryFirstHomology : Triangulation 3 simplex_count → Maybe AbelianGroup
boundaryFirstHomology currentTriangulation
  with Validity.threeDimensionalValidityValue currentTriangulation
... | false = nothing
... | true = homologyOfBoundarySurfaces
  (Classification.classifiedBoundarySurfaces currentTriangulation)
