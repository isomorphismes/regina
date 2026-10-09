{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-09. License: ../../LICENSE.txt.

-- Regina example constructions, translated from original C++ image tables.
-- Sources at e3a5c7c0e0581706d9e5531b750160b322489950:
-- engine/triangulation/detail/example.h and engine/triangulation/example3.cpp.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.Examples where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Input

-- ExampleBase<dimension>::ball: one simplex, all facets unpaired.
ball : (dimension_value : Nat) → Triangulation dimension_value 1
ball dimension_value = unpaired_simplices dimension_value 1

-- ExampleBase<dimension>::sphere: identify the whole boundaries of two
-- simplices by identity. The name records the source construction; this
-- module does not implement or prove sphere recognition.
sphere : (dimension_value : Nat) → Outcome (Triangulation dimension_value 2)
sphere dimension_value = from_gluings dimension_value 2
  (map (λ local_facet → glue (facet fzero local_facet) (fsuc fzero) identity)
    (all_fin (suc dimension_value)))

-- ExampleBase<3>::ballBundle. The map [3,0,1,2] is NOT its own inverse.
-- Distinct facets 0 and 3 of one tetrahedron are paired.
three_dimensional_ball_bundle : Outcome (Triangulation 3 1)
three_dimensional_ball_bundle = from_input_gluings false 3 1
  (input_gluing 0 0 0 (3 ∷ 0 ∷ 1 ∷ 2 ∷ []) ∷ [])

-- ExampleBase<4>::ballBundle takes the orientable double cover: two
-- pentachora, with facet 0 of each joined to facet 4 of the other.
four_dimensional_ball_bundle : Outcome (Triangulation 4 2)
four_dimensional_ball_bundle = from_input_gluings false 4 2
  (input_gluing 0 0 1 (4 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ∷
   input_gluing 1 0 0 (4 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ∷ [])

-- Example<3>::figureEight. Regina attributes these four gluings to
-- Richard Rannard's PhD thesis, chapter 8. Thank you, Richard Rannard.
-- All facets are paired, yet this is an ideal knot-complement example.
-- Zero unpaired facets therefore must not be read as 'closed manifold'.
figure_eight_knot_complement : Outcome (Triangulation 3 2)
figure_eight_knot_complement = from_input_gluings false 3 2
  (input_gluing 0 0 1 (1 ∷ 3 ∷ 0 ∷ 2 ∷ []) ∷
   input_gluing 0 1 1 (2 ∷ 0 ∷ 3 ∷ 1 ∷ []) ∷
   input_gluing 0 2 1 (0 ∷ 3 ∷ 2 ∷ 1 ∷ []) ∷
   input_gluing 0 3 1 (2 ∷ 1 ∷ 0 ∷ 3 ∷ []) ∷ [])
