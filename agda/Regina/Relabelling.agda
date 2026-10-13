{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-13. License: ../../LICENSE.txt.
-- Isomorphism<dim>::operator()(Triangulation), engine/triangulation/isomorphism.h.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.Relabelling where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation

private
  variable
    dimension simplexCount : Nat

record Relabelling (dimension simplexCount : Nat) : Set where
  constructor relabelling
  field
    simplex_mapping : Permutation simplexCount
    vertex_mapping : Fin simplexCount → Permutation (suc dimension)
open Relabelling public

original_facet : Relabelling dimension simplexCount → Facet dimension simplexCount →
  Facet dimension simplexCount
original_facet labelMaps newFacet = facet originalSimplex
  (preimage (vertex_mapping labelMaps originalSimplex) (opposite_vertex newFacet))
  where
  originalSimplex = preimage (simplex_mapping labelMaps) (simplex_number newFacet)

relabelled_adjacency : Triangulation dimension simplexCount → Relabelling dimension simplexCount →
  Facet dimension simplexCount → Maybe (Gluing dimension simplexCount)
relabelled_adjacency currentTriangulation labelMaps newFacet
  with original_facet labelMaps newFacet
... | oldFacet with adjacency (raw_state currentTriangulation) oldFacet
... | nothing = nothing
... | just outward = just (gluing
    (image (simplex_mapping labelMaps) (adjacent_simplex outward))
    (compose (vertex_mapping labelMaps (adjacent_simplex outward))
      (compose (vertex_permutation outward)
        (inverse (vertex_mapping labelMaps (simplex_number oldFacet))))))

relabel_triangulation : Triangulation dimension simplexCount → Relabelling dimension simplexCount →
  Outcome (Triangulation dimension simplexCount)
relabel_triangulation currentTriangulation labelMaps = certify (raw_triangulation
  (relabelled_adjacency currentTriangulation labelMaps)
  (λ newFacet → facet_is_locked (raw_state currentTriangulation) (original_facet labelMaps newFacet))
  (λ newSimplex → simplex_is_locked (raw_state currentTriangulation)
    (preimage (simplex_mapping labelMaps) newSimplex)))

inverse_relabelling : Relabelling dimension simplexCount → Relabelling dimension simplexCount
inverse_relabelling labelMaps = relabelling (inverse (simplex_mapping labelMaps))
  (λ newSimplex → inverse (vertex_mapping labelMaps
    (preimage (simplex_mapping labelMaps) newSimplex)))

compose_relabellings : Relabelling dimension simplexCount → Relabelling dimension simplexCount →
  Relabelling dimension simplexCount
compose_relabellings outerMaps innerMaps = relabelling
  (compose (simplex_mapping outerMaps) (simplex_mapping innerMaps))
  (λ originalSimplex → compose
    (vertex_mapping outerMaps (image (simplex_mapping innerMaps) originalSimplex))
    (vertex_mapping innerMaps originalSimplex))
