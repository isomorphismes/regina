{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-09. License: ../../LICENSE.txt.

-- Input boundary for Regina's fromGluings constructor.
-- Derived from engine/triangulation/triangulation.h and regina-core.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.Input where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation

-- External tables use natural numbers and ordinary image lists. They need
-- not supply either a hand-written inverse or a proof of bijectivity.
record InputGluing : Set where
  constructor input_gluing
  field
    source_simplex_number : Nat
    source_facet_number : Nat
    destination_simplex_number : Nat
    vertex_images : List Nat
open InputGluing public

read_gluing : (dimension_value simplex_count : Nat) → InputGluing →
  Outcome (GluingSpec dimension_value simplex_count)
read_gluing dimension_value simplex_count entry
  with fin_from_nat simplex_count (source_simplex_number entry) |
       fin_from_nat simplex_count (destination_simplex_number entry)
... | nothing | _ = rejected invalid_simplex_number
... | just _ | nothing = rejected invalid_simplex_number
... | just source_index | just destination_index
  with fin_from_nat (suc dimension_value) (source_facet_number entry)
... | nothing = rejected invalid_facet_number
... | just local_facet with from_image_list (suc dimension_value) (vertex_images entry)
... | nothing = rejected invalid_vertex_permutation
... | just mapping = accepted (glue (facet source_index local_facet) destination_index mapping)

read_gluings : (dimension_value simplex_count : Nat) → List InputGluing →
  Outcome (List (GluingSpec dimension_value simplex_count))
read_gluings dimension_value simplex_count [] = accepted []
read_gluings dimension_value simplex_count (entry ∷ remaining)
  with read_gluing dimension_value simplex_count entry
... | rejected reason = rejected reason
... | accepted decoded with read_gluings dimension_value simplex_count remaining
... | rejected reason = rejected reason
... | accepted decoded_remaining = accepted (decoded ∷ decoded_remaining)

at_most : Nat → Nat → Bool
at_most zero bound = true
at_most (suc value) zero = false
at_most (suc value) (suc bound) = at_most value bound

-- Match supportedDim: default Regina supports 2..8; REGINA_HIGHDIM
-- extends the upper limit to 15. The pure finite core itself is generic.
supported_dimension : Bool → Nat → Bool
supported_dimension high_dimensions zero = false
supported_dimension high_dimensions (suc zero) = false
supported_dimension false (suc (suc remaining)) = at_most remaining 6
supported_dimension true (suc (suc remaining)) = at_most remaining 13

-- Decode and apply one entry at a time. Parsing the whole list first would
-- incorrectly let a later malformed entry hide an earlier illegal gluing.
apply_input_gluings : {dimension_value simplex_count : Nat} →
  Triangulation dimension_value simplex_count → List InputGluing →
  Outcome (Triangulation dimension_value simplex_count)
apply_input_gluings current [] = accepted current
apply_input_gluings {dimension_value} {simplex_count} current (entry ∷ remaining)
  with read_gluing dimension_value simplex_count entry
... | rejected reason = rejected reason
... | accepted decoded with join current
  (GluingSpec.source_facet decoded) (GluingSpec.target_simplex decoded)
  (GluingSpec.gluing_permutation decoded)
... | rejected reason = rejected reason
... | accepted completed = apply_input_gluings (resulting_triangulation completed) remaining

from_input_gluings : (high_dimensions : Bool) → (dimension_value simplex_count : Nat) →
  List InputGluing → Outcome (Triangulation dimension_value simplex_count)
from_input_gluings high_dimensions dimension_value simplex_count entries
  with supported_dimension high_dimensions dimension_value
... | false = rejected unsupported_dimension
... | true = apply_input_gluings (unpaired_simplices dimension_value simplex_count) entries
