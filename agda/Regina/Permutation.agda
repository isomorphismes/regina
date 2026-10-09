{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-09. License: ../../LICENSE.txt.

-- A translation of Regina's finite permutation semantics.
-- Source: engine/maths/perm.h at e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton, for the source being translated.
-- Distributed under GPL-2.0-or-later, with Regina's online distribution
-- exception. See ../../LICENSE.txt for the full terms and acknowledgements.

module Regina.Permutation where

open import Regina.Foundation

-- Store both directions, with the two laws that make them a bijection.
-- Regina's packed integers and specialised lookup tables are deliberately
-- absent: this first translation preserves their mathematical behaviour.
record Permutation (number_of_vertices : Nat) : Set where
  constructor permutation
  field
    image : Fin number_of_vertices → Fin number_of_vertices
    preimage : Fin number_of_vertices → Fin number_of_vertices
    preimage_image : (vertex : Fin number_of_vertices) →
                     preimage (image vertex) ≡ vertex
    image_preimage : (vertex : Fin number_of_vertices) →
                     image (preimage vertex) ≡ vertex

open Permutation public

-- Regina Perm<n>() constructs the identity permutation.
identity : {number_of_vertices : Nat} → Permutation number_of_vertices
identity = permutation (λ vertex → vertex) (λ vertex → vertex)
                       (λ vertex → refl) (λ vertex → refl)

-- Regina Perm<n>::inverse(): each image becomes its corresponding preimage.
inverse : {number_of_vertices : Nat} →
          Permutation number_of_vertices → Permutation number_of_vertices
inverse original = permutation
  (preimage original) (image original)
  (image_preimage original) (preimage_image original)

-- Regina operator*: (left * right)[vertex] = left[right[vertex]].
-- Thus right acts first; reversing this order changes facet gluings.
compose : {number_of_vertices : Nat} →
          Permutation number_of_vertices → Permutation number_of_vertices →
          Permutation number_of_vertices
compose left right = permutation
  (λ vertex → image left (image right vertex))
  (λ vertex → preimage right (preimage left vertex))
  (λ vertex → trans
    (cong (preimage right) (preimage_image left (image right vertex)))
    (preimage_image right vertex))
  (λ vertex → trans
    (cong (image left) (image_preimage right (preimage left vertex)))
    (image_preimage left vertex))

-- Regina p.conjugate(q) returns q * p * q.inverse().
conjugate : {number_of_vertices : Nat} →
            Permutation number_of_vertices → Permutation number_of_vertices →
            Permutation number_of_vertices
conjugate original relabelling =
  compose relabelling (compose original (inverse relabelling))

-- Compare permutations by their action on vertices. Equality of their proof
-- fields is neither required nor assumed; no function extensionality is used.
SameImages : {number_of_vertices : Nat} →
             Permutation number_of_vertices → Permutation number_of_vertices → Set
SameImages {number_of_vertices} left right =
  (vertex : Fin number_of_vertices) → image left vertex ≡ image right vertex

permutation_dec_equal : {number_of_vertices : Nat} →
                       (left right : Permutation number_of_vertices) →
                       Dec (SameImages left right)
permutation_dec_equal left right = universal_fin_dec
  (λ vertex → fin_dec_equal (image left vertex) (image right vertex))

permutation_equal : {number_of_vertices : Nat} →
                    Permutation number_of_vertices →
                    Permutation number_of_vertices → Bool
permutation_equal left right = decision_bool (permutation_dec_equal left right)

-- Unlike Regina's unchecked array constructors, this entry point checks
-- every round trip before constructing a permutation. It also handles
-- Fin zero and Fin one, which lie outside Regina's Perm<n> template range.
make_permutation : {number_of_vertices : Nat} →
                   (forward backward : Fin number_of_vertices → Fin number_of_vertices) →
                   Maybe (Permutation number_of_vertices)
make_permutation forward backward
  with universal_fin_dec
         (λ vertex → fin_dec_equal (backward (forward vertex)) vertex) |
       universal_fin_dec
         (λ vertex → fin_dec_equal (forward (backward vertex)) vertex)
... | yes backward_forward | yes forward_backward =
  just (permutation forward backward backward_forward forward_backward)
... | no _ | _ = nothing
... | yes _ | no _ = nothing

-- Search the finite domain for a preimage. If none exists, the fallback is
-- only a candidate: make_permutation still checks both laws and rejects it.
-- No absent preimage can turn into a certified permutation by this fallback.
candidate_preimage : {number_of_vertices : Nat} →
                     (Fin number_of_vertices → Fin number_of_vertices) →
                     Fin number_of_vertices → Fin number_of_vertices
candidate_preimage {number_of_vertices} forward target
  with find (λ source → fin_equal (forward source) target)
            (all_fin number_of_vertices)
... | just source = source
... | nothing = target

-- Regina Perm<n>(image array) supplies only the forward images. Derive the
-- inverse by finite search, then validate it. These exhaustive searches
-- preserve the semantics without Regina's packed integer optimisations.
from_image_function : {number_of_vertices : Nat} →
                      (Fin number_of_vertices → Fin number_of_vertices) →
                      Maybe (Permutation number_of_vertices)
from_image_function forward = make_permutation forward (candidate_preimage forward)

from_image_vector : {number_of_vertices : Nat} →
                    Vector (Fin number_of_vertices) number_of_vertices →
                    Maybe (Permutation number_of_vertices)
from_image_vector table = from_image_function (lookup_vector table)

private
  read_image_vector : (number_of_vertices number_of_entries : Nat) → List Nat →
                      Maybe (Vector (Fin number_of_vertices) number_of_entries)
  read_image_vector number_of_vertices zero [] = just empty_vector
  read_image_vector number_of_vertices zero (_ ∷ _) = nothing
  read_image_vector number_of_vertices (suc number_of_entries) [] = nothing
  read_image_vector number_of_vertices (suc number_of_entries) (head ∷ tail)
    with fin_from_nat number_of_vertices head |
         read_image_vector number_of_vertices number_of_entries tail
  ... | just bounded_head | just bounded_tail =
    just (vector_cons bounded_head bounded_tail)
  ... | nothing | _ = nothing
  ... | just _ | nothing = nothing

-- External tables must have exactly the requested degree, contain only
-- in-range images, and describe a bijection. Every failure returns nothing.
from_image_list : (number_of_vertices : Nat) →
                  List Nat → Maybe (Permutation number_of_vertices)
from_image_list number_of_vertices table
  with read_image_vector number_of_vertices number_of_vertices table
... | just bounded_table = from_image_vector bounded_table
... | nothing = nothing

-- Two source vertices with the same image are the same vertex: apply the
-- inverse to their common image and use the stored round-trip laws.
image_injective : {number_of_vertices : Nat}
                  (relabel : Permutation number_of_vertices)
                  {first second : Fin number_of_vertices} →
                  image relabel first ≡ image relabel second → first ≡ second
image_injective relabel {first} {second} equal_images =
  trans (sym (preimage_image relabel first))
    (trans (cong (preimage relabel) equal_images)
           (preimage_image relabel second))

preimage_injective : {number_of_vertices : Nat}
                     (relabel : Permutation number_of_vertices)
                     {first second : Fin number_of_vertices} →
                     preimage relabel first ≡ preimage relabel second → first ≡ second
preimage_injective relabel = image_injective (inverse relabel)

compose_associative : {number_of_vertices : Nat}
                      (first second third : Permutation number_of_vertices) →
                      SameImages (compose (compose first second) third)
                                 (compose first (compose second third))
compose_associative first second third vertex = refl

identity_left : {number_of_vertices : Nat}
                (original : Permutation number_of_vertices) →
                SameImages (compose identity original) original
identity_left original vertex = refl

identity_right : {number_of_vertices : Nat}
                 (original : Permutation number_of_vertices) →
                 SameImages (compose original identity) original
identity_right original vertex = refl

inverse_left : {number_of_vertices : Nat}
               (original : Permutation number_of_vertices) →
               SameImages (compose (inverse original) original) identity
inverse_left original = preimage_image original

inverse_right : {number_of_vertices : Nat}
                (original : Permutation number_of_vertices) →
                SameImages (compose original (inverse original)) identity
inverse_right original = image_preimage original

inverse_involutive : {number_of_vertices : Nat}
                     (original : Permutation number_of_vertices) →
                     SameImages (inverse (inverse original)) original
inverse_involutive original vertex = refl

image_table : {number_of_vertices : Nat} →
              Permutation number_of_vertices → List Nat
image_table {number_of_vertices} original =
  map (λ vertex → fin_to_nat (image original vertex))
      (all_fin number_of_vertices)
