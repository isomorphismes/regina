{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-13. License: ../../LICENSE.txt.
-- IsoSigData<1,dim>::fillFrom(), IsoSigPrintable::encode() and classical
-- TriangulationBase<dim>::isoSig(), detail/isosig-impl.h, 60-166,317-345,707-764.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.IsomorphismSignature where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton using (filter_list; concat_map; less_than)
open import Regina.SignatureEncoding
open import Agda.Builtin.Nat using (_-_)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (String; primStringFromList)
import Regina.Components as Components
import Regina.SubfaceIncidence3 as Lists
import Regina.DualPresentation3 as Sequence

private
  variable
    dimension tetrahedra : Nat

-- Every vertex permutation is checked as a bijection before use. This
-- reference enumeration replaces the source's packed permutation iterators.
permutation_tables : Nat → List Nat → List (List Nat)
permutation_tables zero remainingNumbers = [] ∷ []
permutation_tables (suc remainingPositions) availableNumbers = concat_map
  (λ firstNumber → map (λ tailNumbers → firstNumber ∷ tailNumbers)
    (permutation_tables remainingPositions
      (filter_list (λ candidateNumber → not (nat_equal candidateNumber firstNumber)) availableNumbers)))
  availableNumbers

all_permutations : (vertexCount : Nat) → Maybe (List (Permutation vertexCount))
all_permutations vertexCount = Sequence.sequence
  (map (from_image_list vertexCount)
    (permutation_tables vertexCount (map fin_to_nat (all_fin vertexCount))))

record CanonicalSimplex (dimension tetrahedra : Nat) : Set where
  constructor canonical_simplex
  field
    original_simplex : Fin tetrahedra
    original_to_canonical_vertices : Permutation (suc dimension)
open CanonicalSimplex public

record SignatureWalk (dimension tetrahedra : Nat) : Set where
  constructor signature_walk
  field
    discovered_simplices : List (CanonicalSimplex dimension tetrahedra)
    facet_trits : List Nat
    joined_simplex_numbers : List Nat
    joined_permutation_numbers : List Nat
    canonical_lock_masks : List Nat
open SignatureWalk public

find_canonical_number : List (CanonicalSimplex dimension tetrahedra) →
  Fin tetrahedra → Nat → Maybe Nat
find_canonical_number [] requestedSimplex nextNumber = nothing
find_canonical_number (headSimplex ∷ remainingSimplices) requestedSimplex nextNumber
  with fin_equal (original_simplex headSimplex) requestedSimplex
... | true = just nextNumber
... | false = find_canonical_number remainingSimplices requestedSimplex (suc nextNumber)

append_facet : Nat → SignatureWalk dimension tetrahedra → SignatureWalk dimension tetrahedra
append_facet facetType currentWalk = signature_walk (discovered_simplices currentWalk)
  (facet_trits currentWalk ++ (facetType ∷ [])) (joined_simplex_numbers currentWalk)
  (joined_permutation_numbers currentWalk) (canonical_lock_masks currentWalk)

visit_facet : Triangulation dimension tetrahedra → Nat → CanonicalSimplex dimension tetrahedra →
  Fin (suc dimension) → SignatureWalk dimension tetrahedra → Maybe (SignatureWalk dimension tetrahedra)
visit_facet currentTriangulation sourceNumber sourceSimplex canonicalFacet currentWalk
  with adjacency (raw_state currentTriangulation) (facet (original_simplex sourceSimplex)
    (preimage (original_to_canonical_vertices sourceSimplex) canonicalFacet))
... | nothing = just (append_facet 0 currentWalk)
... | just outward with find_canonical_number (discovered_simplices currentWalk)
    (adjacent_simplex outward) zero
... | nothing = just (signature_walk
    (discovered_simplices currentWalk ++ (canonical_simplex (adjacent_simplex outward)
      (compose (original_to_canonical_vertices sourceSimplex)
        (inverse (vertex_permutation outward))) ∷ []))
    (facet_trits currentWalk ++ (1 ∷ [])) (joined_simplex_numbers currentWalk)
    (joined_permutation_numbers currentWalk) (canonical_lock_masks currentWalk))
... | just destinationNumber with Lists.lookupList destinationNumber (discovered_simplices currentWalk)
... | nothing = nothing
... | just destinationSimplex with less_than destinationNumber sourceNumber or
    (nat_equal destinationNumber sourceNumber and less_than
      (fin_to_nat (image canonicalGluing canonicalFacet)) (fin_to_nat canonicalFacet))
  where
  canonicalGluing = compose (original_to_canonical_vertices destinationSimplex)
    (compose (vertex_permutation outward) (inverse (original_to_canonical_vertices sourceSimplex)))
... | true = just currentWalk
... | false = just (signature_walk (discovered_simplices currentWalk)
    (facet_trits currentWalk ++ (2 ∷ []))
    (joined_simplex_numbers currentWalk ++ (destinationNumber ∷ []))
    (joined_permutation_numbers currentWalk ++ (permutation_rank
      (image_table (compose (original_to_canonical_vertices destinationSimplex)
        (compose (vertex_permutation outward)
          (inverse (original_to_canonical_vertices sourceSimplex))))) ∷ []))
    (canonical_lock_masks currentWalk))

visit_facets : Triangulation dimension tetrahedra → Nat → CanonicalSimplex dimension tetrahedra →
  List (Fin (suc dimension)) → SignatureWalk dimension tetrahedra →
  Maybe (SignatureWalk dimension tetrahedra)
visit_facets currentTriangulation sourceNumber sourceSimplex [] currentWalk = just currentWalk
visit_facets currentTriangulation sourceNumber sourceSimplex (facetNumber ∷ remainingFacets) currentWalk
  with visit_facet currentTriangulation sourceNumber sourceSimplex facetNumber currentWalk
... | nothing = nothing
... | just nextWalk = visit_facets currentTriangulation sourceNumber sourceSimplex remainingFacets nextWalk

canonical_lock_mask : Triangulation dimension tetrahedra → CanonicalSimplex dimension tetrahedra → Nat
canonical_lock_mask {dimension = dimension} currentTriangulation currentSimplex =
  fold_right (λ facetNumber remainingMask → facetBit facetNumber + remainingMask) simplexBit
    (all_fin (suc dimension))
  where
  simplexBit : Nat
  simplexBit with simplex_is_locked (raw_state currentTriangulation) (original_simplex currentSimplex)
  ... | false = zero
  ... | true = power_of_two (suc dimension)
  facetBit : Fin (suc dimension) → Nat
  facetBit facetNumber with facet_is_locked (raw_state currentTriangulation)
    (facet (original_simplex currentSimplex)
      (preimage (original_to_canonical_vertices currentSimplex) facetNumber))
  ... | false = zero
  ... | true = power_of_two (fin_to_nat facetNumber)

visit_simplices : Nat → Triangulation dimension tetrahedra → Nat →
  SignatureWalk dimension tetrahedra → Maybe (SignatureWalk dimension tetrahedra)
visit_simplices zero currentTriangulation nextNumber currentWalk = just currentWalk
visit_simplices {dimension = dimension} (suc remainingSimplices) currentTriangulation nextNumber currentWalk
  with Lists.lookupList nextNumber (discovered_simplices currentWalk)
... | nothing = nothing
... | just sourceSimplex with visit_facets currentTriangulation nextNumber sourceSimplex
    (all_fin (suc dimension)) currentWalk
... | nothing = nothing
... | just nextWalk = visit_simplices remainingSimplices currentTriangulation (suc nextNumber)
    (signature_walk (discovered_simplices nextWalk) (facet_trits nextWalk)
      (joined_simplex_numbers nextWalk) (joined_permutation_numbers nextWalk)
      (canonical_lock_masks nextWalk ++ (canonical_lock_mask currentTriangulation sourceSimplex ∷ [])))

component_walk : Triangulation dimension tetrahedra → List (Fin tetrahedra) →
  Fin tetrahedra → Permutation (suc dimension) → Maybe (SignatureWalk dimension tetrahedra)
component_walk currentTriangulation componentSimplices rootSimplex rootVertices
  with visit_simplices (length componentSimplices) currentTriangulation zero
    (signature_walk (canonical_simplex rootSimplex (inverse rootVertices) ∷ []) [] [] [] [])
... | nothing = nothing
... | just completedWalk with
    nat_equal (length (discovered_simplices completedWalk)) (length componentSimplices) and
    all (λ sourceSimplex → Components.memberSimplex (original_simplex sourceSimplex) componentSimplices)
      (discovered_simplices completedWalk)
... | false = nothing
... | true = just completedWalk

encode_component : Bool → Nat → SignatureWalk dimension tetrahedra → Maybe (List Char)
encode_component {dimension = dimension} includeLocks componentSize completedWalk
  with encode_size componentSize | encode_trits (facet_trits completedWalk) |
    encode_integers (integer_width componentSize) (joined_simplex_numbers completedWalk) |
    encode_integers (integer_width (factorial (suc dimension) - 1))
      (joined_permutation_numbers completedWalk)
... | just sizeCharacters | just facetCharacters | just simplexCharacters | just permutationCharacters
  with includeLocks and any (λ maskNumber → not (nat_equal maskNumber zero))
    (canonical_lock_masks completedWalk)
... | false = just (sizeCharacters ++ facetCharacters ++ simplexCharacters ++ permutationCharacters)
... | true with encode_integers (integer_width (power_of_two (suc (suc dimension)) - 1))
    (canonical_lock_masks completedWalk)
... | nothing = nothing
... | just lockCharacters = just
    (sizeCharacters ++ facetCharacters ++ simplexCharacters ++ permutationCharacters ++
      ('.' ∷ lockCharacters))
encode_component includeLocks componentSize completedWalk | _ | _ | _ | _ = nothing

candidate_signature : Bool → Triangulation dimension tetrahedra → List (Fin tetrahedra) →
  Fin tetrahedra → Permutation (suc dimension) → Maybe (List Char)
candidate_signature includeLocks currentTriangulation componentSimplices rootSimplex rootVertices
  with component_walk currentTriangulation componentSimplices rootSimplex rootVertices
... | nothing = nothing
... | just completedWalk = encode_component includeLocks (length componentSimplices) completedWalk

component_signature : Bool → Triangulation dimension tetrahedra → List (Permutation (suc dimension)) →
  List (Fin tetrahedra) → Maybe (List Char)
component_signature includeLocks currentTriangulation vertexPermutations componentSimplices
  with Sequence.sequence (concat_map (λ rootSimplex → map
    (candidate_signature includeLocks currentTriangulation componentSimplices rootSimplex)
    vertexPermutations) componentSimplices)
... | nothing = nothing
... | just candidates = smallest_signature candidates

-- includeLocks=false is Regina's IsoSigPrintableLockFree choice. Components
-- are minimised separately and concatenated in ASCII lexicographic order.
classical_signature : Bool → Triangulation dimension tetrahedra → Maybe String
classical_signature {dimension = dimension} {tetrahedra = tetrahedra} includeLocks currentTriangulation
  with Components.simplexComponents currentTriangulation
... | [] = just "a"
... | componentSimplices with all_permutations (suc dimension)
... | nothing = nothing
... | just vertexPermutations with Sequence.sequence (map
    (component_signature includeLocks currentTriangulation vertexPermutations) componentSimplices)
... | nothing = nothing
... | just componentStrings = just (primStringFromList
    (concat_map (λ signatureCharacters → signatureCharacters) (sort_signatures componentStrings)))
