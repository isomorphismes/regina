{-# OPTIONS --safe --without-K #-}
module Regina.IsomorphismSignatureTests where

open import Regina.Foundation
open import Agda.Builtin.Nat using (_-_)
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.SignatureEncoding
open import Regina.IsomorphismSignature
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Char using (Char)
import Regina.Relabelling as Labels
import Regina.PachnerMoves3 as Moves

private
  maybe_count : {element : Set} → Maybe (List element) → Maybe Nat
  maybe_count nothing = nothing
  maybe_count (just entries) = just (length entries)

  signature_outcome : {dimension simplexCount : Nat} → Outcome (Triangulation dimension simplexCount) →
    Outcome (Maybe String)
  signature_outcome = map_outcome (classical_signature true)

  signature_relabelled : {simplexCount : Nat} → Triangulation 3 simplexCount →
    Permutation simplexCount → Permutation 4 → Outcome (Maybe String)
  signature_relabelled currentTriangulation simplexMap vertexMap = signature_outcome
    (Labels.relabel_triangulation currentTriangulation (Labels.relabelling simplexMap (λ _ → vertexMap)))

  facet_locked_ball : Outcome (Triangulation 3 1)
  facet_locked_ball = map_outcome resulting_triangulation (lock_facet (ball 3) (facet fzero fzero))

  simplex_locked_ball : Outcome (Triangulation 3 1)
  simplex_locked_ball = map_outcome resulting_triangulation (lock_simplex (ball 3) fzero)

  figure_eight_relabelled : Triangulation 3 2 → Outcome (Maybe String)
  figure_eight_relabelled currentTriangulation with from_image_list 2 (1 ∷ 0 ∷ []) |
    from_image_list 4 (3 ∷ 0 ∷ 1 ∷ 2 ∷ []) | from_image_list 4 (1 ∷ 0 ∷ 3 ∷ 2 ∷ [])
  ... | just simplexMap | just firstVertexMap | just secondVertexMap = signature_outcome
      (Labels.relabel_triangulation currentTriangulation (Labels.relabelling simplexMap
        (λ simplexIndex → vertexMap simplexIndex)))
    where
    vertexMap : Fin 2 → Permutation 4
    vertexMap fzero = firstVertexMap
    vertexMap (fsuc fzero) = secondVertexMap
  ... | _ | _ | _ = rejected invalid_vertex_permutation

  sphere_locked_internal_face : Triangulation 3 2 → Outcome (Maybe String)
  sphere_locked_internal_face currentTriangulation = signature_outcome
    (map_outcome resulting_triangulation (lock_facet currentTriangulation (facet fzero fzero)))

empty_triangulation_signature : classical_signature true (unpaired_simplices 3 0) ≡ just "a"
empty_triangulation_signature = refl

ball_signature : classical_signature true (ball 3) ≡ just "baa"
ball_signature = refl

triangle_ball_signature : classical_signature true (ball 2) ≡ just "ba"
triangle_ball_signature = refl

three_sphere_signature : signature_outcome (sphere 3) ≡ accepted (just "cPcbbbaaa")
three_sphere_signature = refl

two_sphere_signature : signature_outcome (sphere 2) ≡ accepted (just "cPbbaa")
two_sphere_signature = refl

-- Perm<5> has 120 elements, so every permutation index takes two characters.
four_sphere_signature : signature_outcome (sphere 4) ≡ accepted (just "cPkbbbbaaaaaaaa")
four_sphere_signature = refl

solid_torus_signature : signature_outcome three_dimensional_ball_bundle ≡ accepted (just "bGaj")
solid_torus_signature = refl

figure_eight_signature_matches_the_upstream_oracle :
  signature_outcome figure_eight_knot_complement ≡ accepted (just "cPcbbbiht")
figure_eight_signature_matches_the_upstream_oracle = refl

disconnected_components_are_independently_encoded :
  classical_signature true (unpaired_simplices 3 2) ≡ just "baabaa"
disconnected_components_are_independently_encoded = refl

simplex_lock_changes_signature : signature_outcome simplex_locked_ball ≡ accepted (just "baa.q")
simplex_lock_changes_signature = refl

facet_lock_is_canonically_relabelled : signature_outcome facet_locked_ball ≡ accepted (just "baa.b")
facet_lock_is_canonically_relabelled = refl

lock_free_encoding_omits_facet_locks : map_outcome (classical_signature false) facet_locked_ball ≡
  accepted (just "baa")
lock_free_encoding_omits_facet_locks = refl

separate_simplex_and_vertex_relabellings_preserve_signature :
  map_outcome figure_eight_relabelled figure_eight_knot_complement ≡
    accepted (accepted (just "cPcbbbiht"))
separate_simplex_and_vertex_relabellings_preserve_signature = refl

twenty_four_vertex_permutations_are_available :
  (maybe_count (all_permutations 4)) ≡ just 24
twenty_four_vertex_permutations_are_available = refl

ordered_permutation_index_matches_regina : permutation_rank (1 ∷ 2 ∷ 0 ∷ 3 ∷ []) ≡ 8
ordered_permutation_index_matches_regina = refl

five_vertex_permutation_indices_need_two_characters : integer_width (factorial 5 - 1) ≡ 2
five_vertex_permutation_indices_need_two_characters = refl

facet_trits_use_two_bits_per_trit : encode_trits (1 ∷ 2 ∷ 2 ∷ 2 ∷ []) ≡ just ('P' ∷ 'c' ∷ [])
facet_trits_use_two_bits_per_trit = refl

invalid_facet_trit_is_rejected : encode_trits (3 ∷ []) ≡ nothing
invalid_facet_trit_is_rejected = refl

integer_encoding_rejects_overflow : encode_integer 1 64 ≡ nothing
integer_encoding_rejects_overflow = refl

size_sixty_three_has_a_marker : encode_size 63 ≡ just ('-' ∷ 'b' ∷ '-' ∷ [])
size_sixty_three_has_a_marker = refl

size_sixty_four_has_two_little_endian_characters :
  encode_size 64 ≡ just ('-' ∷ 'c' ∷ 'a' ∷ 'b' ∷ [])
size_sixty_four_has_two_little_endian_characters = refl

signature_minima_use_ascii_order : characters_less ('G' ∷ []) ('c' ∷ []) ≡ true
signature_minima_use_ascii_order = refl
