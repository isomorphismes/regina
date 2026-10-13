{-# OPTIONS --safe --without-K #-}
module Regina.NormalFundamentalTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.Integer using (Int; pos; negsuc)
open import Regina.IntegerMatrix
open import Regina.NormalCoordinates3
open import Regina.NormalMatching3
open import Regina.NormalSurface3
open import Regina.NormalFundamentals3

private
  fundamentalCount : NormalCoords → Maybe Nat
  fundamentalCount encodingValue with fundamentalSurfaces 20 encodingValue (ball 3)
  ... | nothing = nothing
  ... | just result = just (length (fundamental_surface_list result))

  evenCone : MatchingSystem standard 1
  evenCone = matching_system 1 (tabulate 1 7 coefficientValue)
    where
    coefficientValue : Fin 1 → Fin 7 → Int
    coefficientValue _ fzero = pos 1
    coefficientValue _ (fsuc fzero) = pos 1
    coefficientValue _ (fsuc (fsuc fzero)) = negsuc 1
    coefficientValue _ (fsuc (fsuc (fsuc remaining))) = pos zero

  mixedPoint : List Nat
  mixedPoint = 1 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

  containsMixedPoint : Maybe (List (AdmissibleSurface evenCone)) → Bool
  containsMixedPoint nothing = false
  containsMixedPoint (just values) with readSurface standard 1 mixedPoint
  ... | nothing = false
  ... | just wanted = any (λ result → vectorEqual (admissible_vector result) wanted) values

ball_has_seven_standard_fundamental_surfaces : fundamentalCount standard ≡ just 7
ball_has_seven_standard_fundamental_surfaces = refl

ball_has_three_quad_fundamental_surfaces : fundamentalCount quadrilateral ≡ just 3
ball_has_three_quad_fundamental_surfaces = refl

ball_has_ten_almost_normal_fundamental_surfaces : fundamentalCount almost_normal ≡ just 10
ball_has_ten_almost_normal_fundamental_surfaces = refl

ball_has_six_quad_octagon_fundamental_surfaces : fundamentalCount quadrilateral_octagon ≡ just 6
ball_has_six_quad_octagon_fundamental_surfaces = refl

hilbert_basis_can_contain_a_point_between_vertex_rays :
  containsMixedPoint (enumerateFundamentalSystem 30 evenCone) ≡ true
hilbert_basis_can_contain_a_point_between_vertex_rays = refl

incomplete_vertex_enumeration_blocks_fundamental_enumeration :
  fundamentalSurfaces 0 quadrilateral (ball 3) ≡ nothing
incomplete_vertex_enumeration_blocks_fundamental_enumeration = refl
