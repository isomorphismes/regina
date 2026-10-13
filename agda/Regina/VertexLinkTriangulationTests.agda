{-# OPTIONS --safe --without-K #-}
module Regina.VertexLinkTriangulationTests where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.Examples
open import Regina.FaceLinks
open import Regina.Components
open import Regina.VertexLinkTriangulation3

private
  record LinkObservation : Set where
    constructor observed_link
    field
      triangles vertices edges boundary_edges inclusion_frames : Nat
      orientable consistent : Bool

  observe : {count : Nat} → Maybe (BuiltVertexLink3 count) → Maybe LinkObservation
  observe nothing = nothing
  observe (just result) = just (observed_link
    (built_link_triangle_count result)
    (length (faceLinkClasses surface 0))
    (length (faceLinkClasses surface 1))
    (unpaired_facet_count surface)
    (length (built_link_inclusion result))
    (triangulationOrientable surface) (pairings_pass (raw_state surface)))
    where
    surface = built_link_triangulation result

  observations : {count : Nat} → Triangulation 3 count → List (Maybe LinkObservation)
  observations currentTriangulation = map observe (buildVertexLinks currentTriangulation)

ball_has_four_one_triangle_disc_links : observations (ball 3) ≡
  (just (observed_link 1 3 3 3 1 true true) ∷
   just (observed_link 1 3 3 3 1 true true) ∷
   just (observed_link 1 3 3 3 1 true true) ∷
   just (observed_link 1 3 3 3 1 true true) ∷ [])
ball_has_four_one_triangle_disc_links = refl

sphere_has_four_two_triangle_sphere_links :
  map_outcome observations (sphere 3) ≡ accepted
  (just (observed_link 2 3 3 0 2 true true) ∷
   just (observed_link 2 3 3 0 2 true true) ∷
   just (observed_link 2 3 3 0 2 true true) ∷
   just (observed_link 2 3 3 0 2 true true) ∷ [])
sphere_has_four_two_triangle_sphere_links = refl

ball_bundle_has_one_four_triangle_disc_link :
  map_outcome observations three_dimensional_ball_bundle ≡ accepted
    (just (observed_link 4 6 9 6 4 true true) ∷ [])
ball_bundle_has_one_four_triangle_disc_link = refl

figure_eight_cusp_builds_an_eight_triangle_torus :
  map_outcome observations figure_eight_knot_complement ≡ accepted
    (just (observed_link 8 4 12 0 8 true true) ∷ [])
figure_eight_cusp_builds_an_eight_triangle_torus = refl

empty_has_no_vertex_links : observations (unpaired_simplices 3 0) ≡ []
empty_has_no_vertex_links = refl
