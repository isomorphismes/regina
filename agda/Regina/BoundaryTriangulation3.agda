{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-12. License: ../../LICENSE.txt.
-- BoundaryComponent<3>::buildRealBoundary(), from
-- engine/triangulation/detail/boundarycomponent-impl.h, lines 139-202.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.BoundaryTriangulation3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.PermutationExtension using (includeInitialIndex)
open import Regina.PermutationContraction
open import Regina.Triangulation
open import Regina.Skeleton
open import Regina.FaceLinks
import Regina.Embeddings as Embeddings
import Regina.SubfaceIncidence3 as Subfaces
import Regina.ExactEdgeLinks3 as ExactEdges
import Regina.Boundary3 as Boundary
import Regina.FacetOperations3 as Frames

private
  variable
    simplex_count : Nat

lookupComponentFacet : (component : List (Boundary.IndexedBoundaryFacet simplex_count)) →
  Fin (length component) → Boundary.IndexedBoundaryFacet simplex_count
lookupComponentFacet [] ()
lookupComponentFacet (head ∷ tail) fzero = head
lookupComponentFacet (head ∷ tail) (fsuc index) = lookupComponentFacet tail index

componentFrame : Triangulation 3 simplex_count →
  (component : List (Boundary.IndexedBoundaryFacet simplex_count)) →
  Fin (length component) → Outcome (Frames.FacetFrame3 simplex_count)
componentFrame currentTriangulation component index = Frames.facetFrame
  currentTriangulation
  (Boundary.boundary_facet_class_number (lookupComponentFacet component index))

record BoundaryEnd3 (simplex_count : Nat) : Set where
  constructor boundary_end_three
  field
    end_facet : Facet 3 simplex_count
    end_edge_mapping : Permutation 4
    other_end_facet : Facet 3 simplex_count
    other_end_edge_mapping : Permutation 4
    end_ridge_position : Fin 4
open BoundaryEnd3 public

-- One edge-link path has two *directed* ends. A loop edge can have both
-- ends in one tetrahedron, or even in the same boundary triangle.
edgeEnds : ExactEdges.OrderedEdgeLink3 simplex_count →
  Maybe (List (BoundaryEnd3 simplex_count))
edgeEnds currentEdge with ExactEdges.ordered_edge_shape currentEdge
... | ExactEdges.edge_link_cycle = nothing
... | ExactEdges.edge_link_incomplete = nothing
... | ExactEdges.edge_link_path
  with ExactEdges.ordered_edge_first_boundary currentEdge |
       ExactEdges.ordered_edge_last_boundary currentEdge |
       ExactEdges.firstEmbeddingOf (ExactEdges.ordered_edge_embeddings currentEdge) |
       ExactEdges.lastEmbeddingOf (ExactEdges.ordered_edge_embeddings currentEdge)
... | just firstFacet | just lastFacet | just firstEmbedding | just lastEmbedding
  with from_image_list 4 (Embeddings.embeddingVertexTable firstEmbedding) |
       from_image_list 4 (Embeddings.embeddingVertexTable lastEmbedding)
... | just firstMapping | just lastMapping = just
  (boundary_end_three firstFacet firstMapping lastFacet lastMapping
     ExactEdges.vertexTwo ∷
   boundary_end_three lastFacet lastMapping firstFacet firstMapping
     ExactEdges.vertexThree ∷ [])
... | nothing | _ = nothing
... | just _ | nothing = nothing
edgeEnds currentEdge | ExactEdges.edge_link_path | _ | _ | _ | _ = nothing

endMatches : Frames.FacetFrame3 simplex_count → Fin 3 →
  BoundaryEnd3 simplex_count → Bool
endMatches sourceFrame sideNumber currentEnd =
  facet_equal (Frames.framedFacet sourceFrame) (end_facet currentEnd) and
  fin_equal
    (image (Frames.frame_vertex_mapping sourceFrame)
      (includeInitialIndex sideNumber))
    (image (end_edge_mapping currentEnd) (end_ridge_position currentEnd))

findEnd : Frames.FacetFrame3 simplex_count → Fin 3 →
  List (ExactEdges.OrderedEdgeLink3 simplex_count) →
  Maybe (BoundaryEnd3 simplex_count)
findEnd sourceFrame sideNumber [] = nothing
findEnd sourceFrame sideNumber (currentEdge ∷ remainingEdges)
  with edgeEnds currentEdge
... | nothing = findEnd sourceFrame sideNumber remainingEdges
... | just ends with find (endMatches sourceFrame sideNumber) ends
... | just matchedEnd = just matchedEnd
... | nothing = findEnd sourceFrame sideNumber remainingEdges

findDestination : Triangulation 3 simplex_count →
  (component : List (Boundary.IndexedBoundaryFacet simplex_count)) →
  Facet 3 simplex_count → List (Fin (length component)) →
  Maybe (Fin (length component))
findDestination currentTriangulation component wantedFacet [] = nothing
findDestination currentTriangulation component wantedFacet (index ∷ remaining)
  with componentFrame currentTriangulation component index
... | rejected _ = nothing
... | accepted currentFrame
  with facet_equal wantedFacet (Frames.framedFacet currentFrame)
... | true = just index
... | false = findDestination currentTriangulation component wantedFacet remaining

swapLinkDirections : Permutation 4
swapLinkDirections = permutation forward forward undo undo
  where
  forward : Fin 4 → Fin 4
  forward fzero = fzero
  forward (fsuc fzero) = fsuc fzero
  forward (fsuc (fsuc fzero)) = fsuc (fsuc (fsuc fzero))
  forward (fsuc (fsuc (fsuc fzero))) = fsuc (fsuc fzero)
  undo : (vertex : Fin 4) → forward (forward vertex) ≡ vertex
  undo fzero = refl
  undo (fsuc fzero) = refl
  undo (fsuc (fsuc fzero)) = refl
  undo (fsuc (fsuc (fsuc fzero))) = refl

-- This is the source's five-factor composition, in both path directions.
-- The retained fourth image must be fixed before contraction is accepted.
boundarySideMapping : Frames.FacetFrame3 simplex_count →
  Frames.FacetFrame3 simplex_count → BoundaryEnd3 simplex_count →
  Permutation 4
boundarySideMapping sourceFrame targetFrame currentEnd = compose
  (inverse (Frames.frame_vertex_mapping targetFrame))
  (compose (other_end_edge_mapping currentEnd)
    (compose swapLinkDirections
      (compose (inverse (end_edge_mapping currentEnd))
        (Frames.frame_vertex_mapping sourceFrame))))

resolveBoundarySide : Triangulation 3 simplex_count →
  (component : List (Boundary.IndexedBoundaryFacet simplex_count)) →
  List (ExactEdges.OrderedEdgeLink3 simplex_count) →
  Facet 2 (length component) → Maybe (Gluing 2 (length component))
resolveBoundarySide currentTriangulation component edgeClasses sourceSide
  with componentFrame currentTriangulation component (simplex_number sourceSide)
... | rejected _ = nothing
... | accepted sourceFrame
  with findEnd sourceFrame (opposite_vertex sourceSide) edgeClasses
... | nothing = nothing
... | just currentEnd
  with findDestination currentTriangulation component (other_end_facet currentEnd)
    (all_fin (length component))
... | nothing = nothing
... | just targetIndex
  with componentFrame currentTriangulation component targetIndex
... | rejected _ = nothing
... | accepted targetFrame
  with contractPermutation (boundarySideMapping sourceFrame targetFrame currentEnd)
... | nothing = nothing
... | just contractionResult = just
  (gluing targetIndex (contracted_permutation contractionResult))

record BuiltRealBoundary3 : Set where
  constructor built_real_boundary_three
  field
    boundary_source_triangle_numbers : List Nat
    boundary_triangle_count : Nat
    boundary_triangulation : Triangulation 2 boundary_triangle_count
open BuiltRealBoundary3 public

private
  isResolved : {element : Set} → Maybe element → Bool
  isResolved nothing = false
  isResolved (just _) = true

buildFromSideTable : (component : List (Boundary.IndexedBoundaryFacet simplex_count)) →
  (sideGluing : Facet 2 (length component) → Maybe (Gluing 2 (length component))) →
  Maybe BuiltRealBoundary3
buildFromSideTable component sideGluing
  with all (λ sourceSide → isResolved (sideGluing sourceSide))
    (all_facets 2 (length component))
... | false = nothing
... | true with certify (raw_triangulation sideGluing (λ _ → false) (λ _ → false))
... | rejected _ = nothing
... | accepted certifiedBoundary = just (built_real_boundary_three
  (Boundary.componentFacetNumbers component) (length component) certifiedBoundary)

buildRealBoundaryComponent : Triangulation 3 simplex_count →
  (component : List (Boundary.IndexedBoundaryFacet simplex_count)) →
  Maybe BuiltRealBoundary3
buildRealBoundaryComponent currentTriangulation component = buildFromSideTable
  component (resolveBoundarySide currentTriangulation component
    (ExactEdges.orderedEdgeLinks3 currentTriangulation))

buildRealBoundaryComponents : Triangulation 3 simplex_count →
  List (Maybe BuiltRealBoundary3)
buildRealBoundaryComponents currentTriangulation = map
  (buildRealBoundaryComponent currentTriangulation)
  (Boundary.realBoundaryFacetComponents currentTriangulation)
