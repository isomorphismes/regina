{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-18. License: ../../LICENSE.txt.
-- Triangulation<3>::homologyRel(), engine/triangulation/dim3/homology.cpp.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.

module Regina.RelativeHomology3 where

open import Regina.Foundation
open import Regina.Triangulation
open import Regina.IntegerMatrix
open import Regina.AbelianGroup
open import Regina.PrimalBoundary
import Regina.Boundary3 as Boundary
import Regina.ChainHomology as Homology
import Regina.DualPresentation3 as Dual
import Regina.FaceProperties3 as Properties
import Regina.Validity3 as Validity

private
  variable
    simplex_count rows columns : Nat

boundaryVertexNumbers : List Properties.VertexProperties3 → List Nat
boundaryVertexNumbers [] = []
boundaryVertexNumbers (currentVertex ∷ remainingVertices)
  with Properties.core_is_boundary (Properties.vertex_core currentVertex)
... | true = Properties.core_face_class_number
  (Properties.vertex_core currentVertex) ∷
  boundaryVertexNumbers remainingVertices
... | false = boundaryVertexNumbers remainingVertices

boundaryEdgeNumbers : List Properties.EdgeProperties3 → List Nat
boundaryEdgeNumbers [] = []
boundaryEdgeNumbers (currentEdge ∷ remainingEdges)
  with Properties.core_is_boundary (Properties.edge_core currentEdge)
... | true = Properties.core_face_class_number
  (Properties.edge_core currentEdge) ∷
  boundaryEdgeNumbers remainingEdges
... | false = boundaryEdgeNumbers remainingEdges

boundaryTriangleNumbers : List Properties.TriangleProperties3 → List Nat
boundaryTriangleNumbers [] = []
boundaryTriangleNumbers (currentTriangle ∷ remainingTriangles)
  with Properties.core_is_boundary (Properties.triangle_core currentTriangle)
... | true = Properties.core_face_class_number
  (Properties.triangle_core currentTriangle) ∷
  boundaryTriangleNumbers remainingTriangles
... | false = boundaryTriangleNumbers remainingTriangles

boundaryCellNumbers : Triangulation 3 simplex_count → Nat → List Nat
boundaryCellNumbers currentTriangulation zero = boundaryVertexNumbers
  (Properties.vertexProperties currentTriangulation)
boundaryCellNumbers currentTriangulation (suc zero) = boundaryEdgeNumbers
  (Properties.edgeProperties currentTriangulation)
boundaryCellNumbers currentTriangulation (suc (suc zero)) =
  boundaryTriangleNumbers (Properties.triangleProperties currentTriangulation)
boundaryCellNumbers currentTriangulation (suc (suc (suc remainingDimension))) = []

relativeCellIndices : (currentTriangulation : Triangulation 3 simplex_count) →
  (cellDimension : Nat) → List (Fin (cellCount currentTriangulation cellDimension))
relativeCellIndices currentTriangulation cellDimension = Homology.filter
  (λ currentIndex → not (Boundary.natMember (fin_to_nat currentIndex)
    (boundaryCellNumbers currentTriangulation cellDimension)))
  (all_fin (cellCount currentTriangulation cellDimension))

relativeCellCount : Triangulation 3 simplex_count → Nat → Nat
relativeCellCount currentTriangulation cellDimension =
  length (relativeCellIndices currentTriangulation cellDimension)

relativeLowerCellCount : Triangulation 3 simplex_count → Nat → Nat
relativeLowerCellCount currentTriangulation zero = zero
relativeLowerCellCount currentTriangulation (suc lowerDimension) =
  relativeCellCount currentTriangulation lowerDimension

restrictMatrix : Matrix rows columns →
  (selectedRows : List (Fin rows)) →
  (selectedColumns : List (Fin columns)) →
  Matrix (length selectedRows) (length selectedColumns)
restrictMatrix original selectedRows selectedColumns = tabulate
  (length selectedRows) (length selectedColumns)
  (λ row column → entry original
    (Homology.lookup selectedRows row)
    (Homology.lookup selectedColumns column))

-- Quotient the primal chain groups by their boundary cells.  Ideal vertices
-- are boundary vertices; their incident edges and triangles remain relative
-- generators unless they lie on a real boundary component.  This is the
-- chain-complex form of Regina's forest-reduced relative presentation.
relativeBoundaryMap : (currentTriangulation : Triangulation 3 simplex_count) →
  (cellDimension : Nat) →
  Maybe (Matrix (relativeLowerCellCount currentTriangulation cellDimension)
    (relativeCellCount currentTriangulation cellDimension))
relativeBoundaryMap currentTriangulation zero =
  just (zeroMatrix zero (relativeCellCount currentTriangulation zero))
relativeBoundaryMap currentTriangulation (suc lowerDimension)
  with boundaryMap currentTriangulation (suc lowerDimension)
... | nothing = nothing
... | just fullBoundary = just (restrictMatrix fullBoundary
  (relativeCellIndices currentTriangulation lowerDimension)
  (relativeCellIndices currentTriangulation (suc lowerDimension)))

relativeFirstHomologyFromMaps : Nat → Triangulation 3 simplex_count →
  Maybe AbelianGroup
relativeFirstHomologyFromMaps fuel currentTriangulation
  with relativeBoundaryMap currentTriangulation 1 |
       relativeBoundaryMap currentTriangulation 2
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just firstBoundary | just secondBoundary =
  Homology.chainHomology fuel firstBoundary secondBoundary

-- Match Regina's validity precondition and its closed-triangulation shortcut.
-- The closed case reuses the already translated dual homology presentation;
-- otherwise the boundary quotient above includes real and ideal boundary.
relativeFirstHomology : Nat → Triangulation 3 simplex_count → Maybe AbelianGroup
relativeFirstHomology fuel currentTriangulation
  with Validity.threeDimensionalValidityValue currentTriangulation
... | false = nothing
... | true with nat_equal (Boundary.boundaryComponentCount currentTriangulation) zero
...   | true = Dual.firstHomology fuel currentTriangulation
...   | false = relativeFirstHomologyFromMaps fuel currentTriangulation

-- Poincare-Lefschetz duality and the universal coefficient theorem give
-- dim H2(M; Z2) from the free and two-primary parts of H1(M, boundary M).
-- This is Regina's complete homologyH2Z2() calculation.
secondHomologyModTwoRank : Nat → Triangulation 3 simplex_count → Maybe Nat
secondHomologyModTwoRank fuel currentTriangulation
  with relativeFirstHomology fuel currentTriangulation
... | nothing = nothing
... | just relativeGroup = just
  (free_rank relativeGroup + torsionRank 2 relativeGroup)
