{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-10. License: ../../LICENSE.txt.

-- Check the translated finite core, examples, components, dual forest,
-- face quotient and embeddings, exact edge-link ordering, subface and
-- tetrahedron-face mappings, face-link diagnostics, explicit vertex links,
-- boundary structure and labels, per-face API properties, reasoned validity,
-- printable second-generation signatures, relative and boundary homology,
-- and all reduction tests.
module Regina.All where

import Regina.Foundation
import Regina.Permutation
import Regina.PermutationExtension
import Regina.Triangulation
import Regina.Input
import Regina.Examples
import Regina.Components
import Regina.DualForest
import Regina.Skeleton
import Regina.Embeddings
import Regina.FaceLinks
import Regina.ExactEdgeLinks3
import Regina.SubfaceIncidence3
import Regina.TetrahedronFaces3
import Regina.Link3
import Regina.VertexLinkSurface3
import Regina.Boundary3
import Regina.BoundaryClassification3
import Regina.BoundaryLabels3
import Regina.FaceProperties3
import Regina.TriangleTypes3
import Regina.FacetOperations3
import Regina.Validity3
import Regina.PermutationTests
import Regina.PermutationExtensionTests
import Regina.TriangulationTests
import Regina.ComponentTests
import Regina.DualForestTests
import Regina.SkeletonTests
import Regina.EmbeddingTests
import Regina.FaceLinkTests
import Regina.ExactEdgeLinkTests
import Regina.SubfaceTests
import Regina.TetrahedronFaceTests
import Regina.Link3Tests
import Regina.VertexLinkTests
import Regina.BoundaryTests
import Regina.BoundaryOrientationTests
import Regina.BoundaryLabelTests
import Regina.FacePropertyTests
import Regina.TriangleTypeTests
import Regina.FacetOperationTests
import Regina.ValidityTests
import Regina.PermutationContraction
import Regina.BoundaryTriangulation3
import Regina.BoundaryTriangulationTests
import Regina.VertexLinkTriangulation3
import Regina.VertexLinkTriangulationTests
import Regina.Integer
import Regina.IntegerMatrix
import Regina.SmithNormalForm
import Regina.SmithNormalFormTests
import Regina.AbelianGroup
import Regina.ChainHomology
import Regina.DualPresentation3
import Regina.HomologyTests
import Regina.PrimalBoundary
import Regina.PrimalBoundaryTests
import Regina.DualBoundary3
import Regina.DualBoundaryTests
import Regina.BoundaryHomology3
import Regina.RelativeHomology3
import Regina.RelativeBoundaryHomologyTests
import Regina.NormalCoordinates3
import Regina.NormalMatching3
import Regina.NormalSurface3
import Regina.NormalSurfaceTests
import Regina.NormalVertices3
import Regina.NormalVertexTests
import Regina.NormalFundamentals3
import Regina.NormalFundamentalTests
import Regina.NormalTriangleReconstruction3
import Regina.NormalTriangleReconstructionTests
import Regina.PachnerRegion3
import Regina.PachnerMoves3
import Regina.PachnerTests
import Regina.SignatureEncoding
import Regina.IsomorphismSignature
import Regina.Relabelling
import Regina.IsomorphismSignatureTests
import Regina.SignatureDecoding
import Regina.DisjointUnion
import Regina.ClassicalSignatureReader
import Regina.ClassicalSignatureReaderTests
import Regina.SecondGenerationSignature3
import Regina.SecondGenerationSignatureTests
