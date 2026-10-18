# Regina in Agda

This directory translates a finite mathematical core of Regina into executable,
checked Agda. It is a typed reference implementation, not a complete Regina
port or a replacement for Regina's C++ engine.

Source baseline:
[`regina-normal/regina@e3a5c7c0e0581706d9e5531b750160b322489950`](https://github.com/regina-normal/regina/commit/e3a5c7c0e0581706d9e5531b750160b322489950).

The working fork lives at `isomorphismes/regina`; the `Agda` branch and its
history moved with the repository transfer.

## Implemented modules

| Module | Content |
|---|---|
| [`Regina.Foundation`](Regina/Foundation.agda) | Finite indices, vectors, lists, equality, and proof-producing finite decisions. |
| [`Regina.Permutation`](Regina/Permutation.agda) | Finite permutations, inverse, composition, conjugation, checked image tables, and pointwise laws. |
| [`Regina.PermutationExtension`](Regina/PermutationExtension.agda) | Append a fixed vertex label at any finite degree; proved image preservation, inverse, identity, and composition laws. |
| [`Regina.Triangulation`](Regina/Triangulation.agda) | Dimension-indexed simplices, reciprocal facet gluings, locks, immutable transitions, and consistency certificates. |
| [`Regina.Input`](Regina/Input.agda) | Checked natural-number indices and permutation tables, applied in Regina's failure order. |
| [`Regina.Examples`](Regina/Examples.agda) | Regina's ball, sphere, ball-bundle, and figure-eight constructions. |
| [`Regina.Components`](Regina/Components.agda) | Connected components, simplex counts, boundary-facet counts, permutation parity, and orientability. |
| [`Regina.DualForest`](Regina/DualForest.agda) | Regina's deterministic breadth-first maximal forest in the dual 1-skeleton. |
| [`Regina.Skeleton`](Regina/Skeleton.agda) | Quotient classes of local vertices, edges, and all other proper faces. |
| [`Regina.Embeddings`](Regina/Embeddings.agda) | Generic ordered local-face appearances and non-trivial self-identification detection. |
| [`Regina.FaceLinks`](Regina/FaceLinks.agda) | Orientation-normalised face returns, codimension-specific bad-identification tests, and link orientability. |
| [`Regina.ExactEdgeLinks3`](Regina/ExactEdgeLinks3.agda) | Regina's exact dimension-three codimension-two path/cycle walk, embedding order, directed boundary endpoints, and complete mappings. |
| [`Regina.SubfaceIncidence3`](Regina/SubfaceIncidence3.agda) | Dimension-three `Face::face()` and active `faceMapping()` semantics for edge endpoints and triangle vertices and edges. |
| [`Regina.TetrahedronFaces3`](Regina/TetrahedronFaces3.agda) | Dimension-three `Simplex::face()` and `Simplex::faceMapping()` semantics for tetrahedron vertices, edges, and triangles. |
| [`Regina.Link3`](Regina/Link3.agda) | Three-dimensional vertex-link Euler characteristics and finite, real-boundary, or ideal classification. |
| [`Regina.VertexLinkSurface3`](Regina/VertexLinkSurface3.agda) | Explicit triangle surfaces for three-dimensional vertex links, with addressed side pairings and endpoint-labelled corners. |
| [`Regina.Boundary3`](Regina/Boundary3.agda) | Real boundary components from unpaired facets and ideal boundary components from explicit vertex links. |
| [`Regina.BoundaryClassification3`](Regina/BoundaryClassification3.agda) | Real-boundary orientation propagation and closed-surface classification. |
| [`Regina.BoundaryLabels3`](Regina/BoundaryLabels3.agda) | Canonical positive or negative orientation labels for every real-boundary facet, plus explicit conflict and unresolved states. |
| [`Regina.FaceProperties3`](Regina/FaceProperties3.agda) | Dimension-three `Face` API observations: invalidity bits, boundary/internal/link properties, ideal and standard vertices, degrees, Euler characteristics, and maximal-forest triangles. |
| [`Regina.TriangleTypes3`](Regina/TriangleTypes3.agda) | All eight triangle quotient types, their special vertex or edge roles, and the overlapping cone and Möbius-band predicates. |
| [`Regina.FacetOperations3`](Regina/FacetOperations3.agda) | Face-level gluing, locking, unlocking, and lock queries, with proved conversion from inherent triangle labels to local tetrahedron labels. |
| [`Regina.Validity3`](Regina/Validity3.agda) | A reasoned dimension-three validity report plus separate reconstruction-completeness diagnostics. |
| [`Regina.PermutationContraction`](Regina/PermutationContraction.agda) | Checked restriction of a permutation, with proofs of every retained image and the fixed final image. |
| [`Regina.BoundaryTriangulation3`](Regina/BoundaryTriangulation3.agda) | Actual certified real-boundary triangle triangulations, using the composed maps between directed edge-link ends. |
| [`Regina.VertexLinkTriangulation3`](Regina/VertexLinkTriangulation3.agda) | Certified vertex-link triangle triangulations and their inclusion frames. |
| [`Regina.Integer`](Regina/Integer.agda), [`Regina.IntegerMatrix`](Regina/IntegerMatrix.agda) | Exact integers, both division conventions, dimension-indexed matrices, and proof-producing entrywise equality. |
| [`Regina.SmithNormalForm`](Regina/SmithNormalForm.agda) | Smith reduction with both integral basis changes, both inverses, entrywise equivalence proofs, and explicit exhaustion. |
| [`Regina.AbelianGroup`](Regina/AbelianGroup.agda), [`Regina.ChainHomology`](Regina/ChainHomology.agda) | Invariant factors and kernel/image homology, with the next map transported into the kernel basis. |
| [`Regina.DualPresentation3`](Regina/DualPresentation3.agda) | First homology and raw fundamental-group presentations from the dual forest and exact internal-edge walks. |
| [`Regina.PrimalBoundary`](Regina/PrimalBoundary.agda) | Dimension-generic primal boundary maps and quotient homology, including ideal vertices. |
| [`Regina.DualBoundary3`](Regina/DualBoundary3.agda) | Three-dimensional dual boundary maps and H₀–H₃ of the truncated manifold. |
| [`Regina.RelativeHomology3`](Regina/RelativeHomology3.agda), [`Regina.BoundaryHomology3`](Regina/BoundaryHomology3.agda) | Relative H₁ with real and ideal boundary, H₁ of classified boundary surfaces, and mod-two H₂ rank. |
| [`Regina.NormalCoordinates3`](Regina/NormalCoordinates3.agda), [`Regina.NormalMatching3`](Regina/NormalMatching3.agda) | Standard, quadrilateral, almost-normal and quad-octagon matching equations; local compatibility and enumeration admissibility. |
| [`Regina.NormalSurface3`](Regina/NormalSurface3.agda) | Certified admissible vectors, edge weights, arc counts, and Euler characteristic from finite triangle coordinates. |
| [`Regina.NormalVertices3`](Regina/NormalVertices3.agda), [`Regina.NormalFundamentals3`](Regina/NormalFundamentals3.agda) | Exact finite reference enumeration of primitive vertex rays and fundamental integral vectors; exhaustive algorithms rather than Regina's optimized enumeration engines. |
| [`Regina.All`](Regina/All.agda) | Aggregate entry point for all implementation and reduction-test modules. |
| [`Regina.NormalTriangleReconstruction3`](Regina/NormalTriangleReconstruction3.agda) | Minimal finite triangle coordinates, infinite triangles at conflicting vertex links, preserved quad/octagon counts, and proof-carrying matching/normalisation checks. |
| [`Regina.PachnerRegion3`](Regina/PachnerRegion3.agda), [`Regina.PachnerMoves3`](Regina/PachnerMoves3.agda) | Checked 1–4, 2–3, 3–2, and 4–1 moves with exterior gluings, source creation order, and facet-lock transfer. |
| [`Regina.Relabelling`](Regina/Relabelling.agda), [`Regina.DisjointUnion`](Regina/DisjointUnion.agda) | Dimension-indexed simplex/vertex relabellings, inverses/composition, and component union with transported locks. |
| [`Regina.SignatureEncoding`](Regina/SignatureEncoding.agda), [`Regina.SignatureDecoding`](Regina/SignatureDecoding.agda) | Regina base64 characters, little-endian integers, facet trits, and classical signature parsing. |
| [`Regina.IsomorphismSignature`](Regina/IsomorphismSignature.agda), [`Regina.ClassicalSignatureReader`](Regina/ClassicalSignatureReader.agda) | All-dimensional classical signature minimisation and reconstruction, including locks and disconnected components. |

Source maps:

- [`SOURCE-MAP.tsv`](SOURCE-MAP.tsv): permutations, gluings, transitions, input, and examples;
- [`COMPONENTS-SOURCE-MAP.tsv`](COMPONENTS-SOURCE-MAP.tsv): components and orientability;
- [`SKELETON-SOURCE-MAP.tsv`](SKELETON-SOURCE-MAP.tsv): lower-dimensional face quotient;
- [`FOREST-EMBEDDINGS-SOURCE-MAP.tsv`](FOREST-EMBEDDINGS-SOURCE-MAP.tsv): dual forest and generic ordered embeddings;
- [`FACE-LINKS-SOURCE-MAP.tsv`](FACE-LINKS-SOURCE-MAP.tsv): orientation-normalised face links and three-dimensional Euler data;
- [`EDGE-LINK-ORDER3-SOURCE-MAP.tsv`](EDGE-LINK-ORDER3-SOURCE-MAP.tsv): exact dimension-three edge-link paths, cycles, and embedding order;
- [`SUBFACES3-SOURCE-MAP.tsv`](SUBFACES3-SOURCE-MAP.tsv): dimension-three face-to-subface lookup, mappings, and incidences;
- [`TETRAHEDRON-FACES3-SOURCE-MAP.tsv`](TETRAHEDRON-FACES3-SOURCE-MAP.tsv): dimension-three tetrahedron face tables and mappings;
- [`VERTEX-LINKS-BOUNDARY-SOURCE-MAP.tsv`](VERTEX-LINKS-BOUNDARY-SOURCE-MAP.tsv): explicit vertex-link surfaces and boundary components;
- [`BOUNDARY-ORIENTATION-SOURCE-MAP.tsv`](BOUNDARY-ORIENTATION-SOURCE-MAP.tsv): real-boundary orientation and surface classification;
- [`VALIDITY3-SOURCE-MAP.tsv`](VALIDITY3-SOURCE-MAP.tsv): exported boundary-facet labels and the dimension-three validity report;
- [`FACE-PROPERTIES3-SOURCE-MAP.tsv`](FACE-PROPERTIES3-SOURCE-MAP.tsv): the dimension-three face-property layer.
- [`TRIANGLE-TYPES3-SOURCE-MAP.tsv`](TRIANGLE-TYPES3-SOURCE-MAP.tsv): triangle type, subtype, cone, and Möbius-band recognition.
- [`FACET-OPERATIONS3-SOURCE-MAP.tsv`](FACET-OPERATIONS3-SOURCE-MAP.tsv): permutation extension and face-level gluing and locks.
- [`MATHEMATICAL-ENGINE-SOURCE-MAP.tsv`](MATHEMATICAL-ENGINE-SOURCE-MAP.tsv): boundary/link construction, integer algebra, chain maps, and normal-surface machinery.
- [`RELATIVE-BOUNDARY-HOMOLOGY-SOURCE-MAP.tsv`](RELATIVE-BOUNDARY-HOMOLOGY-SOURCE-MAP.tsv): relative and boundary first homology.

## Certified gluing core

A facet is named by its opposite local vertex. A gluing stores a destination
simplex and a permutation of all local vertex labels. The image of the opposite
vertex names the destination facet, and the reverse adjacency stores the inverse
permutation.

Every accepted `Triangulation` carries a `PairingsConsistent` proof. For each
paired facet, the checker establishes that the other side returns to the source
simplex, uses the inverse vertex map, names a different facet, and carries the
same facet lock.

## Components, global faces, and dual forest

Top-dimensional simplices form a finite adjacency graph through paired facets.
Finite closure partitions them into connected components. An even facet
permutation reverses the neighboring simplex orientation; an odd permutation
preserves it. Orientability is checked in the doubled graph
`(simplex, positive | negative)`.

The dual forest preserves Regina's deterministic order: increasing roots,
breadth-first discovery, increasing facet number, and the first gluing that
reaches each undiscovered simplex.

A local `k`-face is a simplex index plus a Boolean characteristic vector
selecting exactly `k+1` local vertices. Traversing facet gluings and taking
finite closure produces global face classes. Generic ordered embeddings retain
the complete local vertex order. `Regina.FaceLinks` applies Regina's
complementary orientation convention before crossings and keeps separate flags
for a non-trivial face self-identification and a nonorientable link return.

## Exact dimension-three edge links

`Regina.ExactEdgeLinks3` now translates Regina's special codimension-two
algorithm instead of treating edge classes as unordered finite closures.

The six source edge maps are:

```text
[0,1,2,3]
[0,2,3,1]
[0,3,1,2]
[1,2,0,3]
[1,3,2,0]
[2,3,0,1]
```

Positions `0,1` are edge endpoints and positions `2,3` are the two link
directions. After adjusting the seed map to the tetrahedron orientation, the
algorithm walks through position `2` and appends, then through position `3` and
prepends. Every crossing applies

```text
adjacentGluing * currentMapping * swap(2,3).
```

This yields Regina's actual ordered path or cycle, including the directed first
and last boundary facets for a path. A return to an already assigned local edge
compares the complete mapping and detects a reversed self-identification.

Checked exact results:

| Triangulation | Exact edge links |
|---|---|
| `ball 3` | six degree-one paths, in local seed order |
| `sphere 3` | six degree-two cycles |
| 3D ball bundle | three paths of degrees `3,2,1` |
| figure-eight complement | two degree-six cycles |

The exact classes are cross-checked against the generic face quotient for
membership, degree, and bad-identification status. Their total degree is also
checked to be six times the number of tetrahedra, and every path endpoint and
cycle closure is re-evaluated from the triangulation.

See [`EDGE-LINK-ORDER3.md`](EDGE-LINK-ORDER3.md).

## Face-to-subface and tetrahedron-face lookup

`Regina.SubfaceIncidence3` provides:

```text
edge -> vertex
triangle -> vertex
triangle -> edge
```

Each result contains the global lower-face class and a certified `Perm<4>`.
The first `lowerdim + 1` images map the lower face's inherent vertex labels into
the containing face's inherent labels. Loop edges retain distinct endpoint
mappings even when both endpoints return the same global vertex.

`Regina.TetrahedronFaces3` implements the opposite direction:

```text
tetrahedron -> vertex
tetrahedron -> edge
tetrahedron -> triangle
```

Each result returns the global face class and the corresponding translated
`FaceEmbedding` permutation. Active images select the requested local face,
occurrence counts reproduce every global face degree, and paired-facet mappings
commute with their gluing permutations.

See [`SUBFACES3.md`](SUBFACES3.md) and
[`TETRAHEDRON-FACES3.md`](TETRAHEDRON-FACES3.md).

## Explicit vertex links and boundary surfaces

For every global vertex, `Regina.VertexLinkSurface3` builds one link triangle
per tetrahedron-vertex occurrence. Each link-triangle side records either a
boundary edge or the addressed side of the adjacent occurrence, together with
the transported endpoint labels. Every paired side is checked to resolve and to
point back reciprocally.

A link corner is labelled by `(global original edge class, endpoint number)`, so
the two ends of a loop edge remain distinct when they represent different
vertices of the link.

| Original triangulation | Link triangles | Link vertices | Link edges | Boundary edges | Euler characteristic |
|---|---:|---:|---:|---:|---:|
| each vertex of `ball 3` | 1 | 3 | 3 | 3 | 1 |
| each vertex of `sphere 3` | 2 | 3 | 3 | 0 | 2 |
| 3D ball-bundle vertex | 4 | 6 | 9 | 6 | 1 |
| figure-eight ideal vertex | 8 | 4 | 12 | 0 | 0 |

`Regina.Boundary3` distinguishes real boundary components assembled from
unpaired facets from ideal boundary components supplied by vertex links.
`Regina.BoundaryClassification3` propagates real-boundary orientation and then
classifies each connected closed surface from orientability and Euler
characteristic.

| Triangulation | Derived boundary classification |
|---|---|
| `ball 3` | one real orientable sphere, `(V,E,F)=(4,6,4)`, `chi=2`, genus 0 |
| `sphere 3` | no boundary components |
| 3D ball bundle | one real orientable torus, `(V,E,F)=(1,3,2)`, `chi=0`, genus 1 |
| figure-eight knot complement | one ideal orientable torus, `(V,E,F)=(4,12,8)`, `chi=0`, genus 1 |

## Dimension-three face properties and validity

`Regina.FaceProperties3` presents degree, boundary/internal status, link
properties, exact invalidity bits, ideal and standard vertex status, Euler
characteristics, and maximal-forest triangle membership.

The exact invalidity values are:

```text
VALID                  = 0
INVALID_IDENTIFICATION = 1
INVALID_LINK           = 2
```

`Regina.Validity3` packages the checks that set Regina's dimension-three
validity value:

1. reciprocal facet adjacency and inverse gluing permutations;
2. no global edge identified with itself in reverse;
3. every real-boundary vertex has a disc link.

Mathematical validity remains separate from richer reconstruction-completeness
fields. The report independently records whether exact edge order, tetrahedron
face tables, explicit vertex links, and real-boundary orientation assignments
all completed.

## Relative and boundary homology

`Regina.RelativeHomology3` computes H₁ relative to all real and ideal boundary
components. Boundary cells and ideal vertices are removed from the primal
chain groups, and the resulting pair of matrices passes through the existing
checked chain-homology and Smith-form code. Invalid triangulations fail, while
boundary-free triangulations follow Regina's shortcut to ordinary H₁.

`Regina.BoundaryHomology3` sums the first homology of every classified real or
ideal boundary surface. Orientable genus `g` contributes `Z^(2g)`;
nonorientable genus `k` contributes `Z^(k-1) + Z/2`. See
[`RELATIVE-BOUNDARY-HOMOLOGY.md`](RELATIVE-BOUNDARY-HOMOLOGY.md) for the exact
representation choice and evidence boundary.

`secondHomologyModTwoRank` also translates Regina's deduction of mod-two H₂:
the free rank of relative H₁ plus its number of two-primary torsion factors.

## Exact boundary

The current work still omits:

- generic all-dimensional simplex and subface APIs;
- exact codimension-two order outside dimension three;
- higher-dimensional face-numbering tables and link-manifold recognition;
- Regina's packed `Perm<3>` serialization for link-triangle side gluings;
- mutable C++ objects, pointer identity, caches, invalidation, and notification behavior;
- closed-cusp slope equations, cutting/crushing, normal-surface topology, and normal hypersurfaces;
- higher-dimensional truncated dual complexes, fundamental-group Tietze simplification, higher-dimensional Pachner moves, general recognition, second-generation/binary signatures, geometry, GUI code, and native bindings.

The source-shaped validity, face-property, triangle-type, subface,
tetrahedron-face, and exact edge-order reports are specific to dimension three.
Generic primal chain maps do not supply higher-dimensional link recognition.
See [`MATHEMATICAL-ENGINE.md`](MATHEMATICAL-ENGINE.md) and
[`CORE-CONTINUATION-20261013.md`](CORE-CONTINUATION-20261013.md) for the algorithms,
their precise success conditions, and the remaining port boundary.

## Triangle identifications

`Regina.TriangleTypes3` translates Regina's eight triangle types and their
numeric codes: ordinary triangle (1), scarf (2), parachute (3), cone (4),
Möbius band (5), horn (6), dunce hat (7), and the `L(3,1)` spine (8).
Recognition reads the actual global vertex and edge classes and the signs of
the inherent edge mappings. The result stores a bounded special vertex or
edge number only for types that have one. An absent special role corresponds
to Regina's `-1` subtype sentinel.

The ball and sphere contain ordinary triangles. The three-dimensional ball
bundle has one Möbius triangle and two parachutes; the figure-eight complement
has four horn triangles. Both `formsCone` and `formsMobiusBand` hold for a dunce
hat, following Regina's overlapping predicates.

The checked lookup returns `nothing` for a missing triangle or an incident
edge with a reversed self-identification. Regina leaves the latter case
undefined. See [`TRIANGLE-TYPES3.md`](TRIANGLE-TYPES3.md) for the exact input,
mapping conventions, and scope.

## Check

`Regina.FacetOperations3` implements `Face<3,2>::join()` from the inherent
labels of two global triangles. It resolves both frames in the current state
and computes `destinationFrame * extend(inherentGluing) * sourceFrame.inverse()`.
General proofs establish the intended image of every triangle vertex and of
the opposite vertex, as well as the full inverse when the gluing is reversed.
The existing certified join retains Regina's occupancy, same-face, and lock
checks. Paired face locks update both local facets.

See [`FACET-OPERATIONS3.md`](FACET-OPERATIONS3.md). A successful edit produces a
new immutable triangulation; global class indices must be resolved in that new
state rather than treated as persistent C++ face objects.

Target: Agda 2.6.3, builtins only.

```text
agda --safe --without-K --ignore-interfaces \
  --no-libraries --no-default-libraries \
  -i agda agda/Regina/All.agda
```

The aggregate checks **85 local modules and 484 concrete reduction
assertions**:

- `Regina.PermutationTests`: 16;
- `Regina.PermutationExtensionTests`: 5;
- `Regina.TriangulationTests`: 48;
- `Regina.ComponentTests`: 9;
- `Regina.DualForestTests`: 10;
- `Regina.SkeletonTests`: 15;
- `Regina.EmbeddingTests`: 11;
- `Regina.FaceLinkTests`: 15;
- `Regina.ExactEdgeLinkTests`: 18;
- `Regina.SubfaceTests`: 15;
- `Regina.TetrahedronFaceTests`: 13;
- `Regina.Link3Tests`: 12;
- `Regina.VertexLinkTests`: 8;
- `Regina.BoundaryTests`: 7;
- `Regina.BoundaryOrientationTests`: 8;
- `Regina.BoundaryLabelTests`: 4;
- `Regina.FacePropertyTests`: 13;
- `Regina.TriangleTypeTests`: 22;
- `Regina.FacetOperationTests`: 22;
- `Regina.ValidityTests`: 6.
- `Regina.BoundaryTriangulationTests`: 9;
- `Regina.VertexLinkTriangulationTests`: 5;
- `Regina.SmithNormalFormTests`: 18;
- `Regina.HomologyTests`: 14;
- `Regina.PrimalBoundaryTests`: 10;
- `Regina.DualBoundaryTests`: 8;
- `Regina.RelativeBoundaryHomologyTests`: 20;
- `Regina.NormalSurfaceTests`: 19;
- `Regina.NormalVertexTests`: 6;
- `Regina.NormalFundamentalTests`: 6.
- `Regina.NormalTriangleReconstructionTests`: 20;
- `Regina.PachnerTests`: 20;
- `Regina.IsomorphismSignatureTests`: 22;
- `Regina.ClassicalSignatureReaderTests`: 30.

See [`VERIFICATION.txt`](VERIFICATION.txt) for the earlier branch run and
[`TRIANGLE-TYPES3-VERIFICATION.txt`](TRIANGLE-TYPES3-VERIFICATION.txt) for the
triangle-recognition check, and
[`FACET-OPERATIONS3-VERIFICATION.txt`](FACET-OPERATIONS3-VERIFICATION.txt) for
the current local aggregate check.
[`MATHEMATICAL-ENGINE-VERIFICATION.txt`](MATHEMATICAL-ENGINE-VERIFICATION.txt)
records the 69-module continuation.
[`CORE-CONTINUATION-20261013-VERIFICATION.txt`](CORE-CONTINUATION-20261013-VERIFICATION.txt)
records the subsequent aggregate check. Earlier receipts remain historical.

## Attribution and license

Thank you to **Benjamin A. Burton**—credited as **Ben Burton** in the translated
source headers—for Regina and the translated permutation, triangulation,
component, orientation, skeleton, dual-forest, face-embedding, exact edge-link,
subface, tetrahedron-face, link, three-dimensional vertex-link,
boundary-component, face-property, triangle-classification, face-gluing,
permutation-extension, and validity algorithms. Thank you to
Ben Burton for the translated matrix, abelian-group, primal/dual chain-map,
boundary/link construction, and normal-surface matching and coordinate
semantics. The exhaustive normal-surface enumeration algorithms are Agda
reference implementations of the mathematical output, not copies of Regina's
optimized implementations. Thank you to
Ben Burton for triangle reconstruction, Pachner transitions, relabellings,
signature discovery, and signature encodings and readers. Signature root
permutation enumeration is exhaustive reference code; Regina's pruning and
packed representations are not claimed. Thank you to
**Ryan Budney** and **William Pettersson** for their work on Regina. Thank you to
**Richard Rannard** for the figure-eight construction credited by Regina to
chapter 8 of his PhD thesis.

These acknowledgments do not replace Regina's complete contributor and citation
records. The translated material follows the repository's existing
GPL-2.0-or-later terms and additional application-store distribution permission.
See [`LICENSE.txt`](../LICENSE.txt).
