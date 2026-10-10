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
| [`Regina.Validity3`](Regina/Validity3.agda) | A reasoned dimension-three validity report plus separate reconstruction-completeness diagnostics. |
| [`Regina.All`](Regina/All.agda) | Aggregate entry point for all implementation and reduction-test modules. |

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

## Exact boundary

The current work still omits:

- generic all-dimensional simplex and subface APIs;
- exact codimension-two order outside dimension three;
- higher-dimensional face-numbering tables and link-manifold recognition;
- Regina's packed `Perm<3>` serialization for link-triangle side gluings;
- mutable C++ objects, pointer identity, caches, invalidation, and notification behavior;
- triangle combinatorial-type recognition;
- normal surfaces and hypersurfaces, homology, fundamental groups, Pachner moves, recognition, isomorphism signatures, geometry, GUI code, and native bindings.

The source-shaped validity, face-property, subface, tetrahedron-face, and exact
edge-order reports are specific to dimension three.

## Check

Target: Agda 2.6.3, builtins only.

```text
agda --safe --without-K --ignore-interfaces \
  --no-libraries --no-default-libraries \
  -i agda agda/Regina/All.agda
```

The aggregate checks **38 local modules and 228 concrete reduction
assertions**:

- `Regina.PermutationTests`: 16;
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
- `Regina.ValidityTests`: 6.

See [`VERIFICATION.txt`](VERIFICATION.txt) and the branch workflow for the
recorded run.

## Attribution and license

Thank you to **Benjamin A. Burton**—credited as **Ben Burton** in the translated
source headers—for Regina and the translated permutation, triangulation,
component, orientation, skeleton, dual-forest, face-embedding, exact edge-link,
subface, tetrahedron-face, link, three-dimensional vertex-link,
boundary-component, face-property, and validity algorithms. Thank you to
**Ryan Budney** and **William Pettersson** for their work on Regina. Thank you to
**Richard Rannard** for the figure-eight construction credited by Regina to
chapter 8 of his PhD thesis.

These acknowledgments do not replace Regina's complete contributor and citation
records. The translated material follows the repository's existing
GPL-2.0-or-later terms and additional application-store distribution permission.
See [`LICENSE.txt`](../LICENSE.txt).
