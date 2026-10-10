# Regina in Agda

This directory translates a finite mathematical core of Regina into executable,
checked Agda. It is a typed reference implementation, not a complete Regina
port or a replacement for Regina's C++ engine.

Source baseline:
[`regina-normal/regina@e3a5c7c0e0581706d9e5531b750160b322489950`](https://github.com/regina-normal/regina/commit/e3a5c7c0e0581706d9e5531b750160b322489950).

The working fork now lives at `isomorphismes/regina`; the `Agda` branch and its
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
| [`Regina.Embeddings`](Regina/Embeddings.agda) | Ordered local-face appearances and non-trivial self-identification detection. |
| [`Regina.FaceLinks`](Regina/FaceLinks.agda) | Orientation-normalised face returns, codimension-specific bad-identification tests, and link orientability. |
| [`Regina.SubfaceIncidence3`](Regina/SubfaceIncidence3.agda) | Dimension-three `Face::face()` and active `faceMapping()` semantics for edge endpoints and triangle vertices and edges. |
| [`Regina.Link3`](Regina/Link3.agda) | Three-dimensional vertex-link Euler characteristics and finite, real-boundary, or ideal classification. |
| [`Regina.VertexLinkSurface3`](Regina/VertexLinkSurface3.agda) | Explicit triangle surfaces for three-dimensional vertex links, with addressed side pairings and endpoint-labelled corners. |
| [`Regina.Boundary3`](Regina/Boundary3.agda) | Real boundary components from unpaired facets and ideal boundary components from explicit vertex links. |
| [`Regina.BoundaryClassification3`](Regina/BoundaryClassification3.agda) | Real-boundary orientation propagation and closed-surface classification. |
| [`Regina.BoundaryLabels3`](Regina/BoundaryLabels3.agda) | Canonical positive or negative orientation labels for every real-boundary facet, plus explicit conflict and unresolved states. |
| [`Regina.FaceProperties3`](Regina/FaceProperties3.agda) | Dimension-three `Face` API observations: invalidity bits, boundary/internal/link properties, ideal and standard vertices, degrees, Euler characteristics, and maximal-forest triangles. |
| [`Regina.Validity3`](Regina/Validity3.agda) | A reasoned source-shaped three-dimensional validity report and separate translation-completeness diagnostics. |
| [`Regina.All`](Regina/All.agda) | Aggregate entry point for all implementation and reduction-test modules. |

Source maps:

- [`SOURCE-MAP.tsv`](SOURCE-MAP.tsv): permutations, gluings, transitions, input, and examples;
- [`COMPONENTS-SOURCE-MAP.tsv`](COMPONENTS-SOURCE-MAP.tsv): components and orientability;
- [`SKELETON-SOURCE-MAP.tsv`](SKELETON-SOURCE-MAP.tsv): lower-dimensional face quotient;
- [`FOREST-EMBEDDINGS-SOURCE-MAP.tsv`](FOREST-EMBEDDINGS-SOURCE-MAP.tsv): dual forest and ordered embeddings;
- [`FACE-LINKS-SOURCE-MAP.tsv`](FACE-LINKS-SOURCE-MAP.tsv): orientation-normalised face links and three-dimensional Euler data;
- [`SUBFACES3-SOURCE-MAP.tsv`](SUBFACES3-SOURCE-MAP.tsv): dimension-three subface lookup, mappings, and incidences;
- [`VERTEX-LINKS-BOUNDARY-SOURCE-MAP.tsv`](VERTEX-LINKS-BOUNDARY-SOURCE-MAP.tsv): explicit vertex-link surfaces and boundary components;
- [`BOUNDARY-ORIENTATION-SOURCE-MAP.tsv`](BOUNDARY-ORIENTATION-SOURCE-MAP.tsv): real-boundary orientation and surface classification;
- [`VALIDITY3-SOURCE-MAP.tsv`](VALIDITY3-SOURCE-MAP.tsv): exported boundary-facet labels and the three-dimensional validity report;
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

For Regina's three-dimensional ball bundle, facet 0 and facet 3 of one
tetrahedron are paired by `[3,0,1,2]`; the reverse map is `[1,2,3,0]`.
Different facets of one simplex may be paired. A facet may not be paired with
itself.

## Components, faces, and links

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
finite closure produces global face classes. Ordered embeddings retain the
complete local vertex order. `Regina.FaceLinks` applies Regina's complementary
orientation convention before crossings and keeps separate flags for a
non-trivial face self-identification and a nonorientable link return.

## Dimension-three subfaces

`Regina.SubfaceIncidence3` provides the fixed-dimension subface operations that
are most useful in a three-dimensional triangulation:

```text
edge -> vertex
triangle -> vertex
triangle -> edge
```

Each result contains the global lower-face class and a certified `Perm<4>`.
The first `lowerdim + 1` images map the lower face's inherent vertex labels into
the containing face's inherent labels, matching Regina's documented
`faceMapping()` contract. The unused images are completed deterministically
with the remaining labels in increasing order; this tail is not claimed to
match Regina because the source declares it semantically unspecified.

The inherent numbering is checked by reduction:

- edge endpoints map to positions `0` and `1`;
- triangle vertices map to `0`, `1`, and `2`;
- triangle edge `0` occupies positions `{1,2}`;
- triangle edge `1` occupies `{0,2}`;
- triangle edge `2` occupies `{0,1}`.

The distinction between a returned global face and its mapping matters for loop
edges. In the figure-eight triangulation, both endpoints of each global edge
return the same global vertex class, but the active mapping images remain `0`
and `1`. Incidence observations therefore count endpoint and corner roles with
multiplicity instead of collapsing them to set membership.

See [`SUBFACES3.md`](SUBFACES3.md) for the full fixed-dimension contract and
checked incidence tables.

## Explicit vertex links and boundary surfaces

For every global vertex, `Regina.VertexLinkSurface3` builds one link triangle
per tetrahedron-vertex occurrence. Each link-triangle side records either a
boundary edge or the addressed side of the adjacent occurrence, together with
the transported endpoint labels. Every paired side is checked to resolve and to
point back reciprocally.

A link corner is labelled by

```text
(global original edge class, endpoint 0 or endpoint 1)
```

so the two ends of a loop edge remain distinct when they represent different
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
| `ball 3` | one real orientable sphere, `(V,E,F)=(4,6,4)`, `χ=2`, genus 0 |
| `sphere 3` | no boundary components |
| 3D ball bundle | one real orientable torus, `(V,E,F)=(1,3,2)`, `χ=0`, genus 1 |
| figure-eight knot complement | one ideal orientable torus, `(V,E,F)=(4,12,8)`, `χ=0`, genus 1 |

## Dimension-three `Face` properties

`Regina.FaceProperties3` presents the translated skeleton results through the
shape of Regina's public `Face<3,subdim>` API.

The private `whyInvalid_` constants are represented exactly:

```text
VALID                  = 0
INVALID_IDENTIFICATION = 1
INVALID_LINK           = 2
```

The two failure bits may coexist, yielding code `3`. The immutable Agda record
exposes `isValid`, `hasBadIdentification`, and `hasBadLink` observations without
copying Regina's mutable face-object cache.

For every vertex, edge, and triangle the module records:

- face-class index and degree;
- link orientability;
- incidence with real boundary;
- `isBoundary` and `isInternal`;
- invalid-identification and invalid-link bits.

Vertices additionally record:

- whether the link is closed;
- ideal and standard status;
- link Euler characteristic;
- a normalised two-bit code for ideal and real-boundary status.

The last code uses Regina's published values `1` and `2`, but is an Agda
observation over the dimension-three API. Regina's C++ `vertexFlags_` field is
physically instantiated only for four-dimensional vertices at this source
revision.

The distinction between boundary and closed link is preserved. A figure-eight
ideal vertex is both `isBoundary = true` and `isLinkClosed = true`; a real
boundary vertex has an open disc link. `isInternal` is exactly validity
conjoined with the negation of `isBoundary`.

For codimension-one faces, the module also exposes membership in the maximal
dual forest. The sphere and figure-eight examples each have one global triangle
selected by the forest, while the one-tetrahedron ball has none.

See [`FACE-PROPERTIES3.md`](FACE-PROPERTIES3.md) for the checked observations and
representation boundary.

## Three-dimensional validity

`Regina.Validity3` packages the checks that set Regina's three-dimensional
`valid_` flag at the pinned source revision:

1. reciprocal facet adjacency and inverse gluing permutations;
2. no global edge identified with itself in reverse;
3. every vertex lying in a real boundary facet has link Euler characteristic
   `1`, as required for a disc link.

A non-boundary vertex with link Euler characteristic `2` is finite. Any other
non-boundary vertex is ideal; it remains valid because Regina allows arbitrary
closed 2-manifold vertex links in dimension three. The separate `standard`
flag requires an ideal link to have Euler characteristic `0`.

The report keeps mathematical validity separate from reconstruction
completeness for explicit vertex-link cells and real-boundary orientation
assignments.

## Exact boundary

The current work still omits:

- Regina's standard-dimension face-number lookup tables and legacy embedding labels;
- exact codimension-two path/cycle appearance order;
- Regina's packed `Perm<3>` serialization for link-triangle side gluings;
- mutable C++ face objects, pointer identity, component pointers, cache invalidation, and notification behavior;
- tetrahedron-to-proper-face lookup through the `Face` API and the generic all-dimensional subface family;
- Regina's choices for semantically unused tail images of `faceMapping()`;
- triangle combinatorial-type recognition;
- higher-dimensional link-manifold recognition and validity;
- normal surfaces and hypersurfaces, homology, fundamental groups, Pachner moves, recognition, isomorphism signatures, geometry, GUI code, and native bindings.

The source-shaped validity, face-property, and subface reports are specific to
dimension three. They do not claim the complete generic
`Triangulation<dim>::isValid()` or all-dimensional `Face<dim,subdim>`
implementation.

## Check

Target: Agda 2.6.3, builtins only.

```text
agda --safe --without-K --ignore-interfaces \
  --no-libraries --no-default-libraries \
  -i agda agda/Regina/All.agda
```

The aggregate checks **34 local modules and 197 concrete reduction
assertions**:

- `Regina.PermutationTests`: 16;
- `Regina.TriangulationTests`: 48;
- `Regina.ComponentTests`: 9;
- `Regina.DualForestTests`: 10;
- `Regina.SkeletonTests`: 15;
- `Regina.EmbeddingTests`: 11;
- `Regina.SubfaceTests`: 15;
- `Regina.FaceLinkTests`: 15;
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
component, orientation, skeleton, dual-forest, face-embedding, subface, link,
three-dimensional vertex-link, boundary-component, face-property, and validity
algorithms. Thank you to **Ryan Budney** and **William Pettersson** for their work
on Regina. Thank you to **Richard Rannard** for the figure-eight construction
credited by Regina to chapter 8 of his PhD thesis.

These acknowledgments do not replace Regina's complete contributor and citation
records. The translated material follows the repository's existing
GPL-2.0-or-later terms and additional application-store distribution permission.
See [`LICENSE.txt`](../LICENSE.txt).
