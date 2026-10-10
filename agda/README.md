# Regina in Agda

This directory translates a finite mathematical core of Regina into executable,
checked Agda. It is a typed reference implementation, not a complete Regina
port or a replacement for Regina's C++ engine.

Source baseline:
[`regina-normal/regina@e3a5c7c0e0581706d9e5531b750160b322489950`](https://github.com/regina-normal/regina/commit/e3a5c7c0e0581706d9e5531b750160b322489950).

## Implemented modules

| Module | Content |
|---|---|
| [`Regina.Foundation`](Regina/Foundation.agda) | Finite indices, vectors, lists, equality, and proof-producing finite decisions. |
| [`Regina.Permutation`](Regina/Permutation.agda) | Finite permutations, inverse, composition, conjugation, checked image tables, and pointwise laws. |
| [`Regina.Triangulation`](Regina/Triangulation.agda) | Dimension-indexed simplices, reciprocal facet gluings, locks, join, unjoin, isolate, and consistency certificates. |
| [`Regina.Input`](Regina/Input.agda) | Checked natural-number indices and permutation tables, applied in Regina's failure order. |
| [`Regina.Examples`](Regina/Examples.agda) | Regina's ball, sphere, ball-bundle, and figure-eight constructions. |
| [`Regina.Components`](Regina/Components.agda) | Connected components, simplex counts, boundary-facet counts, permutation parity, and orientability. |
| [`Regina.DualForest`](Regina/DualForest.agda) | Regina's deterministic breadth-first maximal forest in the dual 1-skeleton. |
| [`Regina.Skeleton`](Regina/Skeleton.agda) | Quotient classes of local vertices, edges, and all other proper faces. |
| [`Regina.Embeddings`](Regina/Embeddings.agda) | Ordered local-face appearances and basic non-trivial self-identification detection. |
| [`Regina.FaceLinks`](Regina/FaceLinks.agda) | Orientation-normalised face returns, codimension-specific bad-identification tests, and link orientability. |
| [`Regina.Link3`](Regina/Link3.agda) | Three-dimensional vertex-link Euler characteristics and finite, real-boundary, or ideal classification. |
| [`Regina.All`](Regina/All.agda) | Aggregate entry point for all implementation and reduction-test modules. |

Source maps:

- [`SOURCE-MAP.tsv`](SOURCE-MAP.tsv): permutations, gluings, transitions, input, and examples;
- [`COMPONENTS-SOURCE-MAP.tsv`](COMPONENTS-SOURCE-MAP.tsv): components and orientability;
- [`SKELETON-SOURCE-MAP.tsv`](SKELETON-SOURCE-MAP.tsv): lower-dimensional face quotient;
- [`FOREST-EMBEDDINGS-SOURCE-MAP.tsv`](FOREST-EMBEDDINGS-SOURCE-MAP.tsv): dual forest and ordered embeddings;
- [`FACE-LINKS-SOURCE-MAP.tsv`](FACE-LINKS-SOURCE-MAP.tsv): orientation-normalised face links and three-dimensional vertex links.

## Certified facet gluings

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

## Components, orientation, and dual forest

Top-dimensional simplices form a finite adjacency graph through paired facets.
Finite closure partitions them into connected components in increasing root
index. An even facet permutation reverses the neighboring simplex orientation;
an odd permutation preserves it. Orientability is checked in the doubled graph
`(simplex, positive | negative)`.

The dual forest follows Regina's order exactly: increasing roots,
breadth-first discovery, increasing facet number, and the first gluing that
reaches each undiscovered simplex. Both incident facets are recorded. Loops and
later parallel edges do not enter the forest.

## Face quotient, embeddings, and links

A local `k`-face is a simplex index plus a Boolean characteristic vector
selecting exactly `k+1` local vertices. Traversing facet gluings and taking
finite closure produces the global face classes and their degrees.

An ordered embedding stores every local vertex, with the selected face vertices
first. `Regina.FaceLinks` then applies Regina's orientation convention: before
a codimension-at-least-two crossing, it swaps the final two ordering positions
and applies the complete facet gluing permutation.

Return maps are checked differently by codimension:

- codimension one requires no further return test;
- codimension two compares the complete ordering in dimensions above two;
- larger codimension compares the face-vertex prefix for bad
  self-identifications and the complementary permutation parity for link
  orientability.

This keeps two failures separate. An edge can return with its endpoints reversed
while its one-dimensional link remains orientable. A vertex can return with its
own label fixed while the complementary triangle is reversed, producing a
nonorientable vertex link without a bad vertex identification.

See [`FACE-LINKS.md`](FACE-LINKS.md) for the exact rules and fixtures.

## Three-dimensional vertex links

For dimension three, Regina computes a vertex-link Euler characteristic from
global edge incidence:

```text
chi(link) = (2 * interior_link_vertices + boundary_link_vertices
             - tetrahedron_vertex_degree) / 2
```

A boundary edge contributes `1` to each valid endpoint link; an interior edge
contributes `2`. An invalid reversed edge contributes only at its first endpoint,
matching the source's protection against false double-counting.

The translated classifications are:

- boundary vertex with Euler characteristic `1`: real-boundary disc link;
- other boundary Euler characteristic: invalid boundary link;
- non-boundary Euler characteristic `2`: finite 2-sphere link;
- other non-boundary Euler characteristic: ideal vertex;
- ideal Euler characteristic `0`: standard ideal link.

Checked examples:

| Construction | Vertex-link result | Aggregate report |
|---|---|---|
| One tetrahedron, `ball 3` | Four orientable discs, degree 1, Euler characteristic 1 | locally valid, non-ideal, standard |
| Two identity-glued tetrahedra, `sphere 3` | Four orientable 2-spheres, degree 2, Euler characteristic 2 | locally valid, non-ideal, standard |
| Regina's 3D ball bundle | One orientable disc, degree 4, Euler characteristic 1 | locally valid, non-ideal, standard |
| Figure-eight knot complement | One orientable closed link, degree 8, Euler characteristic 0 | locally valid, ideal, standard |
| Reversed-edge fixture | Bad codimension-two return | locally invalid |
| Complement-reversal fixture | Nonorientable vertex link with no bad vertex identification | the two diagnostics remain distinct |

`threeDimensionalLocallyValid` is intentionally not called `isValid()`. It
combines certified reciprocal facet data, the translated lower-face
self-identification rules, and the real-boundary Euler test. It does not claim
the full Regina validity contract.

## Exact boundary

The current work still omits:

- Regina's standard-dimension face-number lookup tables and legacy embedding labels;
- exact codimension-two path/cycle appearance order;
- explicit link triangulations and their face tables;
- higher-dimensional link-manifold recognition and bad-link flags;
- real and ideal boundary-component adjacency structures;
- Regina's complete `isValid()` implementation;
- normal surfaces and hypersurfaces, homology, fundamental groups, Pachner moves, recognition, isomorphism signatures, geometry, GUI code, and native bindings.

The simplex count is fixed in the Agda type. State changes are immutable.
Packed integers, pointers, mutation notifications, caches, and Regina's
performance characteristics are not translated.

## Check

Target: Agda 2.6.3, builtins only.

```text
agda --safe --without-K --ignore-interfaces \
  --no-libraries --no-default-libraries \
  -i agda agda/Regina/All.agda
```

The aggregate checks **20 local modules and 136 concrete reduction
assertions**:

- `Regina.PermutationTests`: 16;
- `Regina.TriangulationTests`: 48;
- `Regina.ComponentTests`: 9;
- `Regina.DualForestTests`: 10;
- `Regina.SkeletonTests`: 15;
- `Regina.EmbeddingTests`: 11;
- `Regina.FaceLinkTests`: 15;
- `Regina.Link3Tests`: 12.

See [`VERIFICATION.txt`](VERIFICATION.txt) and the branch workflow for the
recorded run.

## Attribution and license

Thank you to **Benjamin A. Burton**—credited as **Ben Burton** in the translated
source headers—for Regina and the translated permutation, triangulation,
component, orientation, skeleton, dual-forest, face-embedding, link-orientation,
and three-dimensional vertex-link algorithms. Thank you to **Ryan Budney** and
**William Pettersson** for their work on Regina. Thank you to **Richard Rannard**
for the figure-eight construction credited by Regina to chapter 8 of his PhD
thesis.

These acknowledgments do not replace Regina's complete contributor and citation
records. The translated material follows the repository's existing
GPL-2.0-or-later terms and additional application-store distribution permission.
See [`LICENSE.txt`](../LICENSE.txt).
