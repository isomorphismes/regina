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
| [`Regina.Embeddings`](Regina/Embeddings.agda) | Ordered local-face appearances, propagation through gluings, and non-trivial self-identification detection. |
| [`Regina.All`](Regina/All.agda) | Aggregate entry point for implementation and reduction tests. |

Source maps:

- [`SOURCE-MAP.tsv`](SOURCE-MAP.tsv): permutations, gluings, transitions, input, and examples;
- [`COMPONENTS-SOURCE-MAP.tsv`](COMPONENTS-SOURCE-MAP.tsv): components and orientability;
- [`SKELETON-SOURCE-MAP.tsv`](SKELETON-SOURCE-MAP.tsv): lower-dimensional face quotient;
- [`FOREST-EMBEDDINGS-SOURCE-MAP.tsv`](FOREST-EMBEDDINGS-SOURCE-MAP.tsv): dual forest and ordered embeddings.

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
index. The translation reports component sizes and counts unpaired facets
incident to each component.

Regina's orientation rule is preserved: an even facet permutation reverses the
neighboring simplex orientation, while an odd permutation preserves it.
Orientability is checked as reachability in the doubled graph
`(simplex, positive | negative)`; a component is nonorientable when one simplex
is reachable with both signs.

The dual forest follows Regina's concrete traversal order:

1. roots are considered by increasing simplex index;
2. each component is searched breadth-first;
3. facets are examined from 0 through `dimension`;
4. the first gluing that discovers a simplex becomes its forest edge;
5. both incident facets are recorded.

Self-pairings and later gluings to an already discovered simplex are not forest
edges. The tests recover Regina's first-discovery choices for the sphere,
figure-eight, and four-dimensional ball-bundle examples.

## Face quotient and ordered appearances

A local `k`-face is a simplex index plus a Boolean characteristic vector
selecting exactly `k+1` local vertices. It crosses a glued facet when it does not
contain that facet's opposite vertex. The gluing permutation transports the
complete selected vertex set into the neighboring simplex. Finite saturation
therefore computes the global face classes and their degrees.

An ordered `FaceEmbedding` adds a complete local vertex list. The canonical
Agda list places selected face vertices first in increasing order and the
complement afterward in decreasing order, following Regina's generic ordering
rule. Crossing a facet applies the full gluing permutation to this list.

When traversal returns to a local face already seen, the first `k+1` entries are
compared. A disagreement means the underlying `k`-face has been identified with
itself by a non-identity permutation—for example, an edge glued to itself with
its endpoints reversed.

This selected-face-prefix check translates Regina's bad-identification
condition. It does **not** claim byte-for-byte equality with Regina's stored
embedding permutations: Regina has standard-dimension lookup tables, legacy
vertex conventions, orientation normalization on complementary vertices, and
special appearance ordering in codimension two. Those remain outside this
slice.

Checked three-dimensional signatures:

| Construction | vertices | edges | facets |
|---|---:|---:|---:|
| one tetrahedron, `ball 3` | 4 | 6 | 4 |
| two identity-glued tetrahedra, `sphere 3` | 4 | 6 | 4 |
| Regina's 3D ball bundle | 1 | 3 | 3 |
| Regina's figure-eight knot complement | 1 | 2 | 4 |

For the figure-eight triangulation, the single vertex class has degree 8, both
edge classes have degree 6, and all four facet classes have degree 2. Its tested
vertex, edge, and facet classes have no detected non-trivial
self-identifications.

A deliberately malformed one-tetrahedron example pairs two facets with
`[1,0,3,2]`. The local edge `{2,3}` returns as `{3,2}`, and the Agda traversal
marks that edge class as having a bad identification.

## Exact boundary

The current work does not yet implement:

- Regina's standard-dimension face-number lookup tables and legacy embedding labels;
- exact codimension-two path/cycle ordering of appearances;
- orientation-normalized ordering of complementary embedding vertices;
- face links, link orientability, or link triangulations;
- bad-link detection or the full `isValid()` contract;
- real and ideal boundary components;
- normal surfaces and hypersurfaces, homology, fundamental groups, Pachner moves, recognition, isomorphism signatures, geometry, GUI code, or native bindings.

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

The aggregate checks 16 local modules and 109 concrete reduction assertions:

- `Regina.PermutationTests`: 16;
- `Regina.TriangulationTests`: 48;
- `Regina.ComponentTests`: 9;
- `Regina.DualForestTests`: 10;
- `Regina.SkeletonTests`: 15;
- `Regina.EmbeddingTests`: 11.

See [`VERIFICATION.txt`](VERIFICATION.txt) and the branch workflow for the
recorded run.

## Attribution and license

Thank you to **Benjamin A. Burton**—credited as **Ben Burton** in the translated
source headers—for Regina and the translated permutation, triangulation,
component, orientation, skeleton, dual-forest, and face-embedding algorithms.
Thank you to **Ryan Budney** and **William Pettersson** for their work on Regina.
Thank you to **Richard Rannard** for the figure-eight construction credited by
Regina to chapter 8 of his PhD thesis.

These acknowledgments do not replace Regina's complete contributor and citation
records. The translated material follows the repository's existing
GPL-2.0-or-later terms and additional application-store distribution permission.
See [`LICENSE.txt`](../LICENSE.txt).
