# Dual forest and ordered face embeddings

This slice continues the Agda translation of Regina's generic skeleton
calculation with two related structures:

1. the deterministic maximal forest in the dual graph of top-dimensional
   simplices;
2. ordered appearances of lower-dimensional faces, including detection of
   non-trivial self-identifications.

Source baseline: `e3a5c7c0e0581706d9e5531b750160b322489950`.

## Dual spanning forest

A dual-graph vertex is a top-dimensional simplex. Every paired facet gives a
dual edge, including loops and parallel edges. Regina builds a maximal forest
while it labels connected components.

`Regina.DualForest` reproduces the source traversal order:

- candidate roots occur in increasing simplex index;
- each new root begins a breadth-first traversal;
- queued simplices are processed in discovery order;
- each simplex's facets are examined in increasing local facet number;
- an edge is accepted exactly when its opposite simplex has not been discovered;
- both the source facet and the reciprocal destination facet are stored.

Consequently each non-root simplex has one parent edge, a loop never enters the
forest, and a connected component with `n` simplices contributes `n-1` forest
edges. The code exposes:

- `dualForestEdges`;
- `dualForestEdgeCount`;
- `dualForestFacets`;
- `facetInDualForest`;
- `parentFacetOf` and `childFacetOf`.

The sphere example has four parallel dual edges between two tetrahedra. The
forest selects the first facet examined, namely `0 → 0`. The figure-eight
example selects `simplex 0, facet 0 → simplex 1, facet 1`. The one-tetrahedron
ball bundle has a self-pairing but no forest edge.

The Agda record stores forest edges explicitly. Regina stores a facet bit mask
inside each simplex. The represented forest is the same; the storage layout is
not.

## Generic ordered face appearances

`Regina.Skeleton` identifies a local face only by its simplex and selected
vertex set. That is sufficient for quotient classes but insufficient to tell
whether a face returns to itself with its vertices permuted.

`Regina.Embeddings` therefore adds an ordered list of all simplex vertices. For
a `k`-face:

- positions `0` through `k` are the selected face vertices;
- those selected vertices begin in increasing order;
- the unused complementary vertices begin in decreasing order;
- crossing a facet applies the complete gluing permutation to every position.

Traversal keeps one representative ordering for each local face occurrence. If
a later route reaches the same local face, the two selected prefixes of length
`k+1` are compared. Equality means the route acts trivially on the face's own
vertices. Inequality records a bad identification.

For the deliberately malformed gluing `[1,0,3,2]`, the edge with initial
embedding table `[2,3,1,0]` crosses to `[3,2,0,1]`. The selected prefix changes
from `[2,3]` to `[3,2]`, so the edge is identified with itself in reverse.

## Relation to Regina's exact embedding machinery

Regina's `FaceEmbedding<dim,subdim>` stores a simplex pointer and a
`Perm<dim+1>`. Its first `subdim+1` images locate and order the face vertices;
the remaining images carry link-orientation information. Regina also has:

- precomputed standard-dimension numbering and ordering tables;
- legacy choices for some low-dimensional vertex embeddings;
- orientation-dependent swaps among complementary vertices;
- special codimension-one and codimension-two traversal and appearance order;
- link-orientability flags and bad-link checks.

The generic `Regina.Embeddings` record stores a simplex index, a characteristic
face mask, and an ordered finite list. Its selected prefix implements the basic
self-identification check. This module remains useful as a dimension-generic
quotient traversal and as an independent cross-check.

The formerly missing source-specific codimension-two order is now translated
separately in [`Regina.ExactEdgeLinks3`](Regina/ExactEdgeLinks3.agda). That
module uses Regina's exact dimension-three edge ordering tables, walks each edge
link in both directions, prepends and appends exactly as the C++ source does,
and retains the directed boundary endpoints of path links. See
[`EDGE-LINK-ORDER3.md`](EDGE-LINK-ORDER3.md).

Likewise, orientation-normalised link returns and explicit three-dimensional
vertex links are implemented in later modules. This early slice should not be
read as the final boundary of the complete Agda branch.

## Checked reductions

`Regina.DualForestTests` contains 10 assertions covering empty forests,
disconnected components, deterministic first-discovery edges, reciprocal facet
numbers, roots, and non-tree gluings.

`Regina.EmbeddingTests` contains 11 assertions covering:

- degree profiles for the ball, sphere, ball bundle, and figure-eight examples;
- the figure-eight vertex degree 8, edge degrees 6 and 6, and four facet degrees 2;
- absence of detected bad identifications in the tested figure-eight face dimensions;
- canonical selected-first ordering;
- a concrete reversed-edge self-identification;
- the distinction between that bad edge and its unaffected vertex classes.

The exact source-order edge tests live in `Regina.ExactEdgeLinkTests` and are
documented separately.

Thank you to Benjamin A. Burton, Ryan Budney, William Pettersson, Richard
Rannard, and the Regina contributors. Licensing follows the repository's
existing `LICENSE.txt`.
