# Exact dimension-three edge-link order

`Regina.ExactEdgeLinks3` translates Regina's special codimension-two skeleton
algorithm in dimension three. Unlike the generic finite closure used elsewhere
in the Agda development, this module preserves the source's exact path-or-cycle
walk and its exact order of edge embeddings.

Source baseline: `e3a5c7c0e0581706d9e5531b750160b322489950`.
Primary sources:

- `engine/triangulation/detail/skeleton-impl.h`, the
  `calculateFaces<dim-2>()` branch;
- `engine/triangulation/facenumbering.h`, especially
  `FaceNumberingTables<3,1>`.

## Source edge orderings

A tetrahedron has six local edges. Regina numbers them as

```text
0 = 01
1 = 02
2 = 03
3 = 12
4 = 13
5 = 23
```

and supplies one full even `Perm<4>` for each local edge. The Agda tables are:

```text
edge 0 -> [0,1,2,3]
edge 1 -> [0,2,3,1]
edge 2 -> [0,3,1,2]
edge 3 -> [1,2,0,3]
edge 4 -> [1,3,2,0]
edge 5 -> [2,3,0,1]
```

Positions `0` and `1` are the edge endpoints. Positions `2` and `3` are the two
link directions.

Regina first labels the tetrahedra in each connected component with orientation
signs, choosing a positive root. If the source edge ordering has the wrong sign
for its tetrahedron, the final two positions are swapped. Thus the face mapping
always has the same sign as the tetrahedron orientation before the edge walk
begins.

## The two directed walks

The link of an edge in a three-dimensional triangulation is a path or a cycle.
Regina therefore avoids a general search queue and walks in two straight-line
directions.

Starting from the seed embedding:

1. the forward walk exits through position `2`;
2. the backward walk exits through position `3`;
3. crossing a facet computes

```text
adjacentGluing * currentMapping * swap(2,3)
```

4. newly found forward embeddings are appended;
5. newly found backward embeddings are prepended.

The final list is therefore already ordered from one end of the edge link to the
other. It is not a later sort of an unordered face class.

For a boundary edge, the two walks stop at unpaired tetrahedron facets and the
result is a path. For an internal edge, the walk returns to a previously seen
local edge and the result is a cycle. On such a return, the complete four-entry
mapping must agree with the mapping already stored for that occurrence. A
difference records `INVALID_IDENTIFICATION`, including an edge identified with
itself end for end.

## Deterministic class order

Regina considers tetrahedra in increasing index and local edges in the order
`0,1,2,3,4,5`. A new global edge begins at the first local edge occurrence that
has not already been assigned. `orderedEdgeLinks3` preserves this seed order.

For the one-tetrahedron ball, the six global edge classes therefore begin with
local edge numbers

```text
[0,1,2,3,4,5].
```

Their first and last boundary facets are directed data, not an unordered pair:

```text
first boundaries [3,1,2,3,0,1]
last boundaries  [2,3,1,0,2,0]
```

## Checked examples

| Triangulation | Ordered edge-link result |
|---|---|
| `ball 3` | six degree-one paths, in local seed order |
| `sphere 3` | six degree-two cycles; every ordered list runs from tetrahedron 0 to tetrahedron 1 before closing |
| 3D ball bundle | three paths of degrees `3,2,1` |
| figure-eight complement | two degree-six cycles |
| reversed-edge fixture | exact walk records a bad identification |

The ball-bundle degrees arise from its three local-edge orbits:

```text
{01,12,23}  degree 3
{02,13}     degree 2
{03}        degree 1
```

## Independent consistency checks

The exact layer is checked against both the source algorithm and the older
generic face quotient.

`allOrderedEdgeWalksComplete` requires every directed walk to terminate as a
path or cycle without exhausting its finite fuel.

`orderedEdgeOccurrencesComplete` checks that the sum of all edge degrees is
exactly six times the number of tetrahedra.

`allOrderedEdgeStructuresValid` verifies every consecutive crossing, both path
boundary endpoints, and cycle closure in both directions.

`allOrderedMappingsMatchSimplexOrientations` checks that every stored complete
edge mapping has the sign selected for its tetrahedron.

`allOrderedEdgeClassesMatchGeneric` matches each exact class with the generic
`FaceLinkClass` by local occurrences and checks equal degree and equal
bad-identification status. The generic traversal and the source-specific walk
therefore agree on the mathematical edge classes while serving different
purposes.

`Regina.Validity3` exports the conjunction of these checks as
`report_exact_edge_link_order_complete`. This remains a reconstruction-
completeness field, separate from Regina's mathematical `valid_` predicate.

## Representation boundary

This module translates the source-specific dimension-three codimension-two
order. It does not claim:

- generic exact codimension-two order in every dimension;
- mutable `Face` containers or pointer identity;
- Regina's exact deque implementation;
- cache invalidation and packet notifications;
- a proof that arbitrary user-supplied malformed adjacency arrays terminate
  without the explicit fuel bound.

Accepted Agda triangulations already carry reciprocal facet-pairing evidence,
and the checked examples exhaust all local edge occurrences.

Thank you to Benjamin A. Burton, Ryan Budney, William Pettersson, Richard
Rannard, and the Regina contributors. Licensing follows the repository's
existing `LICENSE.txt`.
