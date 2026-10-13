# Gluing facets through their own vertex labels

Two triangular facets each carry inherent vertex labels `0,1,2`. Those labels
usually differ from their local labels in the containing tetrahedron. A
face-level gluing describes how the inherent labels map across; the simplex
join needs the corresponding map on all four local tetrahedron labels.

`Regina.FacetOperations3` translates `Face<3,2>::join()`, `lock()`, `unlock()`,
and `isLocked()` from `engine/triangulation/face.h` at
`e3a5c7c0e0581706d9e5531b750160b322489950`.

## Mapping between frames

A `FacetFrame3` stores its tetrahedron index and a certified permutation on
four labels. Its first three images locate the inherent triangle vertices;
its fourth image names the opposite vertex, and hence the local facet.
`facetFrame` resolves the first ordered embedding of the supplied global
triangle class in the current triangulation.

The source expression is:

```text
destinationFrame * extend(inherentGluing) * sourceFrame.inverse()
```

The rightmost operation acts first. It recovers the inherent source label,
applies the inherent gluing, and then writes the destination tetrahedron label.
The extended gluing fixes inherent position 3 so the facet-naming vertex maps
to the correct opposite vertex of the destination.

For example, facet 0 of an unpaired tetrahedron has the frame `[1,2,3,0]`,
while facet 3 has the frame `[0,1,2,3]`. Gluing them by the identity in their own
labels produces the local map `[3,0,1,2]`. The opposite vertex 0 maps to 3;
the actual triangle vertices 1,2,3 map to 0,1,2. The reciprocal local map is
`[1,2,3,0]`. This recovers Regina's original three-dimensional ball bundle.

General Agda proofs establish:

- the correct image of every inherent triangle vertex;
- the correct image of the facet-naming opposite vertex;
- equality of the reversed frame expression with the full inverse map;
- identity of the local map when an identity gluing uses the same frame.

The last statement concerns the map; attempting to join a facet to itself is
still rejected by the source preconditions.

## Extending finite permutations

`Regina.PermutationExtension.extendPermutation` translates the case of adding
one fixed final label. It operates at arbitrary finite degree and preserves
the images of all old labels. Its inverse laws follow from the input
permutation's proofs rather than a new exhaustive search.

The module also proves that extension preserves identity, commutes with
inverse, and preserves composition. Repeated extension adds multiple fixed
final labels. Its representation uses an indexed old-or-final position view;
it does not use Regina's packed permutation codes or lookup tables.

The pure core handles degree zero and one, which lie outside Regina's public
`2 ≤ k < n` template guard. The face-level interface uses degree 3 to 4,
inside the source guard. No packed-code, serialization, or performance
equivalence is claimed.

## Operations and failures

| Operation | Result |
|---|---|
| `facetFrame current classNumber` | Resolve a global triangle's inherent-to-local frame. |
| `joinBoundaryFacets current sourceClass destinationClass inherentGluing` | Convert the supplied `Permutation 3` to a local `Permutation 4`, then invoke the certified simplex join. |
| `lockFacetFace current classNumber` | Lock the chosen facet, including both local sides when it is paired. |
| `unlockFacetFace current classNumber` | Clear both paired local locks. |
| `facetFaceIsLocked current classNumber` | Report the chosen facet's lock without changing the state. |

Both faces belong to the one supplied triangulation. An absent global class
returns `invalid_facet_number`; a malformed embedding map returns
`invalid_vertex_permutation`. A join checks occupied facets, forbidden
same-facet pairing, and facet locks in Regina's order. Top-dimensional simplex
locks remain independent, as in the already translated core.

Every accepted state update retains a `PairingsConsistent` certificate.
Repeated lock or unlock operations return `no_change` when appropriate.
The operation works on boundary or paired facets for lock changes, while
joining requires two distinct unpaired facets.

## State and scope

The results are immutable transitions. Skeleton classes are recomputed from
the supplied state. A global class number can change its referent after an
edit; callers must resolve the intended facet in the new state. The interface
does not retain or emulate C++ face pointer identity, deletion, caches,
notifications, or snapshots. Frames are values describing a state, not durable
face handles.

The tests reconstruct the ball bundle through the face-level join, check
non-involutive gluing between distinct tetrahedra and its reverse map, merged
face classes, reciprocal locks, both source and destination lock failures,
source failure priority, absent lookups, and empty triangulations. Generic
permutation proofs and all six triangle permutations are checked separately.
The aggregate contains 44 modules and 277 concrete reduction assertions;
general proofs are additional to this assertion count.

These are local Agda type-checking and computation results, not a native C++
differential run. The exported Face operations are specific to dimension
three. The full Regina application and its other algorithms remain outside
this addition.

Thank you to Benjamin A. Burton (Ben Burton in the source headers), Ryan Budney,
William Pettersson, Richard Rannard, and the Regina contributors. Licensing
follows the repository's existing GPL-2.0-or-later terms and additional
distribution permission in `LICENSE.txt`.
