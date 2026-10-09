# Regina in Agda

This directory translates a finite mathematical core of Regina into executable,
checked Agda. It is not a complete Regina port.

Source baseline:
[`regina-normal/regina@e3a5c7c0e0581706d9e5531b750160b322489950`](https://github.com/regina-normal/regina/commit/e3a5c7c0e0581706d9e5531b750160b322489950).

## Implemented

| Module | Content |
|---|---|
| [`Regina.Permutation`](Regina/Permutation.agda) | Finite permutations, identity, inverse, composition, conjugation, checked image tables, and pointwise laws. |
| [`Regina.Triangulation`](Regina/Triangulation.agda) | Dimension-indexed simplices, facet gluings, locks, join, unjoin, isolate, and certified reciprocal pairings. |
| [`Regina.Input`](Regina/Input.agda) | Checked natural-number indices and permutation tables, applied in Regina's failure order. |
| [`Regina.Examples`](Regina/Examples.agda) | Regina's ball, sphere, ball-bundle, and figure-eight constructions. |
| [`Regina.Skeleton`](Regina/Skeleton.agda) | The transitive quotient of local vertices, edges, and higher proper faces under facet gluings. |
| [`Regina.All`](Regina/All.agda) | Aggregate checker for implementation and reduction tests. |

`SOURCE-MAP.tsv` maps the first slice to Regina's C++ source.
`SKELETON-SOURCE-MAP.tsv` maps the lower-dimensional face quotient.

## Gluings

A facet is named by the opposite local vertex. A gluing stores a destination
simplex and a permutation of every local vertex label. The image of the
opposite vertex names the destination facet. The reverse adjacency stores the
inverse permutation.

For Regina's three-dimensional ball bundle, facet 0 and facet 3 of one
tetrahedron are paired by `[3,0,1,2]`; the reverse map is `[1,2,3,0]`.
Different facets of one simplex may be paired. A facet may not be paired with
itself.

Every accepted `Triangulation` carries a `PairingsConsistent` proof. For each
paired facet, the checker establishes that the other side returns to the source
simplex, uses the full inverse vertex map, names a different facet, and carries
the same facet lock.

## Lower-dimensional faces

A local `k`-face is represented by a simplex index and a Boolean characteristic
vector selecting exactly `k+1` local vertices. It can cross a glued facet when
it does not contain that facet's opposite vertex. The gluing permutation moves
the complete selected vertex set into the neighboring simplex.

Finite saturation computes the connected class of each local face. Partitioning
all local faces therefore gives the quotient classes and their degrees. This is
the face-discovery result of Regina's skeleton calculation, without copying its
packed face-number representation.

The reduction tests recover these signatures:

| Construction | vertices | edges | facets |
|---|---:|---:|---:|
| one tetrahedron, `ball 3` | 4 | 6 | 4 |
| two tetrahedra glued by identity, `sphere 3` | 4 | 6 | 4 |
| Regina's 3D ball bundle | 1 | 3 | 3 |
| Regina's figure-eight knot complement | 1 | 2 | 4 |

For the figure-eight triangulation, the single vertex class has degree 8, both
edge classes have degree 6, and all four facet classes have degree 2. These are
combinatorial quotient facts. They are not proofs that a vertex is ideal or
that the triangulation is a manifold.

## What remains outside this translation

The current skeleton slice does not reproduce Regina's embedding order,
canonical face numbering, component orientation, links, link orientability,
bad self-identification detection, real boundary components, or `isValid()`.
It also omits normal surfaces and hypersurfaces, homology, fundamental groups,
Pachner moves, recognition, isomorphism signatures, geometry, GUI code, and
native bindings.

The simplex count is fixed in the Agda type. State changes are immutable
transitions. Packed integers, pointer arrays, mutation notifications, caches,
and Regina's performance characteristics are not translated.

## Check

Target: Agda 2.6.3, builtins only.

```text
agda --safe --without-K --ignore-interfaces --no-libraries --no-default-libraries -i agda agda/Regina/All.agda
```

The aggregate currently checks 10 local modules and 79 concrete reduction
assertions:

- `Regina.PermutationTests`: 16
- `Regina.TriangulationTests`: 48
- `Regina.SkeletonTests`: 15

See [`VERIFICATION.txt`](VERIFICATION.txt) and the branch workflow for the
recorded run.

## Attribution and license

Thank you to **Benjamin A. Burton**—credited as **Ben Burton** in the translated
source headers—for Regina and the translated permutation, triangulation, and
skeleton implementations. Thank you to **Ryan Budney** and **William
Pettersson** for their work on Regina. Thank you to **Richard Rannard** for the
figure-eight construction credited by Regina to chapter 8 of his PhD thesis.

These acknowledgments do not replace Regina's full contributor and citation
records. The translated material follows the repository's existing
GPL-2.0-or-later terms and additional application-store distribution permission.
See [`LICENSE.txt`](../LICENSE.txt).
