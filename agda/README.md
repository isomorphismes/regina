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
| [`Regina.Triangulation`](Regina/Triangulation.agda) | Dimension-indexed simplices, reciprocal facet gluings, locks, immutable transitions, and consistency certificates. |
| [`Regina.Input`](Regina/Input.agda) | Checked natural-number indices and permutation tables, applied in Regina's failure order. |
| [`Regina.Examples`](Regina/Examples.agda) | Regina's ball, sphere, ball-bundle, and figure-eight constructions. |
| [`Regina.Components`](Regina/Components.agda) | Connected components, simplex counts, boundary-facet counts, permutation parity, and orientability. |
| [`Regina.DualForest`](Regina/DualForest.agda) | Regina's deterministic breadth-first maximal forest in the dual 1-skeleton. |
| [`Regina.Skeleton`](Regina/Skeleton.agda) | Quotient classes of local vertices, edges, and all other proper faces. |
| [`Regina.Embeddings`](Regina/Embeddings.agda) | Ordered local-face appearances and basic non-trivial self-identification detection. |
| [`Regina.FaceLinks`](Regina/FaceLinks.agda) | Orientation-normalised face returns, codimension-specific bad-identification tests, and link orientability. |
| [`Regina.Link3`](Regina/Link3.agda) | Three-dimensional vertex-link Euler characteristics and finite, real-boundary, or ideal classification. |
| [`Regina.VertexLinkSurface3`](Regina/VertexLinkSurface3.agda) | Explicit triangle surfaces for three-dimensional vertex links, with addressed side pairings and endpoint-labelled corners. |
| [`Regina.Boundary3`](Regina/Boundary3.agda) | Real boundary components from unpaired facets and ideal boundary components from explicit vertex links. |
| [`Regina.All`](Regina/All.agda) | Aggregate entry point for all implementation and reduction-test modules. |

Source maps:

- [`SOURCE-MAP.tsv`](SOURCE-MAP.tsv): permutations, gluings, transitions, input, and examples;
- [`COMPONENTS-SOURCE-MAP.tsv`](COMPONENTS-SOURCE-MAP.tsv): components and orientability;
- [`SKELETON-SOURCE-MAP.tsv`](SKELETON-SOURCE-MAP.tsv): lower-dimensional face quotient;
- [`FOREST-EMBEDDINGS-SOURCE-MAP.tsv`](FOREST-EMBEDDINGS-SOURCE-MAP.tsv): dual forest and ordered embeddings;
- [`FACE-LINKS-SOURCE-MAP.tsv`](FACE-LINKS-SOURCE-MAP.tsv): orientation-normalised face links and three-dimensional Euler data;
- [`VERTEX-LINKS-BOUNDARY-SOURCE-MAP.tsv`](VERTEX-LINKS-BOUNDARY-SOURCE-MAP.tsv): explicit vertex-link surfaces and boundary components.

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

## Components, faces, and return maps

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

## Explicit three-dimensional vertex links

`Regina.VertexLinkSurface3` translates the object built by
`Face<3,0>::buildLink()`:

1. Every tetrahedron-vertex occurrence of a global vertex becomes one link
   triangle.
2. Each of its three possible exit facets becomes one triangle side.
3. An unpaired tetrahedron facet becomes a boundary side of the link.
4. A paired tetrahedron facet identifies the side with the corresponding side
   of the triangle belonging to the adjacent tetrahedron-vertex occurrence.
5. The gluing permutation transports both side endpoints.

Each link side stores its source address, optional destination address, and
transported endpoint labels. The checker confirms that every non-boundary side
has a target and that following the target side returns to the original side.

Link triangle corners are labelled by

```text
(global edge class, endpoint 0 or endpoint 1)
```

instead of merely by the global edge class. This distinction is necessary for
loop edges: the two ends of one global edge can represent two different
vertices of the link. The endpoint number comes from the ordered global-edge
embedding, so corner labels retain exactly the endpoint information needed for
the link surface.

The explicit surfaces recover:

| Original triangulation | Link triangles | Link vertices | Link edges | Boundary edges | Euler characteristic |
|---|---:|---:|---:|---:|---:|
| each vertex of `ball 3` | 1 | 3 | 3 | 3 | 1 |
| each vertex of `sphere 3` | 2 | 3 | 3 | 0 | 2 |
| 3D ball-bundle vertex | 4 | 6 | 9 | 6 | 1 |
| figure-eight ideal vertex | 8 | 4 | 12 | 0 | 0 |

Thus the earlier Euler-only observations are now backed by explicit finite
triangle complexes: discs for the ball and ball bundle, 2-spheres for the
sphere example, and an eight-triangle Euler-zero torus link for the figure-eight
triangulation.

## Real and ideal boundary components

`Regina.Boundary3` keeps Regina's two boundary mechanisms distinct.

A **real boundary component** is assembled from global triangle classes whose
tetrahedron facets are unpaired. Two boundary triangles belong to the same
component when they meet along a global boundary edge. Finite closure partitions
the boundary triangles, and each component records its unique global vertices,
global edges, triangles, and Euler characteristic.

An **ideal boundary component** is supplied by each ideal global vertex. Its
cell counts, Euler characteristic, and orientability come directly from the
explicit vertex-link surface.

Checked boundary structures are:

| Triangulation | Boundary result |
|---|---|
| `ball 3` | one real component with `(V,E,F)=(4,6,4)` and `χ=2` |
| `sphere 3` | no boundary components |
| 3D ball bundle | one real component with `(V,E,F)=(1,3,2)` and `χ=0` |
| figure-eight knot complement | one ideal orientable component with `(V,E,F)=(4,12,8)` and `χ=0` |

Real-boundary orientability is not yet calculated. Such components carry an
explicit `boundary_orientation_computed = false`; this is not silently treated
as a mathematical nonorientability result. Ideal-component orientability is
computed from the face-link return maps.

See [`VERTEX-LINKS-BOUNDARY.md`](VERTEX-LINKS-BOUNDARY.md) for the construction
and exact representation boundary.

## Exact boundary

The current work still omits:

- Regina's standard-dimension face-number lookup tables and legacy embedding labels;
- exact codimension-two path/cycle appearance order;
- Regina's exact `Perm<3>` serialization for link-triangle edge gluings;
- orientation propagation across real boundary triangles;
- higher-dimensional link-manifold recognition and bad-link flags;
- the complete `isValid()` implementation;
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

The aggregate checks **24 local modules and 151 concrete reduction
assertions**:

- `Regina.PermutationTests`: 16;
- `Regina.TriangulationTests`: 48;
- `Regina.ComponentTests`: 9;
- `Regina.DualForestTests`: 10;
- `Regina.SkeletonTests`: 15;
- `Regina.EmbeddingTests`: 11;
- `Regina.FaceLinkTests`: 15;
- `Regina.Link3Tests`: 12;
- `Regina.VertexLinkTests`: 8;
- `Regina.BoundaryTests`: 7.

See [`VERIFICATION.txt`](VERIFICATION.txt) and the branch workflow for the
recorded run.

## Attribution and license

Thank you to **Benjamin A. Burton**—credited as **Ben Burton** in the translated
source headers—for Regina and the translated permutation, triangulation,
component, orientation, skeleton, dual-forest, face-embedding, link,
three-dimensional vertex-link, and boundary-component algorithms. Thank you to
**Ryan Budney** and **William Pettersson** for their work on Regina. Thank you to
**Richard Rannard** for the figure-eight construction credited by Regina to
chapter 8 of his PhD thesis.

These acknowledgments do not replace Regina's complete contributor and citation
records. The translated material follows the repository's existing
GPL-2.0-or-later terms and additional application-store distribution permission.
See [`LICENSE.txt`](../LICENSE.txt).
