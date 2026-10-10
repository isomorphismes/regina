# Explicit vertex-link surfaces and boundary components

This slice translates Regina's concrete three-dimensional vertex links and its
real-versus-ideal boundary decomposition.

Source baseline: `e3a5c7c0e0581706d9e5531b750160b322489950`.

## Explicit vertex links

`Regina.VertexLinkSurface3` creates one link triangle for every
`(tetrahedron, local vertex)` appearance of a global vertex. Each triangle side
is either a boundary edge or an addressed side of the neighboring occurrence,
and the full tetrahedron gluing transports its two endpoint labels.

The implementation checks that every paired side resolves and that the target
side points back to the source. Link corners are labelled by

```text
(global original edge class, endpoint 0 or endpoint 1)
```

so loop edges retain two distinct endpoint roles where required.

The explicit counts are:

| Original triangulation | Per-link `(V,E,F)` | Boundary edges | Euler characteristic |
|---|---|---:|---:|
| one tetrahedron | `(3,3,1)` | 3 | 1 |
| two identity-glued tetrahedra | `(3,3,2)` | 0 | 2 |
| Regina's 3D ball bundle | `(6,9,4)` | 6 | 1 |
| figure-eight knot complement | `(4,12,8)` | 0 | 0 |

## Boundary components

`Regina.Boundary3` constructs real boundary components by partitioning unpaired
global facets through shared global boundary edges. It constructs one ideal
boundary component for each ideal global vertex, using that vertex's explicit
link surface.

The resulting cell structures are:

| Triangulation | Boundary structure |
|---|---|
| `ball 3` | one real component `(4,6,4)`, `χ=2` |
| `sphere 3` | no boundary |
| 3D ball bundle | one real component `(1,3,2)`, `χ=0` |
| figure-eight complement | one ideal component `(4,12,8)`, `χ=0` |

`Regina.BoundaryClassification3` is the next layer. It computes orientation
compatibility across every shared real-boundary edge and derives the first real
component as a sphere and the second as an orientable torus. It also classifies
the figure-eight ideal component as an orientable torus. See
[`BOUNDARY-ORIENTATION.md`](BOUNDARY-ORIENTATION.md).

## Representation differences

Regina builds each vertex link as a `Triangulation<2>` and stores each side map
as a contracted `Perm<3>`. Agda stores explicit source and destination side
addresses plus the transported endpoint labels. Regina stores mutable boundary
component pointers; Agda computes immutable finite connected components.

Exact packed side-permutation serialization and exported per-facet boundary
orientation labels remain outside this slice.

Thank you to Benjamin A. Burton, Ryan Budney, William Pettersson, Richard
Rannard, and the Regina contributors. Licensing follows the repository's
existing `LICENSE.txt`.
