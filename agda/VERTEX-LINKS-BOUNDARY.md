# Explicit vertex-link surfaces and boundary components

This slice continues the Agda translation of Regina's three-dimensional
skeleton. It replaces the previous Euler-only view of a vertex link with an
explicit finite triangle surface, and then uses these surfaces together with
unpaired facets to construct ideal and real boundary components.

Source baseline: `e3a5c7c0e0581706d9e5531b750160b322489950`.

Primary sources:

- `engine/triangulation/dim3/vertex3.cpp`, especially
  `Face<3,0>::buildLink()`;
- `engine/triangulation/detail/skeleton-impl.h`, especially
  `calculateRealBoundary()`;
- `engine/triangulation/dim3/skeleton.cpp`, especially the classification and
  creation of ideal vertex boundary components;
- `engine/triangulation/boundarycomponent.h` for the public distinction between
  real and ideal boundary components.

## One link triangle per vertex occurrence

Let a global vertex have a finite list of appearances `(tetrahedron, local
vertex)`. Regina creates one two-dimensional triangle for every appearance.
The Agda module `Regina.VertexLinkSurface3` preserves this indexing: the order
of `face_link_embeddings` is the triangle order.

For an occurrence `(T,v)`, the link triangle has one side for each tetrahedron
facet `f ≠ v`.

- If facet `f` is unpaired, this is a boundary edge of the link triangle.
- If facet `f` is glued to another tetrahedron, the side targets the triangle
  belonging to `(adjacent tetrahedron, gluing(v))`.
- The target side is named by `gluing(f)`.
- The two remaining tetrahedron vertices are the endpoints of the link side,
  and the full gluing permutation transports them to the target triangle.

Each side therefore contains enough explicit information to inspect the link
without reconstructing the original tetrahedron gluing:

```text
source triangle number
source exit-facet number
destination triangle and exit-facet address, or boundary
source endpoint labels
transported endpoint labels
```

The implementation verifies two structural conditions by finite reduction:

1. every paired side resolves to an existing target address;
2. looking up that target side returns to the original source address.

This corresponds to Regina's single `join()` call per pair, while retaining both
side descriptions as immutable data.

## Link corners and loop edges

A corner of the vertex-link triangle corresponds to one original tetrahedron
edge incident to the selected vertex. A global original edge can be a loop, so
its two endpoints must not be collapsed merely because they share an edge class.

For this reason, an Agda link-corner label is

```text
(global original edge class number, endpoint number)
```

where the endpoint number is `0` or `1` in the ordered embedding of the global
edge class. Every local corner searches the relevant global edge class and then
asks where the selected tetrahedron vertex occurs in that edge embedding.

Distinct resolved labels are exactly the vertices of the explicit link surface.
This makes the explicit Euler calculation independent of the earlier incidence
shortcut:

```text
link vertices  = number of distinct endpoint-labelled corners
link edges     = boundary sides + paired sides / 2
link triangles = number of vertex occurrences
chi            = vertices - edges + triangles
```

All tested corner labels resolve. No unproved fallback value is counted as a
link vertex.

## Checked explicit surfaces

| Original triangulation | Per-link `(V,E,F)` | Boundary edges | Interpretation supported by the data |
|---|---|---:|---|
| one tetrahedron | `(3,3,1)` | 3 | one triangle disc |
| two identity-glued tetrahedra | `(3,3,2)` | 0 | two-triangle 2-sphere |
| Regina's 3D ball bundle | `(6,9,4)` | 6 | four-triangle disc |
| figure-eight knot complement | `(4,12,8)` | 0 | closed Euler-zero orientable surface |

For the figure-eight link, the explicit calculation returns `4 - 12 + 8 = 0`,
matching the earlier source-style vertex-link formula. Its face-link return maps
also establish orientability, so this is the expected torus cusp link.

## Boundary components

Regina distinguishes real boundary from ideal boundary.

### Real boundary

A real boundary triangle is a global codimension-one face whose tetrahedron
facet is unpaired. Real boundary triangles are adjacent when they share a global
boundary edge. `Regina.Boundary3` computes the finite connected components of
this adjacency relation.

For every component it records:

- the source global facet-class numbers;
- unique global vertex-class numbers;
- unique global edge-class numbers;
- triangle count;
- Euler characteristic `V - E + F`.

This is equivalent to the connectivity part of Regina's ridge-based boundary
traversal. The Agda implementation uses already-calculated global edge classes
instead of mutable per-face boundary-component pointers.

The current slice does not propagate orientations through real boundary
triangles. Each real component explicitly records that orientation was not
computed. This prevents the placeholder Boolean from being confused with a
proved nonorientability result.

### Ideal boundary

Every ideal global vertex contributes one ideal boundary component. Its surface
is the explicit vertex link described above, so its `V`, `E`, `F`, Euler
characteristic, and orientability are all retained.

The figure-eight example therefore has one ideal boundary component with
`(V,E,F)=(4,12,8)`, Euler characteristic zero, and orientable link return maps.
It has no real boundary component because all tetrahedron facets are paired.

## Checked boundary examples

| Triangulation | Real components | Ideal components | Cell data established by Agda |
|---|---:|---:|---|
| `ball 3` | 1 | 0 | closed component `(4,6,4)`, `χ=2` |
| `sphere 3` | 0 | 0 | none |
| 3D ball bundle | 1 | 0 | closed component `(1,3,2)`, `χ=0`; orientation not yet computed |
| figure-eight complement | 0 | 1 | ideal orientable torus `(4,12,8)`, `χ=0` |

Regina describes `ballBundle()` as the higher-dimensional analogue of a layered
solid torus, and in dimension three its intended real boundary is a torus. The
current Agda boundary record establishes the connected closed cell structure
and Euler characteristic but deliberately postpones the orientation calculation
needed to derive that classification internally.

## Representation differences and limits

Regina's link construction produces an actual `Triangulation<2>` and uses
`Perm<3>::contract(...)` for each edge gluing. The Agda surface records the
same source and destination side addresses and explicitly transports the two
endpoint labels. It does not yet package each side map as Regina's exact
three-symbol permutation code.

Regina's real boundary construction stores component pointers on faces and
propagates component orientation. Agda instead performs immutable finite
closure through global edge classes and currently leaves real-boundary
orientation uncomputed.

This slice does not yet provide:

- exact Regina link-triangle edge permutation serialization;
- real-boundary orientation propagation;
- link isomorphism signatures or normal-curve operations;
- higher-dimensional link-manifold recognition;
- the complete `isValid()` contract.

Thank you to Benjamin A. Burton, Ryan Budney, William Pettersson, Richard
Rannard, and the Regina contributors. Licensing follows the repository's
existing `LICENSE.txt`.
