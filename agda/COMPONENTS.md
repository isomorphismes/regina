# Components and orientability

`Regina.Components` translates the first stage of Regina's generic skeleton
calculation: connected simplex components, unpaired-facet totals, permutation
parity, and orientation consistency.

Source baseline: `e3a5c7c0e0581706d9e5531b750160b322489950`.
Primary source: `engine/triangulation/detail/skeleton-impl.h`, especially the
component traversal in `TriangulationBase<dim>::calculateSkeleton()`.

## Connected components

The top-dimensional simplices are the vertices of a finite graph. Two are
adjacent when a facet pairing joins them; a self-pairing is a loop. Finite
saturation computes the component of the first remaining simplex, removes it,
and repeats. Since enumeration begins at index zero, each component is rooted
at its smallest simplex index, matching Regina's traversal convention.

The exported observations are:

- `simplexComponents`
- `componentCount`
- `componentSizes`
- `componentBoundaryFacetCounts`

The boundary count totals unpaired top-dimensional facets. It does not identify
real boundary components, ideal boundary components, or links.

## Orientation propagation

Regina gives the smallest-index simplex of each component orientation `+1`.
Across a facet gluing:

- an even vertex permutation reverses the neighboring orientation;
- an odd vertex permutation preserves it.

`permutationEven` computes inversion parity from the complete finite image
table. The translation then constructs the doubled state graph
`(simplex, positive | negative)` and follows the same crossing rule. A component
is orientable when no simplex is reachable from the positive root in both
orientation states.

This formulation checks path consistency directly. It does not expose Regina's
chosen per-simplex orientation labels or construct `dualForest_`.

## Checked cases

| Construction | component sizes | unpaired facets | orientable |
|---|---|---|---|
| three unpaired tetrahedra | `1,1,1` | `4,4,4` | yes, each component |
| two tetrahedra joined once plus one isolated | `2,1` | `6,4` | yes, both components |
| `sphere 3` | `2` | `0` | yes |
| Regina's 3D ball bundle | `1` | `2` | yes |
| Regina's figure-eight example | `2` | `0` | yes |
| one tetrahedron with an even self-return | `1` | `2` | no |

The last case uses the even 3-cycle `[1,2,0,3]` to pair different facets of one
tetrahedron. Crossing the gluing returns to the same simplex with the opposite
orientation, so both orientation states are reachable.

## Boundary of this slice

Component connectivity and orientation consistency do not imply manifold
validity. This module does not calculate links, detect all bad lower-face
identifications, construct real boundary components, or implement `isValid()`.
It also does not reproduce Regina's dual spanning forest.

Thank you to Benjamin A. Burton, Ryan Budney, William Pettersson, and the Regina
contributors. Licensing follows the repository's existing `LICENSE.txt`.
