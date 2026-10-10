# Real-boundary orientation and closed-surface classification

`Regina.BoundaryClassification3` continues the dimension-three skeleton
translation by computing the orientability of every real boundary component and
then classifying each connected closed boundary surface from orientability and
Euler characteristic.

Source baseline: `e3a5c7c0e0581706d9e5531b750160b322489950`.
Primary source: `TriangulationBase<dim>::calculateRealBoundary()` in
`engine/triangulation/detail/skeleton-impl.h`.

## What Regina propagates

Regina begins each real boundary component with orientation `+1`. It traverses
boundary facets breadth-first through their shared codimension-two faces. For
every neighboring facet it constructs the induced facet gluing. A positive
permutation sign reverses the neighboring orientation; a negative sign
preserves it. Reaching an already-labelled facet with the opposite required
orientation marks the component nonorientable.

The Agda translation expresses the same compatibility condition edge by edge.

## Directed boundary edges

Take an ordered boundary triangle `[v0,v1,v2]`. Its canonical induced edge
directions are

```text
(v1,v2), (v2,v0), (v0,v1).
```

Every local edge belongs to a global edge class. Earlier translation work gives
that global edge an ordered pair of endpoints, numbered `0` and `1`. Therefore
each boundary-triangle side receives:

- its boundary facet number;
- its local side number;
- its global edge-class number;
- whether its canonical direction is endpoint `0 → 1` or `1 → 0`.

No arbitrary integer fallback is admitted. If either endpoint cannot be found
in the ordered global-edge embedding, the orientation data for the component is
reported as unresolved.

## Compatibility across a shared edge

Two oriented triangles induce opposite directions on their common edge. Thus:

- when the two canonical side directions agree, the neighboring triangle sign
  must flip;
- when the canonical directions disagree, the neighboring sign is preserved.

The implementation builds a finite graph whose vertices are

```text
(boundary facet, positive | negative).
```

Starting from a positive root, it closes under the compatibility rule. A
boundary facet reachable with both signs witnesses a conflicting return and
therefore nonorientability.

Before returning an orientation result, the implementation checks:

1. every boundary facet contributes exactly three resolved sides;
2. every resolved global boundary edge occurs exactly twice;
3. the total number of side occurrences is three times the number of boundary
   triangles.

If any check fails, orientation remains explicitly uncomputed instead of being
reported as false.

## Closed-surface classification

For a connected closed surface with computed orientation:

- orientable surfaces satisfy `χ = 2 - 2g`;
- nonorientable surfaces satisfy `χ = 2 - k`.

The Agda result type is:

```text
orientable_genus g
nonorientable_genus k
unclassified_surface
```

Classification remains `unclassified_surface` when orientation is unresolved,
when the orientable Euler deficit is odd, or when the supplied Euler
characteristic does not describe a closed surface of the stated kind.

## Checked examples

| Construction | Real or ideal | Cell data | Derived type |
|---|---|---|---|
| one tetrahedron, `ball 3` | real | `(4,6,4)`, `χ=2` | orientable genus 0 sphere |
| `sphere 3` | none | no boundary | no surface |
| Regina's 3D ball bundle | real | `(1,3,2)`, `χ=0` | orientable genus 1 torus |
| figure-eight complement | ideal | `(4,12,8)`, `χ=0` | orientable genus 1 torus |

The ball-bundle torus is now derived inside Agda from explicit orientation
compatibility and Euler characteristic; it is no longer merely copied from the
source description.

The reduction tests also check the abstract classifications of a sphere, torus,
and Klein bottle, and verify that unresolved orientation never receives a
surface name.

## Representation boundary

Regina stores one mutable orientation integer per boundary facet during a BFS.
Agda stores no mutation and no distinguished spanning tree: it computes finite
reachability in the doubled orientation graph. The two descriptions enforce the
same local compatibility condition.

The module reports component orientability and surface type. It does not yet
export a selected orientation label for every individual boundary facet, nor
does it serialize the exact facet-gluing permutations that Regina constructs
internally.

Thank you to Benjamin A. Burton, Ryan Budney, William Pettersson, Richard
Rannard, and the Regina contributors. Licensing follows the repository's
existing `LICENSE.txt`.
