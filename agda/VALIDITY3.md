# Three-dimensional validity and boundary-facet labels

`Regina.Validity3` gives a source-shaped, reasoned account of the validity
checks performed during Regina's three-dimensional skeleton calculation.
`Regina.BoundaryLabels3` exposes the concrete facet orientations that the
preceding boundary-orientation work had used only internally.

Source baseline: `e3a5c7c0e0581706d9e5531b750160b322489950`.

## Regina's three-dimensional validity checks

The general Regina documentation describes two kinds of failure:

1. a face is identified with itself under a non-identity permutation;
2. a face has an inappropriate link.

At the pinned source revision, the dimension-three skeleton specializes these
rules as follows.

### Reciprocal facet data

`Triangulation<3>::checkPermutations()` checks both directions of every paired
tetrahedron facet. The neighboring tetrahedron must point back, and the product
of the two gluing permutations must be the identity.

The Agda `Triangulation` type already stores a `PairingsConsistent` witness.
`facetPairingsValid` nevertheless reruns the executable finite checker so the
validity report exposes the corresponding Boolean observation.

### Edge self-identifications

A codimension-two face in dimension three is an edge. Regina walks the edge
link in both directions. Returning to an already visited local edge with a
different complete ordering means that the edge has been identified with itself
under a non-identity permutation; the usual example is an edge reversed end for
end.

`edgeIdentificationsValid` negates the translated codimension-two
`hasBadIdentification` result. The invalidity reason is
`reversed_edge_identification`.

### Vertex links

For every global vertex, Regina computes

```text
chi(link) = (2 * interior_link_vertices + boundary_link_vertices
             - tetrahedron_vertex_degree) / 2.
```

A vertex belonging to a real boundary facet must have Euler characteristic `1`,
which is the disc-link case. Any other value gives the reason
`invalid_real_boundary_vertex_link`.

For a vertex not belonging to real boundary:

- Euler characteristic `2` gives a finite vertex with a 2-sphere link;
- any other value gives an ideal vertex.

The latter remains valid: in dimension three, an interior vertex is allowed to
have any closed 2-manifold as its link. Regina's separate `standard` flag is
true only when every ideal vertex link has Euler characteristic `0`.

## The report

`ThreeDimensionalValidityReport` contains:

- the reciprocal-pairing result;
- the edge-identification result;
- the real-boundary vertex-link result;
- the conjunction used as the three-dimensional validity value;
- triangulation orientability;
- ideal and standard flags;
- explicit vertex-link analysis completeness;
- real-boundary orientation-assignment completeness;
- a list of named invalidity reasons.

The additional completeness fields are not smuggled into mathematical
validity. They report whether the richer Agda representations—explicit link
corners and side addresses, reciprocal link-side pairings, and concrete
boundary-facet signs—were fully reconstructed.

## Concrete boundary-facet labels

Regina's real-boundary BFS stores one integer orientation on every boundary
facet. Agda previously used the equivalent doubled graph only to decide whether
a component was orientable.

`Regina.BoundaryLabels3` now chooses the same positive root convention and
exports one status for every facet:

- `boundary_facet_positive`;
- `boundary_facet_negative`;
- `boundary_facet_conflicting` when both signs are reachable;
- `boundary_facet_unreachable` when the incidence data is unresolved.

An assignment is complete only when all facet signs are unique. The checked
ball boundary assigns four facets, and the ball-bundle boundary assigns two;
both assignments are complete, rooted positively, orientable, and
conflict-free. Closed and ideal-only examples have no real-boundary assignment.

## Checked reports

| Triangulation | Valid | Orientable | Ideal | Standard | Extra analyses complete |
|---|---:|---:|---:|---:|---:|
| one tetrahedron | yes | yes | no | yes | yes |
| two identity-glued tetrahedra | yes | yes | no | yes | yes |
| 3D ball bundle | yes | yes | no | yes | yes |
| figure-eight complement | yes | yes | yes | yes | yes |

The reversed-edge fixture fails validity and contains the explicit reason
`reversed_edge_identification`.

## Claim boundary

The report matches the validity-setting checks translated from the pinned
three-dimensional skeleton sources. It does not reproduce Regina's mutable
cache, C++ pointer graph, face-object `whyInvalid()` storage layout, or exception
and notification behavior. It also does not generalize this result to
`Triangulation<dim>::isValid()` in dimensions two, four, or higher.

Thank you to Benjamin A. Burton, Ryan Budney, William Pettersson, Richard
Rannard, and the Regina contributors. Licensing follows the repository's
existing `LICENSE.txt`.
