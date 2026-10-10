# Three-dimensional validity and reconstruction completeness

`Regina.Validity3` gives a source-shaped, reasoned account of the validity
checks performed during Regina's three-dimensional skeleton calculation. It
also reports whether the richer immutable Agda reconstructions—tetrahedron face
tables, explicit vertex links, and real-boundary orientations—completed without
an unresolved incidence.

Source baseline: `e3a5c7c0e0581706d9e5531b750160b322489950`.

## Regina's three-dimensional validity checks

The general Regina documentation describes two kinds of face failure:

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
- tetrahedron face-table and mapping completeness;
- explicit vertex-link analysis completeness;
- real-boundary orientation-assignment completeness;
- a list of named invalidity reasons.

The completeness fields are not included in mathematical validity. They report
whether richer translated structures were reconstructed in full.

### Tetrahedron face-table completeness

`report_tetrahedron_face_mappings_complete` requires all of the following:

1. every tetrahedron vertex, edge, and triangle lookup resolves;
2. each active mapping prefix selects the requested local face;
3. occurrence counts from all tetrahedron tables equal the global face degrees;
4. every paired-facet triangle mapping commutes with its gluing permutation.

This field connects Regina's simplex-local `face()` and `faceMapping()` tables
to the independently translated global skeleton. It remains separate from
`report_validity_value`: an incomplete translation report must not silently
change the mathematical predicate being translated.

### Explicit link and boundary completeness

The explicit-link field requires every link corner and side address to resolve
and every paired side to be reciprocal. The boundary-orientation field requires
every real-boundary facet to receive one unique sign after the incidence checks
pass.

## Concrete boundary-facet labels

`Regina.BoundaryLabels3` chooses Regina's positive root convention and exports
one status for every real-boundary facet:

- `boundary_facet_positive`;
- `boundary_facet_negative`;
- `boundary_facet_conflicting` when both signs are reachable;
- `boundary_facet_unreachable` when the incidence data is unresolved.

The checked ball boundary assigns four facets, and the ball-bundle boundary
assigns two. Both assignments are complete, rooted positively, orientable, and
conflict-free. Closed and ideal-only examples have no real-boundary assignment.

## Checked reports

| Triangulation | Valid | Orientable | Ideal | Standard | Tetrahedron tables | Explicit links | Boundary signs |
|---|---:|---:|---:|---:|---:|---:|---:|
| one tetrahedron | yes | yes | no | yes | complete | complete | complete |
| two identity-glued tetrahedra | yes | yes | no | yes | complete | complete | complete |
| 3D ball bundle | yes | yes | no | yes | complete | complete | complete |
| figure-eight complement | yes | yes | yes | yes | complete | complete | complete |

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
