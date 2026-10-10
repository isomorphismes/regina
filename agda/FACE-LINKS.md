# Face-link orientation and three-dimensional vertex links

This slice continues the Agda translation of Regina's skeleton calculation in
two stages:

1. orientation-normalised return maps for every proper face;
2. Regina's three-dimensional vertex-link Euler-characteristic calculation.

Source baseline: `e3a5c7c0e0581706d9e5531b750160b322489950`.

## Orientation-normalised face traversal

`Regina.FaceLinks` starts from the ordered local appearances in
`Regina.Embeddings`, but follows the extra convention used by Regina's skeleton
code. Before a face of codimension at least two crosses a glued facet, the last
two positions of its complete vertex ordering are swapped. The gluing
permutation is then applied to every position.

This is the list form of Regina's

```text
adjacentGluing * currentMapping * swap(dim-1, dim)
```

and preserves the chosen orientation of the complementary simplex in the
face's link.

A return to an already visited local face is interpreted according to its
codimension:

- **Codimension one:** no additional return-map test is required.
- **Codimension two:** in dimensions above two, the complete ordered map must
  agree. A difference is a bad identification. The link is a path or loop and
  is orientable as a one-dimensional manifold.
- **Codimension greater than two:** the first `faceDimension + 1` positions
  must agree, or the face has a non-trivial self-identification. Independently,
  the relative permutation of the complementary positions must be even, or the
  face link is nonorientable.

This separation matters. A return can fix the face itself while reversing its
link, or it can permute the face vertices while preserving link orientation.
The implementation records these as different facts.

The deliberately malformed one-tetrahedron gluing `[1,0,3,2]` returns the edge
`{2,3}` as `{3,2}`. The codimension-two full-return rule detects the reversed
edge, while its one-dimensional link remains orientable.

A second gluing, `[1,3,2,0]`, fixes local vertex `2` but reverses the
complementary triangle after orientation normalisation. Agda reports a
nonorientable vertex link without reporting a bad vertex identification.

## Exact edge-link order

`Regina.FaceLinks` deliberately computes face classes by finite closure; its
class membership and invalidity flags are independent of any special list
order. Regina's C++ skeleton uses a more specific algorithm for codimension-two
faces: the edge link is walked in both directions, forward appearances are
appended, and backward appearances are prepended.

That exact dimension-three path-or-cycle order is now translated in
[`Regina.ExactEdgeLinks3`](Regina/ExactEdgeLinks3.agda). It uses Regina's six
hard-coded edge orderings, retains directed path endpoints, and independently
matches every exact class against the generic `FaceLinkClass`. See
[`EDGE-LINK-ORDER3.md`](EDGE-LINK-ORDER3.md).

## Three-dimensional Euler data

`Regina.Link3` translates `Triangulation<3>::calculateVertexLinks()` without
requiring the later explicit triangle-complex representation.

For each global edge class, Regina contributes to the links of its endpoints:

- a boundary edge contributes `1`;
- an interior edge contributes `2`;
- a valid edge contributes at both endpoints;
- an invalid edge contributes only at the first endpoint, avoiding a false
  double count when an edge is identified with itself in reverse.

For a global vertex with tetrahedron-vertex degree `f`, the source computes

```text
chi(link) = (2 * interior_link_vertices + boundary_link_vertices - f) / 2
```

The Agda code performs the same finite incidence calculation. It records a
small signed integer Euler characteristic and verifies that the numerator is
even before classifying the link.

The classifications follow Regina's three-dimensional skeleton logic:

- a boundary vertex with Euler characteristic `1` has a real-boundary disc
  link;
- a boundary vertex with any other Euler characteristic has an invalid link;
- a non-boundary vertex with Euler characteristic `2` is finite, with a
  2-sphere link;
- any other non-boundary vertex is ideal;
- an ideal vertex with Euler characteristic `0` is standard; other ideal Euler
  characteristics make the triangulation non-standard.

Link orientability is retained separately. A nonorientable closed ideal link
can be meaningful and is not automatically collapsed into the bad-face
identification flag.

## Checked examples

| Construction | Vertex-link result | Agda flags |
|---|---|---|
| One tetrahedron, `ball 3` | Four orientable discs, each degree 1 and Euler characteristic 1 | valid, non-ideal, standard |
| Two identity-glued tetrahedra, `sphere 3` | Four orientable 2-spheres, each degree 2 and Euler characteristic 2 | valid, non-ideal, standard |
| Regina's 3D ball bundle | One orientable disc, degree 4 and Euler characteristic 1 | valid, non-ideal, standard |
| Figure-eight knot complement | One orientable closed link, degree 8 and Euler characteristic 0 | valid, ideal, standard |
| Reversed-edge fixture | Codimension-two bad identification | invalid |
| Complement-reversal fixture | A nonorientable vertex link with no bad vertex identification | both facts remain distinct |

The complete source-shaped dimension-three validity report is now provided by
`Regina.Validity3`. Explicit vertex-link triangle surfaces and real and ideal
boundary components are supplied by later modules.

## Exported observations

`Regina.FaceLinks` exports:

- `faceLinkClasses`
- `faceLinkClassDegrees`
- `badIdentificationCount`
- `nonorientableFaceLinkCount`
- `hasBadIdentification`
- `allFaceLinksOrientable`

`Regina.Link3` exports:

- `threeDimensionalVertexLinkSummaries`
- `threeDimensionalHasInvalidVertexLink`
- `threeDimensionalIsIdeal`
- `threeDimensionalIsStandard`
- `threeDimensionalHasBadIdentification`
- `threeDimensionalLocallyValid`

`Regina.ExactEdgeLinks3` adds source-ordered codimension-two paths and cycles,
directed path boundaries, exact seed order, and exact complete edge mappings.

## Module boundary

This module's orientation-return test is dimension-generic, while the Euler
calculation is specific to dimension three. Explicit link surfaces, boundary
components, exact edge order, face properties, and the source-shaped validity
report are intentionally separated into later modules so each layer can be
checked independently.

Still outside the whole branch are higher-dimensional link-manifold recognition,
generic exact codimension-two order in arbitrary dimensions, and the complete
all-dimensional Regina API.

Thank you to Benjamin A. Burton, Ryan Budney, William Pettersson, Richard
Rannard, and the Regina contributors. Licensing follows the repository's
existing `LICENSE.txt`.
