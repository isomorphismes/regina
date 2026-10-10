# Dimension-three face properties

`Regina.FaceProperties3` presents the translated dimension-three skeleton using
observations modelled on Regina's public `Face<3,subdim>` API.

Source baseline: `e3a5c7c0e0581706d9e5531b750160b322489950`.
Primary source: `engine/triangulation/face.h`, together with the already
translated skeleton, link, boundary, and dual-forest calculations.

## Exact invalidity bits

Regina stores a bitwise combination of three private `Validity` constants:

```text
VALID                  = 0
INVALID_IDENTIFICATION = 1
INVALID_LINK           = 2
```

The Agda `FaceInvalidityBits` record stores the two failure propositions
separately and `faceInvalidityCode` reproduces codes `0`, `1`, `2`, and `3`.
The following observations have the source meanings:

- `faceValidityValue`: neither failure bit is set;
- `faceHasBadIdentification`: the face returns to itself under a non-identity
  permutation;
- `faceHasBadLink`: the link fails the standard-dimension link condition.

This is an exact translation of the values and Boolean semantics, not the
mutable C++ storage location or cache lifetime.

## Shared face observations

`FaceCoreProperties3` records, for a global vertex, edge, or triangle:

- face dimension;
- face-class number;
- degree, meaning number of local simplex appearances;
- link orientability;
- whether the face belongs to a real boundary facet;
- `isBoundary`;
- `isInternal`;
- invalidity bits.

The source distinction between `isBoundary()` and `isLinkClosed()` matters.
Ideal and invalid vertices are considered boundary vertices, even when their
links are closed. `isInternal()` is valid and not boundary.

## Vertex properties

`VertexProperties3` adds:

- `vertex_link_closed`;
- `vertex_is_ideal`;
- `vertex_is_standard`;
- link Euler characteristic;
- a normalised ideal/real-boundary bit code.

The two normalised flag values are:

```text
ideal         = 1
real boundary = 2
```

These numbers come from Regina's `VertexFlags` enum. At the pinned C++ revision,
its physical `vertexFlags_` field is instantiated only for vertices in dimension
four. In dimension three Regina exposes the same logical distinctions through
`isIdeal()`, `isBoundary()`, the link Euler characteristic, and skeleton data.
The Agda code therefore uses the enum values as a compact public observation; it
does not claim that a 3D C++ face contains this exact field.

Checked vertex behaviour:

| Example | Boundary | Link closed | Ideal | Standard | Link Euler characteristic |
|---|---:|---:|---:|---:|---:|
| each ball vertex | yes | no | no | yes | 1 |
| each sphere vertex | no | yes | no | yes | 2 |
| ball-bundle vertex | yes | no | no | yes | 1 |
| figure-eight vertex | yes | yes | yes | yes | 0 |

The figure-eight row demonstrates that `isBoundary()` is not the negation of
`isLinkClosed()`.

## Edge properties

`EdgeProperties3` records the shared face observations and whether the
one-dimensional link is closed. The one-tetrahedron ball has six degree-one
boundary edges. The two-tetrahedron sphere has six degree-two internal edges.

A deliberately reversed edge receives invalidity code `1`, exactly the
`INVALID_IDENTIFICATION` bit. No invalid-link bit is invented for this case.

A separate malformed fixture produces a real-boundary vertex whose link Euler
characteristic is not one; its vertex record carries the `INVALID_LINK` bit.

## Triangles and the dual forest

`TriangleProperties3` records shared face properties and whether the global
triangle represents an edge of Regina's chosen maximal forest in the dual
1-skeleton.

The computation maps each local triangle to its opposite tetrahedron vertex,
then asks whether that facet is one of the explicitly translated forest facets.
Because both sides of a chosen dual edge are marked, the answer is independent
of which triangle embedding is inspected.

Checked counts:

- `ball 3`: four boundary triangles, none in the forest;
- `sphere 3`: no boundary triangles, one global triangle in the forest;
- figure-eight triangulation: one global triangle in the forest.

## Test coverage

`Regina.FacePropertyTests` contains 13 reduction assertions covering:

- all four invalidity codes;
- all four normalised ideal/real-boundary codes;
- ball, sphere, ball-bundle, and figure-eight vertex properties;
- ball and sphere edge degrees and boundary status;
- the invalid-identification bit on a reversed edge;
- the invalid-link bit on a malformed real-boundary vertex;
- boundary-triangle and dual-forest counts.

## Representation boundary

This module is a finite immutable report over the translated skeleton. It does
not reproduce:

- C++ face-object pointer identity or lifetime;
- mutable cached fields and invalidation notifications;
- component and boundary-component pointers;
- exact codimension-two appearance order;
- subface lookup and `faceMapping()` APIs;
- triangle combinatorial-type recognition;
- dimension-four or higher-dimensional face specialisations.

Thank you to Benjamin A. Burton, Ryan Budney, William Pettersson, Richard
Rannard, and the Regina contributors. Licensing follows the repository's
existing `LICENSE.txt`.
