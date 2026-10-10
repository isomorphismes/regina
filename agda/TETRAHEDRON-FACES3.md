# Tetrahedron face lookup and mappings

`Regina.TetrahedronFaces3` translates the dimension-three part of Regina's
`Simplex::face()` and `Simplex::faceMapping()` interface. In dimension three the
top-dimensional simplex is a tetrahedron, and the translated operations are:

```text
tetrahedron -> vertex
tetrahedron -> edge
tetrahedron -> triangle
```

Source baseline: `e3a5c7c0e0581706d9e5531b750160b322489950`.
Primary sources:

- `engine/triangulation/simplex.h` for `face()`, the dimension-specific aliases,
  and `faceMapping()`;
- `engine/triangulation/facenumbering.h` for the standard three-dimensional
  vertex, edge, and triangle numbering conventions.

## Returned reference

A `TetrahedronFaceReference3` contains:

- the face dimension;
- the global face-class number;
- a certified `Permutation 4` mapping the global face's inherent vertex labels
  into the local tetrahedron vertex labels.

The source documents `Simplex::faceMapping()` as the same permutation returned
by the corresponding `FaceEmbedding::vertices()`. The Agda implementation uses
exactly the ordered embedding already calculated by `Regina.FaceLinks`; it does
not create a second mapping convention.

The first `faceDimension + 1` images are the active face mapping. They are the
images whose semantics Regina specifies directly. The remaining images encode
the translated complementary orientation convention inherited from the face
embedding. For triangles, all four images are fixed by the face and therefore
the complete mappings can be compared directly with Regina's standard
three-dimensional ordering.

## Local numbering

Tetrahedron vertices are numbered `0,1,2,3`.

Edges use Regina's public three-dimensional table:

| edge | endpoints |
|---:|---|
| 0 | 0,1 |
| 1 | 0,2 |
| 2 | 0,3 |
| 3 | 1,2 |
| 4 | 1,3 |
| 5 | 2,3 |

Triangles are numbered by opposite vertex:

| triangle | vertices |
|---:|---|
| 0 | 1,2,3 |
| 1 | 0,2,3 |
| 2 | 0,1,3 |
| 3 | 0,1,2 |

For the one-tetrahedron ball, the complete triangle mappings reduce to:

```text
triangle 0 -> [1,2,3,0]
triangle 1 -> [0,2,3,1]
triangle 2 -> [0,1,3,2]
triangle 3 -> [0,1,2,3]
```

The edge active images reduce to the six endpoint rows in the edge table above.

## Lookup algorithm

For a requested tetrahedron and local face number, the translation:

1. checks the tetrahedron and face indices;
2. constructs the local selected-vertex mask using Regina's numbering table;
3. searches the already translated global face classes for that local
   occurrence;
4. returns the global class number and that occurrence's ordered embedding as a
   checked `Perm<4>`.

Out-of-range tetrahedron, vertex, edge, or triangle numbers return `nothing`.
No default face or identity map is substituted.

The public entry points are:

```text
tetrahedronVertexReference
tetrahedronEdgeReference
tetrahedronTriangleReference
```

with row and all-tetrahedron variants for finite table inspection.

## Cross-layer checks

This slice is checked against independent translated structures instead of only
checking hand-written examples.

### Active images select the requested local face

For every tetrahedron in each checked triangulation:

- every vertex mapping selects the requested local vertex;
- every edge mapping selects the requested edge endpoints;
- every triangle mapping selects the requested three vertices.

### Local occurrences recover global degrees

Counting how often each global vertex, edge, or triangle is returned across all
tetrahedra reproduces the corresponding global face degree from
`Regina.FaceLinks`.

For the figure-eight triangulation this gives:

```text
vertex degrees   [8]
edge degrees     [6,6]
triangle degrees [2,2,2,2]
```

Thus the simplex-local face tables and the independently constructed global
face quotient agree exactly.

### Facet mappings commute with gluings

For every paired tetrahedron facet, let `p` be the facet gluing permutation.
The source triangle reference and destination triangle reference must:

- name the same global triangle class;
- have active images related by applying `p` to the source active images.

`allFacetMappingsCompatible` exhaustively checks this equation for every facet
of every tetrahedron. Boundary facets pass vacuously because no second
occurrence exists across them.

### Identity-glued sphere

The two tetrahedra of `sphere 3` have equal vertex, edge, and triangle
face-class tables because every corresponding facet is glued by the identity.
This is checked independently of the general gluing equation.

## Relation to the previous subface slice

`Regina.SubfaceIncidence3` starts with a global edge or triangle and asks for one
of its lower-dimensional faces. `Regina.TetrahedronFaces3` starts with a local
face number in a tetrahedron and asks which global face it represents.
Together they cover the useful dimension-three incidence directions:

```text
tetrahedron -> triangle -> edge -> vertex
tetrahedron -> edge -> vertex
tetrahedron -> vertex
```

Both layers retain inherent-label mappings, so loop edges and repeated global
vertices do not erase local endpoint or corner roles.

## Verification scope

`Regina.TetrahedronFaceTests` contains 13 reduction assertions covering:

- complete lookup, active mappings, incidence-degree agreement, and facet
  compatibility for the ball, sphere, ball bundle, and figure-eight examples;
- exact ball vertex, edge, and triangle class tables;
- exact complete triangle mappings and edge active images;
- identity-gluing agreement between the sphere's two tetrahedra;
- fail-closed invalid indices;
- explicit ball and figure-eight incidence-degree tables.

The translation is specific to dimension three. It does not yet provide the
generic `Simplex<dim>::face<subdim>()` family, higher-dimensional numbering
tables, mutable C++ face pointers, or Regina's cache and notification behavior.

Thank you to Benjamin A. Burton, Ryan Budney, William Pettersson, Richard
Rannard, and the Regina contributors. Licensing follows the repository's
existing `LICENSE.txt`.
