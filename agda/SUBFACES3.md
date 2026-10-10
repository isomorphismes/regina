# Dimension-three subfaces and inherent-vertex mappings

`Regina.SubfaceIncidence3` translates the useful dimension-three part of
Regina's `Face::face()` and `Face::faceMapping()` interface.

Source baseline: `e3a5c7c0e0581706d9e5531b750160b322489950`.
Primary source: `engine/triangulation/face.h`, together with the translated
face classes and ordered embeddings.

## Returned data

A `SubfaceReference3` contains:

- the lower face dimension;
- the global lower-face class number;
- a certified `Permutation 4`.

The first `lowerFaceDimension + 1` images of the permutation have Regina's
`faceMapping()` meaning: they map the lower face's inherent vertex labels into
the inherent vertex labels of the containing face.

For example, an edge endpoint reference has one active image. An endpoint may
map to position `0` or position `1` of the containing edge. A triangle-edge
reference has two active images, locating the two inherent vertices of the
edge inside the triangle.

Regina leaves the unused images of a face mapping unspecified. Agda completes
the active images to a full `Perm<4>` deterministically by appending the unused
positions in increasing order. Only the active prefix carries subface meaning;
the deterministic completion exists so every returned map is a genuine checked
permutation rather than an unchecked partial table.

## Supported fixed-dimension API

The module currently provides:

```text
edgeVertexReference
triangleVertexReference
triangleEdgeReference
```

and the corresponding complete rows:

```text
edgeVertexReferences
triangleVertexReferences
triangleEdgeReferences
```

The inherent numbering follows Regina's standard face convention:

- edge vertices are `0` and `1`;
- triangle vertices are `0`, `1`, and `2`;
- triangle edge `0` is opposite triangle vertex `0`, so it uses vertices
  `{1,2}`;
- triangle edge `1` uses `{0,2}`;
- triangle edge `2` uses `{0,1}`.

A lookup begins with one ordered representative occurrence of the containing
global face. It selects the requested local vertex subset, finds the global
lower-face class containing that local occurrence, and compares the ordered
lower-face vertices with the containing face's ordered vertices. This produces
both the global `face()` result and the active `faceMapping()` images.

## Loop edges

Subface mappings carry information that a bare lower-face pointer cannot.

In the figure-eight knot triangulation, both global edges are loops. Each edge
has the same global vertex class at both ends, but the two endpoint references
remain distinct:

```text
endpoint 0 -> global vertex 0, image 0
endpoint 1 -> global vertex 0, image 1
```

Thus `face(0)` and `face(1)` may return the same global vertex while
`faceMapping(0)` and `faceMapping(1)` still distinguish the two endpoint roles.
This is exactly why the mapping must accompany subface lookup.

## Incidence observations

The module also derives finite incidence tables and containment queries:

```text
edgeContainsVertexClass
triangleContainsVertexClass
triangleContainsEdgeClass
edgeVertexIncidenceCounts
triangleVertexIncidenceCounts
triangleEdgeIncidenceCounts
edgeLoopFlags
```

Incidence counts retain multiplicity. If a loop edge has both endpoints at the
same global vertex, it contributes two endpoint incidences to that vertex.
Likewise, a triangle whose three corners represent one global vertex contributes
three incidences rather than one set-membership event.

Checked examples include:

| Triangulation | Result |
|---|---|
| one tetrahedron | every vertex lies on three edges and three triangles; every edge lies on two triangles |
| two identity-glued tetrahedra | the same global tetrahedral incidence counts |
| figure-eight complement | both global edges are loops; the unique vertex receives four edge-end incidences and twelve triangle-corner incidences; both edges have six triangle incidences |

All edge-to-vertex, triangle-to-vertex, and triangle-to-edge references resolve
for the ball, sphere, ball-bundle, and figure-eight examples. The active mapping
images satisfy the inherent numbering rules above.

## Exact boundary

This slice is intentionally fixed to the public dimension-three combinations
used most often:

- edge to vertex;
- triangle to vertex;
- triangle to edge.

It does not yet implement:

- tetrahedron-to-proper-face lookup as a `Face` method;
- the generic all-dimensional `Face<dim,subdim>::face<lowerdim>()` family;
- exact Regina choices for the semantically unused tail images of
  `faceMapping()`;
- mutable C++ face pointers or cached subface arrays;
- codimension-two appearance order.

Thank you to Benjamin A. Burton, Ryan Budney, William Pettersson, Richard
Rannard, and the Regina contributors. Licensing follows the repository's
existing `LICENSE.txt`.
