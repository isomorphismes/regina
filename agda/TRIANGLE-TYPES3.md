# Triangle quotient types in dimension three

The vertices and edges of a triangle in a generalized triangulation can be
identified with one another. `Regina.TriangleTypes3` translates Regina's
classification of these identifications, using the already translated
global face classes and inherent subface mappings.

Source baseline: `e3a5c7c0e0581706d9e5531b750160b322489950`.
Primary source: `engine/triangulation/face.h`, lines 2037–2131.

## Recognition

| Edge identifications | Additional condition | Type | Special role |
|---|---|---|---|
| Three distinct edges | Three distinct corners | Triangle | None |
| Three distinct edges | Exactly two corners identified | Scarf | Vertex opposite the identified pair |
| Three distinct edges | All three corners identified | Parachute | None |
| Exactly two edges identified | Their edge mappings have equal signs | Möbius band | Unpaired edge |
| Exactly two edges identified | Opposite signs, with a separate apex | Cone | Unpaired edge |
| Exactly two edges identified | Opposite signs, with every corner identified | Horn | Unpaired edge |
| All three edges identified | Mixed edge-mapping signs | Dunce hat | Exceptional-sign edge |
| All three edges identified | All edge-mapping signs equal | `L(3,1)` spine | None |

Edge `i` is opposite inherent triangle vertex `i`. Mapping signs refer to the
edge's two inherent vertices mapped into triangle positions. They must not
be replaced by the signs of the tetrahedron's facet-gluing permutations.

In dimension three, a triangle-edge `faceMapping()` fixes position 3. Its first
two images specify the edge endpoints, and the only remaining triangle
position specifies its third image. These images uniquely determine the
complete permutation. The existing `triangleEdgeReference` completion therefore
has the full sign Regina uses here, even though unused tails of general
subface mappings remain outside the earlier translation's exact contract.

`classifyTriangleIncidence` accepts three vertex class numbers, three edge
class numbers, and three mapping parities. This pure classifier does not prove
that arbitrary caller-supplied incidence data can occur in a triangulation.

`triangleClassification` derives that input from an actual
`Triangulation 3 simplex_count`. It returns `nothing` on failed lookup or an
incident edge with a reversed self-identification. Regina explicitly leaves
triangle type and subtype undefined in the latter case; the Agda interface
rejects the case instead of choosing an arbitrary answer. Invalid vertices
alone do not block recognition when the required edge data remains defined.

## Result and predicates

`TriangleClassification` has eight constructors. Five carry a `Fin 3` special
role. This representation cannot store Unknown, an out-of-range subtype, or
a special role for a type that lacks one. `triangleTypeCode` reproduces
Regina's integer enumeration. `triangleSubtype` uses `nothing` for the
source's `-1` sentinel and `just` for a bounded position; this inner absence is
distinct from the outer failure of `triangleClassification`.

`formsMobiusBand` holds for Möbius bands, dunce hats, and `L(3,1)` spines.
`formsCone` holds for cones, horns, and dunce hats. These properties overlap.

The implementation preserves the source's cyclic role order 0, 1, 2 and its
branch priority. It computes a fresh pure result instead of using Regina's
mutable type and subtype caches.

## Validation

The 22 new Agda reduction assertions cover all eight types, all three possible
special positions, all eight sign triples when all edges are identified, both
predicates, source enumeration values, subtype absence, absent indices, empty
triangulations, and reversed-edge rejection. The ball, sphere, ball-bundle,
and figure-eight examples exercise the full lookup path through face classes
and mapping signs. Exact derived results include:

| Example | Types in translated triangle-class order |
|---|---|
| Ball | Four ordinary triangles |
| Sphere | Four ordinary triangles |
| Ball bundle | Möbius band, special edge 1; two parachutes |
| Figure-eight complement | Four horns, special edges 2, 1, 0, 1 |

These are computation checks in Agda, grounded in the pinned source algorithm.
No C++ differential run or homeomorphism theorem is claimed. The public lookup
is dimension three; the generic all-dimensional Face interface remains
untranslated. This addition does not translate normal surfaces, homology,
manifold recognition, or the Regina application.

Thank you to Benjamin A. Burton (Ben Burton in the source headers), Ryan Budney,
William Pettersson, Richard Rannard, and the Regina contributors. Licensing
follows the repository's existing GPL-2.0-or-later terms and additional
distribution permission in `LICENSE.txt`.
