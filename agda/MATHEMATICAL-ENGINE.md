# Regina Agda mathematical-engine continuation

This continuation adds 25 modules and 95 concrete reduction assertions to the
44-module continuation at `89de32fee353ead99aed7eb5615d52b14675fe51`.
It does not complete the entire Regina engine.

## Boundary and vertex links

Real boundaries now contain actual certified `Triangulation 2` values. The
gluing between two boundary triangles follows the two directed ends of their
ordered edge link and uses Regina's five-factor permutation composition. A
successful contraction carries proofs of all retained images and the fixed
fourth image. An unresolved side or nonreciprocal result fails construction.

Vertex links also produce certified triangle triangulations, together with
the tetrahedron and permutation for each inclusion frame. These additions
replace no existing orientation labels or classification reports. The ball's
boundary is a four-triangle sphere; the solid-torus boundary is a two-triangle
torus; the figure-eight ideal vertex has an eight-triangle torus link.

## Integer algebra and homology

Smith reduction tracks `left * original * right = diagonal` and both integral
inverse basis matrices. Its certificate contains actual entrywise equality
proofs for this equation and both orders of both inverse products. A separate
check enforces a nonnegative diagonal, zero off-diagonal entries, and successive
divisibility. The API takes a work bound; exhaustion returns `nothing`, never
a partial normal form. A general sufficient bound and a general unbounded
termination proof are not supplied.

Chain homology first checks that the two boundary maps compose to zero. It
uses the right basis of the first map for the kernel, transports the second
map by its inverse, checks that all nonkernel coordinates vanish, and computes
the abelian presentation on the remaining coordinates. Unit factors are
removed; nonunit factors retain torsion.

The generic primal boundary map follows the source's descending deletion
order and relative orientation signs. The three-dimensional dual boundary
maps use complementary orientation and omit real and ideal boundary faces.
These are intentionally separate results: including the figure-eight ideal
vertex gives a primal compactification with trivial H1, whereas the manifold's
truncated dual complex gives H1 = Z.

| Example | H0 | H1 | H2 | H3 |
|---|---|---|---|---|
| 3-ball | Z | 0 | 0 | 0 |
| 3-sphere | Z | 0 | 0 | Z |
| solid torus | Z | Z | 0 | 0 |
| figure-eight complement | Z | Z | 0 | 0 |
| RP2 × S1 | Z | Z ⊕ Z/2 | Z/2 | 0 |

These are reduction fixtures, not manifold-recognition proofs. Generic primal
fixtures also cover the circle, 2-sphere and 4-sphere. Fundamental-group output
retains the source's dual presentation before its Tietze simplification.

## Normal surfaces

The four implemented systems are Standard, AlmostNormal, Quad and QuadOct.
Full-coordinate systems impose three arc equations per internal triangle;
quad systems impose one oriented equation per internal edge. Repeated entries
from self-gluings accumulate before evaluation.

`embedded` checks the local quad/octagon support. Enumeration additionally
checks the global octagon support. Neither condition says the total octagon
multiplicity is one. Euler characteristic follows the source's edge weights,
arc counts and disc counts when finite triangle coordinates are present.
Quad-only input requires triangle reconstruction before Euler evaluation.

The reference vertex enumerator visits every coordinate support. It rejects
inadmissible supports, reduces their matching matrix, and accepts exactly
one-dimensional kernels with all supported coordinates of one strict sign.
The integral inverse basis makes the resulting ray primitive; returned vectors
carry matching and admissibility checker proofs. Any Smith exhaustion aborts
the whole enumeration.

The fundamental enumerator uses the sum of all primitive admissible rays as
a coordinate bound. An indecomposable point other than a primitive ray can
be expressed using ray coefficients below one: subtracting a ray with a
coefficient at least one would decompose it. Thus the coordinate bound contains
every fundamental point. It enumerates integer points within the bound and
rejects any point with a proper nonzero matching point below it. The difference
also matches and has support contained in the original, so it is admissible.

The polyhedral completeness arguments above are mathematical explanations,
not general Agda theorem proofs. This is exact finite reference code, with
exponential support and integer-point searches, not a performance-equivalent
port of Regina's optimized engines. Fixtures cover all four one-tetrahedron
systems and a cone whose Hilbert basis contains a point between vertex rays.

## Still required for a full port

The subsequent [2026-10-13 continuation](CORE-CONTINUATION-20261013.md)
implements triangle reconstruction with spun/infinite coordinates, all four
three-dimensional Pachner moves, and classical signatures and their reader.
A later continuation reconstructs three-dimensional triangulations from
printable second-generation signatures, including their bit stream, oriented
permutation indices, locks, and disconnected components.
Closed-cusp slope equations, surface topology and cutting/crushing remain
untranslated. A later continuation implements relative and boundary first
homology in dimension three. Still untranslated are normal hypersurfaces,
higher-dimensional links and recognition, higher-dimensional truncated dual
complexes, Tietze simplification,
higher-dimensional Pachner moves, second-generation canonical generation and
binary signatures,
geometric engines, broader serialization, GUI and bindings.
The original source remains pinned to
`e3a5c7c0e0581706d9e5531b750160b322489950`.
