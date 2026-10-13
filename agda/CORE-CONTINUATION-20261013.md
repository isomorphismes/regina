# Regina Agda core continuation, 2026-10-13

The existing Agda branch was recovered together with the three cumulative
unpublished patches ending in the 69-module mathematical-engine continuation.
This work adds 13 implementation/test modules and 92 reduction assertions.
The full Regina port remains incomplete; the current boundary is listed in
README.md. This continuation does not redefine a full port as complete.

## Triangle reconstruction

Quadrilateral and quadrilateral/octagon coordinates now gain the four triangle
coordinates per tetrahedron. The implementation propagates the source's arc
differences across the connected vertex-link side graph. A vertex with
consistent equations is normalised by subtracting its minimum potential.
Conflicting equations produce infinite triangle coordinates at every
occurrence of that vertex, as in Regina's reconstructTriangles(). Missing
coverage or malformed frames remain failures instead of being called infinity.

Existing full-coordinate input is returned unchanged. Quad and octagon counts
are copied exactly. A separately checked certificate carries proofs of disc
preservation, all extended arc equations, and vertex normalisation. Infinite
counts are explicit, and cannot be converted into a finite surface or assigned
a finite Euler characteristic. This certificate does not make arbitrary
nonmatching reduced input into a valid spun surface: matching and embeddedness
remain separate requirements. The figure-eight fixture exercises all three.

The propagation order is an immutable saturation of vertex-link sides instead
of Regina's mutable depth-first stack of ordered edge ends. On a connected
vertex class, the same difference equations determine potentials up to a
constant; minimum normalisation removes that constant. A general Agda theorem
identifying the two algorithms is not supplied.

## Pachner moves

The four dimension-three moves use Regina's conceptual chamber frames and
its exact movePerm<3,1> and movePerm<3,2> tables. A region must contain the
required number of distinct tetrahedra, with every internal adjacency and
complete vertex map equal to the source pattern. Locked simplices or internal
facets block the move. External facet locks are carried to their replacements.

Replacement tetrahedra appear in the source's reverse creation order. Exterior
gluings, including self-gluings or gluings between two removed chambers, are
transported through both exterior vertex frames. Retained tetrahedra preserve
their order and locks. The resulting whole triangulation is recertified for
reciprocal gluings, inverse permutations, distinct facets, and paired locks.

Tests cover each move size, both inverse pairs, exact ball and solid-torus
1–4–1 pairing-table round trips, face counts, real boundaries, exterior
neighbors, transferred locks, and rejection at boundary faces and locked
internal facets. These are executable instances, not a universal Agda
homeomorphism theorem or a port of every higher-dimensional move.

## Classical signatures and reconstruction

The generic signature walk visits simplices and facets in canonical order.
New simplices receive identity gluings. Already discovered gluings retain
their target index and lexicographic permutation index, and their reverse is
skipped exactly once. Every candidate root and vertex permutation is tried;
each connected component is minimised separately, then component strings are
sorted and concatenated in ASCII order. Locks are relabelled into canonical
facet positions. The lock-free encoding is an explicit choice.

The encoding uses Regina's a..zA..Z0..9+- alphabet, least-significant base64
digits first, and three two-bit facet trits per character. Perm<5> indices take
two characters: four-dimensional fixtures check this distinction. The
figure-eight signature cPcbbbiht agrees with the pinned upstream
python/testsuite/signatures.out fixture. This is comparison with a source
fixture, not a newly executed C++ differential test.

The classical reader reconstructs reciprocal gluings, reads simplex/facet
locks, and combines disconnected components through bounded sum indices. It
rejects illegal actions, nonzero padding, missing input, unseen targets,
out-of-range permutation indices and lock bits, same-facet joins, and
inconsistent locks on paired facets. It accepts surrounding whitespace while
rejecting internal whitespace, following the source decoder. Second-generation
and binary signatures remain separate unfinished formats and are rejected by
this explicitly classical reader.

## Evidence

Agda 2.6.3, builtins only, safe mode and without-K. The aggregate contains 82
local modules and 464 top-level concrete reduction assertions. No postulates,
termination escape, standard library, GHC compilation, native execution,
physical-device claim, or performance-equivalence claim supplies this result.
The immutable reference algorithms retain their explicit resource costs.
General recognition, higher-dimensional manifold links, geometry, and the
other remaining engine families must not inherit PASS from these checks.
