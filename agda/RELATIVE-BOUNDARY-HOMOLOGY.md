# Relative and boundary first homology

This slice translates Regina's three-dimensional `homologyRel()` and
`homologyBdry()` results from the source baseline
`e3a5c7c0e0581706d9e5531b750160b322489950`.

## Relative H₁

`Regina.RelativeHomology3` first enforces the translated three-dimensional
validity precondition. A triangulation with no real or ideal boundary follows
Regina's shortcut to ordinary first homology.

For a nonempty boundary, the module constructs the relative primal chain
complex. It removes:

- every real-boundary or ideal vertex from C₀;
- every real-boundary edge from C₁;
- every real-boundary triangle from C₂.

Restricting both boundary matrices to the surviving rows and columns forms
`C*(M) / C*(boundary M)`. The existing certified chain-homology path checks
that the two maps compose to zero, changes to an integral kernel basis, and
computes invariant factors by Smith reduction.

Regina's C++ implementation first collapses a maximal forest rooted separately
at the boundary components and then presents the group using the remaining
edges and internal triangles. The Agda implementation keeps the complete
relative chain complex instead. This preserves the mathematical group while
avoiding a second mutable forest algorithm. The checked examples agree with
the expected groups; a universal Agda theorem equating the two presentations
is not claimed.

## Boundary H₁

`Regina.BoundaryHomology3` follows Regina's direct surface calculation. For
each classified real or ideal boundary component:

- an orientable genus-g surface contributes `Z^(2g)`;
- a nonorientable genus-k surface contributes `Z^(k-1) + Z/2`.

The direct sum over all components is returned. An absent boundary therefore
has trivial H₁. Invalid triangulations and boundary surfaces whose orientation
or genus could not be classified return `nothing` rather than a group.

## Reduction fixtures

`Regina.RelativeBoundaryHomologyTests` checks:

- boundary H₁ for a 3-ball, 3-sphere, solid torus and figure-eight complement;
- the nonorientable closed-surface formula;
- relative H₁ for the same manifold fixtures and `RP2 x S1`;
- the closed-manifold shortcut, empty triangulation, and invalid-input failure.

The aggregate uses Agda safe mode, without K, builtins only. These reductions
do not claim a fresh C++ differential run, a general equivalence proof between
the forest and chain-quotient presentations, or Regina's caching and mutable
object behavior.
