# Printable second-generation signatures in dimension three

This slice translates Regina's printable second-generation signature reader
from source baseline
`e3a5c7c0e0581706d9e5531b750160b322489950`.

`Regina.SecondGenerationSignature3` reads each base64 character from its least
significant bit upward. It enforces the `11` generation marker, zero padding at
character boundaries, component sizes, the orientation flag, type-A/type-B
facet masks, destination simplex numbers, sign-ordered `Perm<4>` indices, and
the optional lock suffix.

Type-A facets discover the next tetrahedron and use Regina's `(0,1)` swap.
Type-B facets are either boundary facets or joins to an already discovered
tetrahedron. Reconstruction uses the existing certified immutable `join`, so
every accepted result again carries reciprocal adjacency, inverse-permutation,
distinct-facet, and paired-lock proofs. Multiple components are combined with
the checked disjoint-union path.

For oriented data, the reader expands each four-bit stored permutation number
to the odd five-bit `S4` index. Regina's sign ordering differs from
lexicographic order by the adjacent swaps `2 <-> 3`, `6 <-> 7`, and so on;
the reader performs that conversion before constructing the checked Agda
permutation.

The reduction fixtures cover the canonical one-tetrahedron ball encoding
`b-F`, disconnected components, the source's figure-eight encoding `cV6cqb`,
its locked form `cV6cqb.ai`, and a nine-tetrahedron nonorientable encoding.
The figure-eight result converts to the classical source oracle
`cPcbbbiht`. Malformed markers, truncated streams, invalid characters, and
nonzero padding are rejected.

This is the printable three-dimensional reconstruction path. It does not yet
implement canonical `neoSig()` generation, ridge-degree pruning, the binary
byte encoding, printable conversion of binary signatures, or readers in other
dimensions. The fixtures are comparisons with pinned source strings, not a
fresh C++ differential run or a performance-equivalence claim.
