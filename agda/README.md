# Regina's facet-gluing core in Agda

This directory translates Regina's finite permutations, simplex facet gluings,
lock operations, and several original example constructions into executable
Agda definitions. It is a first subsystem of a Regina translation;
normal-surface algorithms and the rest of Regina remain outside this slice.

The source baseline is
[regina-normal/regina at e3a5c7c0e0581706d9e5531b750160b322489950](https://github.com/regina-normal/regina/commit/e3a5c7c0e0581706d9e5531b750160b322489950).
The translation lives on the fork's `Agda` branch. [SOURCE-MAP.tsv](SOURCE-MAP.tsv)
records the original functions, source ranges, and the relationship of each Agda
component to them. The pinned C++ source defines the behavior being translated;
the proofs and checked input boundary make some of its assumptions explicit.

## The mathematical object

Take a finite collection of tetrahedra. Each tetrahedron has four local vertex
labels, `0, 1, 2, 3`, and four triangular facets. Facet `0` is the triangle with
vertices `1, 2, 3`: a facet is named by the vertex opposite it.

A gluing chooses a source facet, a destination tetrahedron, and a permutation
of all four local vertex labels. For example, Regina's three-dimensional ball
bundle glues facet `0` of one tetrahedron to facet `3` of that same tetrahedron
using the images `[3, 0, 1, 2]`:

| Source local label | Image | Meaning |
|---|---|---|
| 0 | 3 | Names the destination facet; these opposite vertices are excluded from the gluing. |
| 1 | 0 | Identifies a vertex of the source triangle with a vertex of the destination triangle. |
| 2 | 1 | Identifies the next pair of triangle vertices. |
| 3 | 2 | Identifies the remaining pair of triangle vertices. |

The reverse direction uses `[1, 2, 3, 0]`. Storing the same permutation on both
sides would be wrong for this example. Two different facets of one simplex may
be paired; pairing one facet with itself is forbidden.

The same description works in dimension `dimension`: each simplex has
`dimension + 1` local vertices and facets. `Facet` stores a simplex index and its
opposite-vertex label. `Gluing` stores the destination simplex and a permutation.
`destination` uses the image of the opposite vertex to locate the other facet.
`cross_facet` maps a vertex across that gluing only when the vertex belongs to
the facet. These conventions follow
[Regina's adjacency contract](https://github.com/regina-normal/regina/blob/e3a5c7c0e0581706d9e5531b750160b322489950/engine/triangulation/simplex.h#L261-L305).

The adjacency table describes Regina's generalized triangulations. Facet
gluings can identify different local vertices and edges, including making loop
edges. A structurally consistent table need not describe a manifold. This
translation does not impose the stronger restrictions of an ordinary
simplicial complex, nor does it derive the full quotient of lower-dimensional
faces. See the
[original triangulation definition](https://github.com/regina-normal/regina/blob/e3a5c7c0e0581706d9e5531b750160b322489950/engine/triangulation/triangulation.h#L4851-L4881).

## Implemented operations

| Component | Behavior |
|---|---|
| `Permutation` | Stores forward and inverse maps with both inverse laws; supplies identity, inverse, composition, conjugation, and comparison by vertex images. Composition preserves Regina's order: `compose left right` applies `right` first. |
| `from_image_list` | Reads exactly the required number of images, checks their bounds, finds inverse candidates, and checks both inverse laws. Callers supply no inverse or proof. |
| `unpaired_simplices` | Creates the specified finite number of simplices, initially with all facets unpaired and all locks clear. |
| `join` | Checks both facets are unpaired, rejects a facet paired with itself, checks both facet locks, then installs forward and inverse adjacency. |
| `unjoin` | Clears both directions and returns the previous neighbor. An already unpaired facet produces `no_change`, even if that boundary facet is locked. |
| `isolate` | Checks every paired facet lock before clearing any pair incident to the chosen simplex. Locked boundary facets remain unchanged. |
| `lock_facet`, `unlock_facet` | Change the lock on both sides of an existing pair. Repeating the current lock setting produces `no_change`. |
| `lock_simplex`, `unlock_simplex` | Change the independent top-dimensional simplex lock. They do not lock or unlock its facets. |
| `from_gluings` | Applies typed gluing specifications in sequence. Each pair is supplied once; duplicate pairs, including reverse duplicates, are rejected. Unmentioned facets stay unpaired. |
| `from_input_gluings` | Checks the dimension and reads ordinary natural-number indices and image lists. Each entry is decoded and applied before the next is examined, preserving the first illegal gluing as the reported failure. |
| `unpaired_facet_count`, `has_boundary_facet` | Inspect unpaired facets, without making a claim about ideal boundary components or manifold recognition. |
| `cross_facet` | Computes one local vertex identification across one facet; it does not compute transitive identifications throughout the triangulation. |

The distinction between simplex locks and facet locks matters. In Regina,
locking a simplex prevents operations such as removing, subdividing, or merging
that simplex; it does not itself forbid changing gluings along unlocked facets.
The translated operations preserve that independence. Their lock and failure
ordering follows the
[original implementation](https://github.com/regina-normal/regina/blob/e3a5c7c0e0581706d9e5531b750160b322489950/engine/triangulation/simplex.h#L1391-L1565).

## What the checker establishes

`RawTriangulation` exposes an adjacency table and independent lock tables.
`PairingsConsistent` states, for every paired source facet, that:

1. The destination facet differs from the source facet.
2. The destination contains a reverse gluing to the original simplex.
3. Its permutation agrees with the inverse of the forward permutation on every
   vertex label, including the labels used to name the facets.
4. Both descriptions of the paired facet have the same lock value.

`dec_pairings_consistent` decides this finite proposition and returns either a
proof or a refutation. `certify` constructs a `Triangulation` only with a proof.
Every accepted public transition contains such a certified result. The raw
constructor and raw setters remain available for deliberately inconsistent
test inputs; they do not supply the proof required by `Triangulation`.

This is an exhaustive certificate for each successful result. The current
development does not separately prove that every operation with satisfied
preconditions must succeed, or a general theorem that every operation preserves
all unrelated entries. Rechecking the resulting table is part of execution.
The mathematical proofs also include permutation injectivity, pointwise group
laws, vertex round trips, preservation of membership in the glued facet, and
the return of the reciprocal facet label. No postulate supplies any of these
witnesses.

`PairingsConsistent` is deliberately separate from Regina's `isValid()`.
Regina also tests lower-dimensional self-identifications and, in standard
dimensions, vertex and face links. Appropriate vertex links can include closed
manifolds other than spheres, accounting for ideal vertices. Those tests are
not translated here. In higher dimensions even Regina's validity criterion has
a more limited scope; see its
[precise validity contract](https://github.com/regina-normal/regina/blob/e3a5c7c0e0581706d9e5531b750160b322489950/engine/triangulation/triangulation.h#L1151-L1187).

## Original examples

`Regina.Examples` translates these constructions from the pinned source:

| Agda example | Construction | Expected unpaired facets |
|---|---|---|
| `ball dimension` | One simplex with no gluings. | `dimension + 1` |
| `sphere dimension` | Two simplices with all corresponding facets glued by identity. | 0 |
| `three_dimensional_ball_bundle` | One tetrahedron with facet 0 paired to facet 3 by `[3, 0, 1, 2]`. | 2 |
| `four_dimensional_ball_bundle` | Two pentachora with facet 0 of each paired to facet 4 of the other by `[4, 0, 1, 2, 3]`. | 6 |
| `figure_eight_knot_complement` | The original four gluing permutations on two tetrahedra. | 0 |

The example names identify Regina's source constructions. The Agda code checks
their permutation and pairing structure; it does not prove the resulting
homeomorphism types. The figure-eight example is an ideal knot complement, so
zero unpaired facets must not be interpreted as a closed manifold.

The ball, sphere, and ball-bundle constructions come from
[detail/example.h](https://github.com/regina-normal/regina/blob/e3a5c7c0e0581706d9e5531b750160b322489950/engine/triangulation/detail/example.h#L228-L350).
The figure-eight construction comes from
[example3.cpp](https://github.com/regina-normal/regina/blob/e3a5c7c0e0581706d9e5531b750160b322489950/engine/triangulation/example3.cpp#L564-L575),
which attributes it to chapter 8 of Richard Rannard's PhD thesis.

## Representation and scope differences

This is a translation of the selected mathematical behavior into Agda, with
explicit differences from the C++ representation:

- Packed permutation integers, lookup tables, pointer arrays, and lock bit
  masks become finite-indexed functions, records, and Boolean lock fields.
  Permutations are compared pointwise, without assuming equality of proof
  fields or function extensionality.
- Input permutation validation is stronger than Regina's unchecked image-array
  constructor. Malformed image lists receive an explicit rejection.
- Mutation becomes an immutable `Transition`; failures return a `Failure`
  value and callers retain their original state. The change markers
  `no_change`, `topology_changed`, and `locks_changed` summarize the kind of
  edit. They do not implement Regina's snapshots, packet notifications, or
  cache invalidation. In particular, `topology_changed` marks a gluing-table
  edit, not a proved change of homeomorphism type.
- The simplex count is fixed in the type of a triangulation. This slice can
  create an initially unpaired collection of a chosen size, but does not add,
  delete, reorder, or move simplices between existing triangulations. Facet
  addresses are indices into the supplied table, not persistent C++ objects.
- Each changed result is exhaustively recertified. No claim of Regina's
  performance or suitability for large censuses follows from these definitions.
- The pure finite core is generic in dimension and permutation degree,
  including small cases outside Regina's template range. The external
  `from_input_gluings` entry point follows Regina's dimension guard: `false`
  selects dimensions 2 through 8; `true` selects dimensions 2 through 15.
  Typed `from_gluings` and generic examples do not impose that guard.

The omitted subsystems include normal surfaces and hypersurfaces, homology,
fundamental groups, lower-dimensional skeleton and link construction, Pachner
moves and other retriangulation algorithms, recognition, isomorphism
signatures, geometric realization, GUI rendering, and native bindings. No
complete Regina API, application replacement, or C++ interoperability layer is
provided by this directory.

## Checking the Agda development

The validation target is **Agda 2.6.3**, using builtin modules only. No Agda
standard library or other installed library is required. From the repository
root, the aggregate checking command is:

```text
agda --safe --without-K --ignore-interfaces --no-libraries --no-default-libraries -i agda agda/Regina/All.agda
```

`Regina.All` loads the implementation and its reduction tests. Rechecking
interfaces is intentional. `--safe` keeps unchecked postulates and unsafe
termination escapes out of this development; `--without-K` avoids assuming the
K equality principle. Computation is exercised by Agda reduction while checking
the test equalities. This command checks definitions and proofs; it does not
build or run a GHC-backend executable, and no such executable is claimed here.

[VERIFICATION.txt](VERIFICATION.txt) records the validation result and its
execution boundary.

| Module | Responsibility |
|---|---|
| [Regina.Foundation](Regina/Foundation.agda) | Finite indices, vectors, lists, equality, and exhaustive proof-producing decisions. |
| [Regina.Permutation](Regina/Permutation.agda) | Permutation operations, checked construction, and pointwise laws. |
| [Regina.Triangulation](Regina/Triangulation.agda) | Adjacency, locks, transitions, structural certification, and local vertex crossing. |
| [Regina.Input](Regina/Input.agda) | Checked number and image-list input, dimension guard, and sequential gluing construction. |
| [Regina.Examples](Regina/Examples.agda) | Original Regina example constructions. |
| [Regina.PermutationTests](Regina/PermutationTests.agda) | Reduction tests for permutation operations and rejected image inputs. |
| [Regina.TriangulationTests](Regina/TriangulationTests.agda) | Reduction tests for gluing structure, state changes, input failures, and locks. |
| [Regina.All](Regina/All.agda) | Aggregate entry point for implementation and tests. |

## Attribution and licensing

Thank you, **Benjamin A. Burton**, credited as **Ben Burton** in the translated
source headers, for Regina and the permutation and triangulation implementation.
Thank you, **Ryan Budney**, for your work on Regina.
Thank you, **William Pettersson**, for your work on Regina.
The three are individually named in Regina's
[citation and author guidance](https://github.com/regina-normal/regina/blob/e3a5c7c0e0581706d9e5531b750160b322489950/LICENSE.txt#L6-L26).

Thank you, **Richard Rannard**, for the figure-eight construction credited to
chapter 8 of your PhD thesis in the original source. This translation preserves
that source attribution without inventing a thesis title or claiming to have
audited its bibliography.

These acknowledgments identify the developers and reference used for this
subsystem; they are not a complete census of Regina's contributors or cited
authors. Regina's existing credits and wider acknowledgments remain in place.

The translated material is distributed under **GPL-2.0-or-later**, with Regina's
existing additional permission for distribution through the named application
stores. [The root LICENSE.txt](../LICENSE.txt) contains the governing terms,
upstream citation guidance, acknowledgments, and third-party notices. It remains
unchanged. The additional permission must not be generalized to third-party
components whose licenses do not grant it.
