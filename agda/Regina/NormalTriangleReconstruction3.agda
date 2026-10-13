{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-13. License: ../../LICENSE.txt.
-- NormalSurface::reconstructTriangles(), engine/surface/triangles.cpp.
-- Source baseline e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- The immutable implementation propagates the same arc differences across
-- vertex-link sides, then subtracts the minimum at each global vertex.

module Regina.NormalTriangleReconstruction3 where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation
open import Regina.Skeleton using (LocalFace; face_simplex; face_vertices;
  face_classes; tabulate_vector; concat_map)
open import Regina.NormalCoordinates3
open import Regina.Integer using (Int; pos; negsuc)
import Regina.Integer as Integer
import Regina.DualPresentation3 as Sequence
import Regina.NormalSurface3 as Surfaces

private
  variable
    tetrahedra : Nat
    encoding : NormalCoords

-- Infinity is a result, not an unknown value or a failed reconstruction.
-- Unknown intermediate coordinates use Maybe Int and never reach the output.
data DiscCount : Set where
  finite : Nat → DiscCount
  infinite : DiscCount

include_triangles : NormalCoords → NormalCoords
include_triangles standard = standard
include_triangles almost_normal = almost_normal
include_triangles quadrilateral = standard
include_triangles quadrilateral_octagon = almost_normal

record ReconstructedSurface (encoding : NormalCoords) (tetrahedra : Nat) : Set where
  constructor surface_containing_triangles
  field
    reconstructed_coordinates : Vector DiscCount
      (tetrahedra * coordinateBlock (include_triangles encoding))
open ReconstructedSurface public

disc_count_equal : DiscCount → DiscCount → Bool
disc_count_equal (finite first) (finite second) = nat_equal first second
disc_count_equal infinite infinite = true
disc_count_equal _ _ = false

corner_equal : LocalVertex 3 tetrahedra → LocalVertex 3 tetrahedra → Bool
corner_equal first second = fin_equal (containing_simplex first)
  (containing_simplex second) and fin_equal (local_number first) (local_number second)

all_corners : (tetrahedra : Nat) → List (LocalVertex 3 tetrahedra)
all_corners tetrahedra = concat_map
  (λ tetrahedronIndex → map (local_vertex tetrahedronIndex) (all_fin 4)) (all_fin tetrahedra)

corners_of_face : LocalFace 3 tetrahedra → Maybe (LocalVertex 3 tetrahedra)
corners_of_face currentFace with find
  (lookup_vector (face_vertices currentFace)) (all_fin 4)
... | nothing = nothing
... | just vertexNumber = just (local_vertex (face_simplex currentFace) vertexNumber)

vertex_corner_classes : Triangulation 3 tetrahedra →
  Maybe (List (List (LocalVertex 3 tetrahedra)))
vertex_corner_classes currentTriangulation = Sequence.sequence (map
  (λ vertexClass → Sequence.sequence (map corners_of_face vertexClass))
  (face_classes currentTriangulation 0))

TrianglePotentials : Nat → Set
TrianglePotentials tetrahedra = LocalVertex 3 tetrahedra → Maybe Int

set_triangle_potential : TrianglePotentials tetrahedra →
  LocalVertex 3 tetrahedra → Int → TrianglePotentials tetrahedra
set_triangle_potential previous changedCorner coordinateValue requestedCorner
  with corner_equal changedCorner requestedCorner
... | true = just coordinateValue
... | false = previous requestedCorner

-- Arc counts contributed by discs other than triangles, at one vertex of
-- a face. The two octagon types meeting the relevant edge both contribute.
triangle_arc_offset : SurfaceVector encoding tetrahedra →
  LocalVertex 3 tetrahedra → Fin 4 → Maybe Int
triangle_arc_offset {encoding = encodingValue} currentSurface currentCorner oppositeVertex
  with quadSeparating (local_number currentCorner) oppositeVertex
... | nothing = nothing
... | just separatingType with discCoordinate currentSurface
    (containing_simplex currentCorner) (quadOffset encodingValue + fin_to_nat separatingType)
... | nothing = nothing
... | just quadCount with storesOctagons encodingValue
... | false = just (pos quadCount)
... | true with Sequence.sequence (map
    (λ octagonType → discCoordinate currentSurface (containing_simplex currentCorner)
      (octagonOffset encodingValue + fin_to_nat octagonType)) (quadMeeting separatingType))
... | nothing = nothing
... | just octagonCounts = just (Integer.add (pos quadCount)
    (Integer.sum (map pos octagonCounts)))

data PotentialState (tetrahedra : Nat) : Set where
  consistent_potentials : TrianglePotentials tetrahedra → PotentialState tetrahedra
  conflicting_equations : PotentialState tetrahedra

propagate_across_facet : Triangulation 3 tetrahedra →
  SurfaceVector encoding tetrahedra → PotentialState tetrahedra →
  LocalVertex 3 tetrahedra → Fin 4 → Maybe (PotentialState tetrahedra)
propagate_across_facet currentTriangulation currentSurface conflicting_equations
  currentCorner oppositeVertex = just conflicting_equations
propagate_across_facet currentTriangulation currentSurface
  (consistent_potentials potentialValues) currentCorner oppositeVertex
  with fin_equal (local_number currentCorner) oppositeVertex
... | true = just (consistent_potentials potentialValues)
... | false with potentialValues currentCorner |
    adjacency (raw_state currentTriangulation)
      (facet (containing_simplex currentCorner) oppositeVertex)
... | nothing | _ = just (consistent_potentials potentialValues)
... | just _ | nothing = just (consistent_potentials potentialValues)
... | just sourceValue | just outward
  with triangle_arc_offset currentSurface currentCorner oppositeVertex |
    triangle_arc_offset currentSurface
      (local_vertex (adjacent_simplex outward)
        (image (vertex_permutation outward) (local_number currentCorner)))
      (image (vertex_permutation outward) oppositeVertex)
... | nothing | _ = nothing
... | just _ | nothing = nothing
... | just sourceOffset | just targetOffset = assign
    (local_vertex (adjacent_simplex outward)
      (image (vertex_permutation outward) (local_number currentCorner)))
    (Integer.subtract (Integer.add sourceValue sourceOffset) targetOffset)
  where
  assign : LocalVertex 3 _ → Int → Maybe (PotentialState _)
  assign targetCorner expectedValue with potentialValues targetCorner
  ... | nothing = just (consistent_potentials
      (set_triangle_potential potentialValues targetCorner expectedValue))
  ... | just previousValue with Integer.integer_equal previousValue expectedValue
  ... | true = just (consistent_potentials potentialValues)
  ... | false = just conflicting_equations

propagate_corner : Triangulation 3 tetrahedra → SurfaceVector encoding tetrahedra →
  PotentialState tetrahedra → LocalVertex 3 tetrahedra → List (Fin 4) →
  Maybe (PotentialState tetrahedra)
propagate_corner currentTriangulation currentSurface currentState currentCorner [] = just currentState
propagate_corner currentTriangulation currentSurface currentState currentCorner (sideNumber ∷ remaining)
  with propagate_across_facet currentTriangulation currentSurface currentState currentCorner sideNumber
... | nothing = nothing
... | just nextState = propagate_corner currentTriangulation currentSurface
    nextState currentCorner remaining

propagate_pass : Triangulation 3 tetrahedra → SurfaceVector encoding tetrahedra →
  PotentialState tetrahedra → List (LocalVertex 3 tetrahedra) →
  Maybe (PotentialState tetrahedra)
propagate_pass currentTriangulation currentSurface currentState [] = just currentState
propagate_pass currentTriangulation currentSurface currentState (currentCorner ∷ remaining)
  with propagate_corner currentTriangulation currentSurface currentState currentCorner (all_fin 4)
... | nothing = nothing
... | just nextState = propagate_pass currentTriangulation currentSurface nextState remaining

-- A vertex class with m occurrences has a connected side-adjacency graph.
-- m passes suffice to visit every occurrence and then check every return.
-- Missing coverage remains a failure instead of being called infinity.
propagate_vertex : Nat → Triangulation 3 tetrahedra → SurfaceVector encoding tetrahedra →
  List (LocalVertex 3 tetrahedra) → PotentialState tetrahedra →
  Maybe (PotentialState tetrahedra)
propagate_vertex zero currentTriangulation currentSurface vertexCorners currentState = just currentState
propagate_vertex (suc passes) currentTriangulation currentSurface vertexCorners currentState
  with propagate_pass currentTriangulation currentSurface currentState vertexCorners
... | nothing = nothing
... | just conflicting_equations = just conflicting_equations
... | just (consistent_potentials nextValues) = propagate_vertex passes
    currentTriangulation currentSurface vertexCorners (consistent_potentials nextValues)

integer_less : Int → Int → Bool
integer_less (pos first) (pos second) = Integer.natural_less first second
integer_less (negsuc first) (negsuc second) = Integer.natural_less second first
integer_less (negsuc _) (pos _) = true
integer_less (pos _) (negsuc _) = false

smaller_integer : Int → Int → Int
smaller_integer first second with integer_less first second
... | true = first
... | false = second

record TriangleCoordinate (tetrahedra : Nat) : Set where
  constructor triangle_coordinate
  field
    triangle_corner : LocalVertex 3 tetrahedra
    triangle_count : DiscCount
open TriangleCoordinate public

normalise_corner : TrianglePotentials tetrahedra → Int → LocalVertex 3 tetrahedra →
  Maybe (TriangleCoordinate tetrahedra)
normalise_corner potentialValues minimumValue currentCorner with potentialValues currentCorner
... | nothing = nothing
... | just coordinateValue with Integer.subtract coordinateValue minimumValue
... | pos discMultiplicity = just (triangle_coordinate currentCorner (finite discMultiplicity))
... | negsuc _ = nothing

solve_vertex_triangles : Triangulation 3 tetrahedra → SurfaceVector encoding tetrahedra →
  List (LocalVertex 3 tetrahedra) → Maybe (List (TriangleCoordinate tetrahedra))
solve_vertex_triangles currentTriangulation currentSurface [] = nothing
solve_vertex_triangles currentTriangulation currentSurface (startingCorner ∷ remaining)
  with propagate_vertex (suc (length remaining)) currentTriangulation currentSurface
    (startingCorner ∷ remaining) (consistent_potentials
      (set_triangle_potential (λ _ → nothing) startingCorner (pos zero)))
... | nothing = nothing
... | just conflicting_equations = just (map
    (λ currentCorner → triangle_coordinate currentCorner infinite) (startingCorner ∷ remaining))
... | just (consistent_potentials potentialValues)
  with Sequence.sequence (map potentialValues (startingCorner ∷ remaining))
... | nothing = nothing
... | just coordinateValues = Sequence.sequence (map
    (normalise_corner potentialValues (fold_right smaller_integer (pos zero) coordinateValues))
    (startingCorner ∷ remaining))

triangle_count_at : List (TriangleCoordinate tetrahedra) →
  LocalVertex 3 tetrahedra → Maybe DiscCount
triangle_count_at coordinateValues currentCorner with find
  (λ entry → corner_equal (triangle_corner entry) currentCorner) coordinateValues
... | nothing = nothing
... | just entry = just (triangle_count entry)

tetrahedron_disc_counts : SurfaceVector encoding tetrahedra →
  List (TriangleCoordinate tetrahedra) → Fin tetrahedra → Maybe (List DiscCount)
tetrahedron_disc_counts {encoding = encodingValue} currentSurface triangleRecords tetrahedronIndex
  with Sequence.sequence (map
  (λ vertexNumber → triangle_count_at triangleRecords (local_vertex tetrahedronIndex vertexNumber)) (all_fin 4)) |
    Sequence.sequence (map
      (discCoordinate currentSurface tetrahedronIndex) (quadOctDiscTypes encodingValue))
... | just triangleCounts | just otherCounts = just (triangleCounts ++ map finite otherCounts)
... | _ | _ = nothing

read_disc_counts : (size : Nat) → List DiscCount → Maybe (Vector DiscCount size)
read_disc_counts zero [] = just empty_vector
read_disc_counts zero (_ ∷ _) = nothing
read_disc_counts (suc remaining) [] = nothing
read_disc_counts (suc remaining) (head ∷ tail) with read_disc_counts remaining tail
... | nothing = nothing
... | just coordinateValues = just (vector_cons head coordinateValues)

reconstruct_missing_triangles : Triangulation 3 tetrahedra → SurfaceVector encoding tetrahedra →
  Maybe (ReconstructedSurface encoding tetrahedra)
reconstruct_missing_triangles {tetrahedra = tetrahedra} {encoding = encodingValue}
  currentTriangulation currentSurface with vertex_corner_classes currentTriangulation
... | nothing = nothing
... | just cornerClasses with Sequence.sequence
    (map (solve_vertex_triangles currentTriangulation currentSurface) cornerClasses)
... | nothing = nothing
... | just triangleGroups with Sequence.sequence (map
    (tetrahedron_disc_counts currentSurface (concat_map (λ group → group) triangleGroups))
    (all_fin tetrahedra))
... | nothing = nothing
... | just blocks with read_disc_counts (tetrahedra * coordinateBlock
    (include_triangles encodingValue)) (concat_map (λ block → block) blocks)
... | nothing = nothing
... | just coordinateValues = just (surface_containing_triangles coordinateValues)

map_finite : {size : Nat} → Vector Nat size → Vector DiscCount size
map_finite empty_vector = empty_vector
map_finite (vector_cons head tail) = vector_cons (finite head) (map_finite tail)

-- Full-coordinate encodings are returned unchanged, including vertex links.
reconstruct_triangles : {encoding : NormalCoords} → Triangulation 3 tetrahedra →
  SurfaceVector encoding tetrahedra → Maybe (ReconstructedSurface encoding tetrahedra)
reconstruct_triangles {encoding = standard} currentTriangulation currentSurface =
  just (surface_containing_triangles (map_finite (coordinates currentSurface)))
reconstruct_triangles {encoding = almost_normal} currentTriangulation currentSurface =
  just (surface_containing_triangles (map_finite (coordinates currentSurface)))
reconstruct_triangles {encoding = quadrilateral} = reconstruct_missing_triangles
reconstruct_triangles {encoding = quadrilateral_octagon} = reconstruct_missing_triangles

disc_counts_to_list : {size : Nat} → Vector DiscCount size → List DiscCount
disc_counts_to_list empty_vector = []
disc_counts_to_list (vector_cons head tail) = head ∷ disc_counts_to_list tail

finite_disc_counts : {size : Nat} → Vector DiscCount size → Maybe (Vector Nat size)
finite_disc_counts empty_vector = just empty_vector
finite_disc_counts (vector_cons infinite _) = nothing
finite_disc_counts (vector_cons (finite head) tail) with finite_disc_counts tail
... | nothing = nothing
... | just coordinateValues = just (vector_cons head coordinateValues)

finite_surface : ReconstructedSurface encoding tetrahedra →
  Maybe (SurfaceVector (include_triangles encoding) tetrahedra)
finite_surface currentSurface with finite_disc_counts (reconstructed_coordinates currentSurface)
... | nothing = nothing
... | just coordinateValues = just (surface_vector coordinateValues)

reconstructed_disc : ReconstructedSurface encoding tetrahedra → Fin tetrahedra → Nat →
  Maybe DiscCount
reconstructed_disc {encoding = encodingValue} {tetrahedra = tetrahedra}
  currentSurface tetrahedronIndex discType with fin_from_nat
    (tetrahedra * coordinateBlock (include_triangles encodingValue))
    (fin_to_nat tetrahedronIndex * coordinateBlock (include_triangles encodingValue) + discType)
... | nothing = nothing
... | just index = just (lookup_vector (reconstructed_coordinates currentSurface) index)

add_finite_offset : DiscCount → Int → Maybe DiscCount
add_finite_offset infinite arcOffsetValue = just infinite
add_finite_offset (finite discMultiplicity) arcOffsetValue with Integer.add (pos discMultiplicity) arcOffsetValue
... | pos coordinateValue = just (finite coordinateValue)
... | negsuc _ = nothing

extended_arc_count : SurfaceVector encoding tetrahedra →
  ReconstructedSurface encoding tetrahedra → LocalVertex 3 tetrahedra → Fin 4 →
  Maybe DiscCount
extended_arc_count sourceSurface reconstructionResult currentCorner oppositeVertex with
  reconstructed_disc reconstructionResult (containing_simplex currentCorner) (fin_to_nat (local_number currentCorner)) |
  triangle_arc_offset sourceSurface currentCorner oppositeVertex
... | just discMultiplicity | just arcOffsetValue = add_finite_offset discMultiplicity arcOffsetValue
... | _ | _ = nothing

arc_equation_holds : Triangulation 3 tetrahedra → SurfaceVector encoding tetrahedra →
  ReconstructedSurface encoding tetrahedra → LocalVertex 3 tetrahedra → Fin 4 → Bool
arc_equation_holds currentTriangulation sourceSurface reconstructionResult currentCorner sideNumber
  with fin_equal (local_number currentCorner) sideNumber
... | true = true
... | false with adjacency (raw_state currentTriangulation)
    (facet (containing_simplex currentCorner) sideNumber)
... | nothing = true
... | just outward with extended_arc_count sourceSurface reconstructionResult currentCorner sideNumber |
    extended_arc_count sourceSurface reconstructionResult
      (local_vertex (adjacent_simplex outward)
        (image (vertex_permutation outward) (local_number currentCorner)))
      (image (vertex_permutation outward) sideNumber)
... | just first | just second = disc_count_equal first second
... | _ | _ = false

reconstructed_arcs_match : Triangulation 3 tetrahedra → SurfaceVector encoding tetrahedra →
  ReconstructedSurface encoding tetrahedra → Bool
reconstructed_arcs_match {tetrahedra = tetrahedra} currentTriangulation sourceSurface reconstructionResult =
  all (λ currentCorner → all (arc_equation_holds currentTriangulation sourceSurface reconstructionResult currentCorner)
    (all_fin 4)) (all_corners tetrahedra)

non_triangles_preserved : SurfaceVector encoding tetrahedra →
  ReconstructedSurface encoding tetrahedra → Bool
non_triangles_preserved {encoding = encodingValue} {tetrahedra = tetrahedra} sourceSurface reconstructionResult =
  all (λ tetrahedronIndex → all (coordinate_agrees tetrahedronIndex)
    (quadOctDiscTypes encodingValue)) (all_fin tetrahedra)
  where
  output_index : Nat → Nat
  output_index sourceIndex with storesTriangles encodingValue
  ... | true = sourceIndex
  ... | false = 4 + sourceIndex
  coordinate_agrees : Fin tetrahedra → Nat → Bool
  coordinate_agrees tetrahedronIndex discType with discCoordinate sourceSurface tetrahedronIndex discType |
    reconstructed_disc reconstructionResult tetrahedronIndex (output_index discType)
  ... | just sourceCount | just resultCount = disc_count_equal (finite sourceCount) resultCount
  ... | _ | _ = false

is_infinite : Maybe DiscCount → Bool
is_infinite (just infinite) = true
is_infinite _ = false

is_finite : Maybe DiscCount → Bool
is_finite (just (finite _)) = true
is_finite _ = false

is_zero : Maybe DiscCount → Bool
is_zero (just (finite zero)) = true
is_zero _ = false

vertex_triangles_minimal : ReconstructedSurface encoding tetrahedra →
  List (LocalVertex 3 tetrahedra) → Bool
vertex_triangles_minimal reconstructionResult vertexCorners = all (λ currentCorner → is_infinite (coordinateValue currentCorner)) vertexCorners or
  (all (λ currentCorner → is_finite (coordinateValue currentCorner)) vertexCorners and
   any (λ currentCorner → is_zero (coordinateValue currentCorner)) vertexCorners)
  where
  coordinateValue : LocalVertex 3 _ → Maybe DiscCount
  coordinateValue currentCorner = reconstructed_disc reconstructionResult (containing_simplex currentCorner)
    (fin_to_nat (local_number currentCorner))

triangles_minimal : Triangulation 3 tetrahedra → ReconstructedSurface encoding tetrahedra → Bool
triangles_minimal {encoding = encodingValue} currentTriangulation reconstructionResult
  with storesTriangles encodingValue
... | true = true
... | false with vertex_corner_classes currentTriangulation
... | nothing = false
... | just cornerClasses = all (vertex_triangles_minimal reconstructionResult) cornerClasses

record CertifiedReconstruction (currentTriangulation : Triangulation 3 tetrahedra)
  (sourceSurface : SurfaceVector encoding tetrahedra) : Set where
  constructor certified_reconstruction
  field
    reconstructed_surface : ReconstructedSurface encoding tetrahedra
    disc_preservation : non_triangles_preserved sourceSurface reconstructed_surface ≡ true
    arc_matching : reconstructed_arcs_match currentTriangulation sourceSurface reconstructed_surface ≡ true
    vertex_normalisation : triangles_minimal currentTriangulation reconstructed_surface ≡ true
open CertifiedReconstruction public

certify_reconstruction : (currentTriangulation : Triangulation 3 tetrahedra) →
  (sourceSurface : SurfaceVector encoding tetrahedra) → Maybe (CertifiedReconstruction currentTriangulation sourceSurface)
certify_reconstruction currentTriangulation sourceSurface with reconstruct_triangles currentTriangulation sourceSurface
... | nothing = nothing
... | just reconstructionResult with bool_dec_equal (non_triangles_preserved sourceSurface reconstructionResult) true |
    bool_dec_equal (reconstructed_arcs_match currentTriangulation sourceSurface reconstructionResult) true |
    bool_dec_equal (triangles_minimal currentTriangulation reconstructionResult) true
... | yes preservationProof | yes matchingProof | yes normalisationProof =
    just (certified_reconstruction reconstructionResult preservationProof matchingProof normalisationProof)
... | no _ | _ | _ = nothing
... | yes _ | no _ | _ = nothing
... | yes _ | yes _ | no _ = nothing

reconstructed_euler_characteristic : Triangulation 3 tetrahedra →
  SurfaceVector encoding tetrahedra → Maybe Int
reconstructed_euler_characteristic currentTriangulation sourceSurface
  with certify_reconstruction currentTriangulation sourceSurface
... | nothing = nothing
... | just certificateValue with finite_surface (reconstructed_surface certificateValue)
... | nothing = nothing
... | just finiteSurface = Surfaces.eulerCharacteristic currentTriangulation finiteSurface
