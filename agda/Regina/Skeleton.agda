{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-09. License: ../../LICENSE.txt.

-- Finite lower-dimensional face quotients for Regina triangulations.
-- Derived from engine/triangulation/detail/skeleton-impl.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.Skeleton where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation

private
  variable
    dimension simplex_count : Nat

-- Regina numbers a local k-face by a subset of k+1 simplex vertices.  A
-- Boolean vector is a direct characteristic function for that subset.  It
-- avoids committing this translation to Regina's packed face-number tables.
record LocalFace (dimension simplex_count : Nat) : Set where
  constructor local_face
  field
    face_simplex : Fin simplex_count
    face_vertices : Vector Bool (suc dimension)
open LocalFace public

filter_list : {element : Set} → (element → Bool) → List element → List element
filter_list predicate [] = []
filter_list predicate (head ∷ tail) with predicate head
... | true = head ∷ filter_list predicate tail
... | false = filter_list predicate tail

concat_map : {source target : Set} →
  (source → List target) → List source → List target
concat_map function [] = []
concat_map function (head ∷ tail) = function head ++ concat_map function tail

count_matching : {element : Set} → (element → Bool) → List element → Nat
count_matching predicate [] = zero
count_matching predicate (head ∷ tail) with predicate head
... | true = suc (count_matching predicate tail)
... | false = count_matching predicate tail

less_than : Nat → Nat → Bool
less_than zero zero = false
less_than zero (suc right) = true
less_than (suc left) zero = false
less_than (suc left) (suc right) = less_than left right

vector_equal : {element_count : Nat} →
  Vector Bool element_count → Vector Bool element_count → Bool
vector_equal empty_vector empty_vector = true
vector_equal (vector_cons left left_tail) (vector_cons right right_tail) =
  bool_equal left right and vector_equal left_tail right_tail

true_count : {element_count : Nat} → Vector Bool element_count → Nat
true_count empty_vector = zero
true_count (vector_cons false tail) = true_count tail
true_count (vector_cons true tail) = suc (true_count tail)

tabulate_vector : {element : Set} (element_count : Nat) →
  (Fin element_count → element) → Vector element element_count
tabulate_vector zero function = empty_vector
tabulate_vector (suc element_count) function =
  vector_cons (function fzero)
    (tabulate_vector element_count (λ position → function (fsuc position)))

all_boolean_vectors : (element_count : Nat) → List (Vector Bool element_count)
all_boolean_vectors zero = empty_vector ∷ []
all_boolean_vectors (suc element_count) =
  map (λ tail → vector_cons false tail) (all_boolean_vectors element_count) ++
  map (λ tail → vector_cons true tail) (all_boolean_vectors element_count)

faceMasks : (dimension face_dimension : Nat) →
  List (Vector Bool (suc dimension))
faceMasks dimension face_dimension with less_than face_dimension dimension
... | false = []
... | true = filter_list
  (λ mask → nat_equal (true_count mask) (suc face_dimension))
  (all_boolean_vectors (suc dimension))

local_faces : (dimension simplex_count face_dimension : Nat) →
  List (LocalFace dimension simplex_count)
local_faces dimension simplex_count face_dimension = concat_map
  (λ simplex_index → map (local_face simplex_index)
    (faceMasks dimension face_dimension))
  (all_fin simplex_count)

local_face_equal : LocalFace dimension simplex_count →
  LocalFace dimension simplex_count → Bool
local_face_equal first second =
  fin_equal (face_simplex first) (face_simplex second) and
  vector_equal (face_vertices first) (face_vertices second)

relabel_face_vertices : Permutation (suc dimension) →
  Vector Bool (suc dimension) → Vector Bool (suc dimension)
relabel_face_vertices {dimension} mapping source_vertices =
  tabulate_vector (suc dimension)
    (λ target_vertex → lookup_vector source_vertices
      (preimage mapping target_vertex))

-- A local face can cross a facet precisely when it does not contain the
-- opposite vertex naming that facet.  The entire vertex subset is transported
-- by the facet permutation.
cross_local_face : Triangulation dimension simplex_count →
  LocalFace dimension simplex_count → Fin (suc dimension) →
  Maybe (LocalFace dimension simplex_count)
cross_local_face current source exit_facet
  with lookup_vector (face_vertices source) exit_facet
... | true = nothing
... | false with adjacency (raw_state current)
  (facet (face_simplex source) exit_facet)
... | nothing = nothing
... | just outward = just (local_face (adjacent_simplex outward)
  (relabel_face_vertices (vertex_permutation outward)
    (face_vertices source)))

collect_crossings : Triangulation dimension simplex_count →
  LocalFace dimension simplex_count → List (Fin (suc dimension)) →
  List (LocalFace dimension simplex_count)
collect_crossings current source [] = []
collect_crossings current source (exit_facet ∷ remaining)
  with cross_local_face current source exit_facet
... | nothing = collect_crossings current source remaining
... | just target = target ∷ collect_crossings current source remaining

local_face_neighbors : Triangulation dimension simplex_count →
  LocalFace dimension simplex_count → List (LocalFace dimension simplex_count)
local_face_neighbors {dimension} current source =
  collect_crossings current source (all_fin (suc dimension))

member_local_face : LocalFace dimension simplex_count →
  List (LocalFace dimension simplex_count) → Bool
member_local_face target [] = false
member_local_face target (candidate ∷ remaining) =
  local_face_equal target candidate or member_local_face target remaining

-- Reflexive adjacency lets one finite saturation pass retain everything that
-- it had already reached while adding all one-step neighbors.
directly_connected : Triangulation dimension simplex_count →
  LocalFace dimension simplex_count → LocalFace dimension simplex_count → Bool
directly_connected current first second =
  local_face_equal first second or
  member_local_face second (local_face_neighbors current first)

expand_reachable_once : Triangulation dimension simplex_count →
  List (LocalFace dimension simplex_count) →
  List (LocalFace dimension simplex_count) →
  List (LocalFace dimension simplex_count)
expand_reachable_once current universe reached = filter_list
  (λ candidate → any (λ known → directly_connected current known candidate) reached)
  universe

expand_reachable : Nat → Triangulation dimension simplex_count →
  List (LocalFace dimension simplex_count) →
  List (LocalFace dimension simplex_count) →
  List (LocalFace dimension simplex_count)
expand_reachable zero current universe reached = reached
expand_reachable (suc fuel) current universe reached =
  expand_reachable fuel current universe
    (expand_reachable_once current universe reached)

face_class_of : Triangulation dimension simplex_count →
  List (LocalFace dimension simplex_count) →
  LocalFace dimension simplex_count →
  List (LocalFace dimension simplex_count)
face_class_of current universe seed =
  expand_reachable (length universe) current universe (seed ∷ [])

remove_local_faces : List (LocalFace dimension simplex_count) →
  List (LocalFace dimension simplex_count) →
  List (LocalFace dimension simplex_count)
remove_local_faces removed = filter_list
  (λ candidate → not (member_local_face candidate removed))

partition_local_faces : Nat → Triangulation dimension simplex_count →
  List (LocalFace dimension simplex_count) →
  List (LocalFace dimension simplex_count) →
  List (List (LocalFace dimension simplex_count))
partition_local_faces zero current universe remaining = []
partition_local_faces (suc fuel) current universe [] = []
partition_local_faces (suc fuel) current universe (seed ∷ remaining) =
  component ∷ partition_local_faces fuel current universe
    (remove_local_faces component remaining)
  where
  component : List (LocalFace dimension simplex_count)
  component = face_class_of current universe seed

-- This is the transitive quotient of all local k-faces under the supplied
-- facet gluings.  It translates Regina's face-discovery result, not its
-- embedding order, face numbering, link construction, or validity flags.
face_classes : Triangulation dimension simplex_count → Nat →
  List (List (LocalFace dimension simplex_count))
face_classes {dimension} {simplex_count} current face_dimension
  with local_faces dimension simplex_count face_dimension
... | universe = partition_local_faces (length universe) current universe universe

face_class_count : Triangulation dimension simplex_count → Nat → Nat
face_class_count current face_dimension =
  length (face_classes current face_dimension)

face_class_degrees : Triangulation dimension simplex_count → Nat → List Nat
face_class_degrees current face_dimension =
  map length (face_classes current face_dimension)

face_classes_of_degree : Triangulation dimension simplex_count → Nat → Nat → Nat
face_classes_of_degree current face_dimension requested_degree = count_matching
  (λ component → nat_equal (length component) requested_degree)
  (face_classes current face_dimension)

-- Regina exposes face counts for dimensions 0 through dimension-1.  Keeping
-- this order makes the result useful as a compact skeleton signature.
skeleton_face_counts : Triangulation dimension simplex_count → List Nat
skeleton_face_counts {dimension} current = map
  (λ face_dimension → face_class_count current (fin_to_nat face_dimension))
  (all_fin dimension)
