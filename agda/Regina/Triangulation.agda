{-# OPTIONS --safe --without-K #-}

-- Agda translation of Regina's finite facet-gluing subsystem.
-- Derived from engine/triangulation/simplex.h and triangulation.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later, with Regina's additional distribution permission;
-- see ../../LICENSE.txt. Translation changes: 2026-10-09.

module Regina.Triangulation where

open import Regina.Foundation
open import Regina.Permutation
open import Agda.Builtin.Unit using (⊤; tt)

private
  variable
    dimension simplex_count : Nat

-- A facet is named by the vertex opposite it. That vertex is excluded from
-- the actual gluing. Two different facets of one simplex may be paired.
record Facet (dimension simplex_count : Nat) : Set where
  constructor facet
  field
    simplex_number : Fin simplex_count
    opposite_vertex : Fin (suc dimension)
open Facet public

facet_equal : Facet dimension simplex_count → Facet dimension simplex_count → Bool
facet_equal first second =
  fin_equal (simplex_number first) (simplex_number second) and
  fin_equal (opposite_vertex first) (opposite_vertex second)

record Gluing (dimension simplex_count : Nat) : Set where
  constructor gluing
  field
    adjacent_simplex : Fin simplex_count
    vertex_permutation : Permutation (suc dimension)
open Gluing public

destination : Facet dimension simplex_count → Gluing dimension simplex_count →
              Facet dimension simplex_count
destination source outward = facet (adjacent_simplex outward)
  (image (vertex_permutation outward) (opposite_vertex source))

-- This explicit state replaces Regina's pointer arrays and lock bit masks.
-- A boundary facet has no gluing, rather than an inaccessible stale map.
record RawTriangulation (dimension simplex_count : Nat) : Set where
  constructor raw_triangulation
  field
    adjacency : Facet dimension simplex_count → Maybe (Gluing dimension simplex_count)
    facet_is_locked : Facet dimension simplex_count → Bool
    simplex_is_locked : Fin simplex_count → Bool
open RawTriangulation public

bool_equal : Bool → Bool → Bool
bool_equal false false = true
bool_equal true true = true
bool_equal _ _ = false

bool_dec_equal : (first second : Bool) → Dec (first ≡ second)
bool_dec_equal false false = yes refl
bool_dec_equal false true = no (λ ())
bool_dec_equal true false = no (λ ())
bool_dec_equal true true = yes refl

-- These are structural rules for the adjacency table. They say nothing
-- about vertex links, manifold recognition, orientability, or ideal ends.
record MatchedPair
  (current_table : RawTriangulation dimension simplex_count)
  (source : Facet dimension simplex_count)
  (outward inward : Gluing dimension simplex_count) : Set where
  constructor matched_pair
  field
    distinct_facets : facet_equal source (destination source outward) ≡ false
    returns_to_source_simplex : adjacent_simplex inward ≡ simplex_number source
    returns_every_vertex : (vertex_index : Fin (suc dimension)) →
      image (vertex_permutation inward) vertex_index ≡
      preimage (vertex_permutation outward) vertex_index
    matching_facet_locks : facet_is_locked current_table source ≡
      facet_is_locked current_table (destination source outward)

dec_matched_pair :
  (current_table : RawTriangulation dimension simplex_count)
  (source : Facet dimension simplex_count)
  (outward inward : Gluing dimension simplex_count) →
  Dec (MatchedPair current_table source outward inward)
dec_matched_pair current_table source outward inward
  with bool_dec_equal (facet_equal source (destination source outward)) false
... | no refute = no (λ witness → refute (MatchedPair.distinct_facets witness))
... | yes distinct
  with fin_dec_equal (adjacent_simplex inward) (simplex_number source)
... | no refute = no (λ witness → refute (MatchedPair.returns_to_source_simplex witness))
... | yes returns_simplex
  with universal_fin_dec (λ vertex_index → fin_dec_equal
    (image (vertex_permutation inward) vertex_index)
    (preimage (vertex_permutation outward) vertex_index))
... | no refute = no (λ witness → refute (MatchedPair.returns_every_vertex witness))
... | yes returns_vertices
  with bool_dec_equal (facet_is_locked current_table source)
    (facet_is_locked current_table (destination source outward))
... | no refute = no (λ witness → refute (MatchedPair.matching_facet_locks witness))
... | yes matching_locks =
  yes (matched_pair distinct returns_simplex returns_vertices matching_locks)

paired_rule : (current_table : RawTriangulation dimension simplex_count) →
  Facet dimension simplex_count → Gluing dimension simplex_count → Set
paired_rule current_table source outward
  with adjacency current_table (destination source outward)
... | nothing = ⊥
... | just inward = MatchedPair current_table source outward inward

dec_paired_rule : (current_table : RawTriangulation dimension simplex_count)
  (source : Facet dimension simplex_count)
  (outward : Gluing dimension simplex_count) → Dec (paired_rule current_table source outward)
dec_paired_rule current_table source outward
  with adjacency current_table (destination source outward)
... | nothing = no (λ impossible → impossible)
... | just inward = dec_matched_pair current_table source outward inward

pairing_rule : (current_table : RawTriangulation dimension simplex_count) →
  Facet dimension simplex_count → Set
pairing_rule current_table source with adjacency current_table source
... | nothing = ⊤
... | just outward = paired_rule current_table source outward

dec_pairing_rule : (current_table : RawTriangulation dimension simplex_count)
  (source : Facet dimension simplex_count) → Dec (pairing_rule current_table source)
dec_pairing_rule current_table source with adjacency current_table source
... | nothing = yes tt
... | just outward = dec_paired_rule current_table source outward

PairingsConsistent : RawTriangulation dimension simplex_count → Set
PairingsConsistent {dimension} {simplex_count} current_table =
  (simplex_index : Fin simplex_count) → (local_facet : Fin (suc dimension)) →
  pairing_rule current_table (facet simplex_index local_facet)

dec_pairings_consistent : (current_table : RawTriangulation dimension simplex_count) →
  Dec (PairingsConsistent current_table)
dec_pairings_consistent current_table = universal_fin_dec (λ simplex_index →
  universal_fin_dec (λ local_facet → dec_pairing_rule current_table (facet simplex_index local_facet)))

-- A successful public operation contains a proof of all the pairing rules.
-- The checker constructs the proof; no postulate turns a Boolean into one.
record Triangulation (dimension simplex_count : Nat) : Set where
  constructor triangulation
  field
    raw_state : RawTriangulation dimension simplex_count
    pairings_consistent : PairingsConsistent raw_state
open Triangulation public

data Failure : Set where
  facet_already_joined same_facet_gluing locked_facet inconsistent_pairing_table : Failure
  invalid_simplex_number invalid_facet_number invalid_vertex_permutation unsupported_dimension : Failure

data Outcome (value_type : Set) : Set where
  rejected : Failure → Outcome value_type
  accepted : value_type → Outcome value_type

map_outcome : {input output : Set} → (input → output) → Outcome input → Outcome output
map_outcome mapping (rejected reason) = rejected reason
map_outcome mapping (accepted value) = accepted (mapping value)

certify : RawTriangulation dimension simplex_count → Outcome (Triangulation dimension simplex_count)
certify current_table with dec_pairings_consistent current_table
... | no _ = rejected inconsistent_pairing_table
... | yes witness = accepted (triangulation current_table witness)

pairings_pass : RawTriangulation dimension simplex_count → Bool
pairings_pass current_table with dec_pairings_consistent current_table
... | no _ = false
... | yes _ = true

unpaired_simplices : (dimension simplex_count : Nat) → Triangulation dimension simplex_count
unpaired_simplices current_dimension number_of_simplices = triangulation
  (raw_triangulation (λ _ → nothing) (λ _ → false) (λ _ → false))
  (λ _ _ → tt)

-- All state writes are ordinary functions; an unsuccessful operation has no
-- partially changed table. Callers retain their original immutable state.
set_adjacency : RawTriangulation dimension simplex_count →
  Facet dimension simplex_count → Maybe (Gluing dimension simplex_count) →
  RawTriangulation dimension simplex_count
set_adjacency {dimension} {simplex_count} current_table changed_facet replacement = record current_table
  { adjacency = λ queried_facet → choose queried_facet }
  where
  choose : Facet dimension simplex_count → Maybe (Gluing dimension simplex_count)
  choose queried_facet with facet_equal queried_facet changed_facet
  ... | true = replacement
  ... | false = adjacency current_table queried_facet

set_facet_lock_raw : RawTriangulation dimension simplex_count →
  Facet dimension simplex_count → Bool → RawTriangulation dimension simplex_count
set_facet_lock_raw {dimension} {simplex_count} current_table changed_facet replacement = record current_table
  { facet_is_locked = λ queried_facet → choose queried_facet }
  where
  choose : Facet dimension simplex_count → Bool
  choose queried_facet with facet_equal queried_facet changed_facet
  ... | true = replacement
  ... | false = facet_is_locked current_table queried_facet

set_simplex_lock_raw : RawTriangulation dimension simplex_count →
  Fin simplex_count → Bool → RawTriangulation dimension simplex_count
set_simplex_lock_raw {dimension} {simplex_count} current_table changed_simplex replacement = record current_table
  { simplex_is_locked = λ queried_simplex → choose queried_simplex }
  where
  choose : Fin simplex_count → Bool
  choose queried_simplex with fin_equal queried_simplex changed_simplex
  ... | true = replacement
  ... | false = simplex_is_locked current_table queried_simplex

data Change : Set where
  no_change topology_changed locks_changed : Change

record Transition (dimension simplex_count : Nat) : Set where
  constructor transition
  field
    resulting_triangulation : Triangulation dimension simplex_count
    change : Change
open Transition public

finish_transition : Change → RawTriangulation dimension simplex_count →
  Outcome (Transition dimension simplex_count)
finish_transition kind current_table = map_outcome (λ certified → transition certified kind) (certify current_table)

-- Simplex::join: check occupancy, then forbidden self-pairing, then locks;
-- write p forward and p⁻¹ backward. Both references share the input state,
-- so a cross-triangulation pointer cannot enter this interface.
join : Triangulation dimension simplex_count → Facet dimension simplex_count →
  Fin simplex_count → Permutation (suc dimension) → Outcome (Transition dimension simplex_count)
join current source target_simplex mapping
  with adjacency (raw_state current) source |
       adjacency (raw_state current) (destination source (gluing target_simplex mapping))
... | just _ | _ = rejected facet_already_joined
... | nothing | just _ = rejected facet_already_joined
... | nothing | nothing
  with facet_equal source (destination source (gluing target_simplex mapping))
... | true = rejected same_facet_gluing
... | false
  with facet_is_locked (raw_state current) source or
       facet_is_locked (raw_state current) (destination source (gluing target_simplex mapping))
... | true = rejected locked_facet
... | false = finish_transition topology_changed
  (set_adjacency
    (set_adjacency (raw_state current) source (just (gluing target_simplex mapping)))
    (destination source (gluing target_simplex mapping))
    (just (gluing (simplex_number source) (inverse mapping))))

record UnjoinResult (dimension simplex_count : Nat) : Set where
  constructor detached
  field
    unjoin_transition : Transition dimension simplex_count
    previous_neighbor : Maybe (Fin simplex_count)

clear_pair_raw : RawTriangulation dimension simplex_count →
  Facet dimension simplex_count → RawTriangulation dimension simplex_count
clear_pair_raw current_table source with adjacency current_table source
... | nothing = current_table
... | just outward = set_adjacency
  (set_adjacency current_table (destination source outward) nothing) source nothing

-- Regina checks boundary BEFORE the lock: even a locked boundary unjoin
-- is a no-op. A joined lock refuses the entire change.
unjoin : Triangulation dimension simplex_count → Facet dimension simplex_count →
  Outcome (UnjoinResult dimension simplex_count)
unjoin current source with adjacency (raw_state current) source
... | nothing = accepted (detached (transition current no_change) nothing)
... | just outward with facet_is_locked (raw_state current) source
... | true = rejected locked_facet
... | false = map_outcome (λ completed →
  detached completed (just (adjacent_simplex outward)))
  (finish_transition topology_changed (clear_pair_raw (raw_state current) source))

change_facet_lock_raw : RawTriangulation dimension simplex_count →
  Facet dimension simplex_count → Bool → RawTriangulation dimension simplex_count
change_facet_lock_raw current_table source lock_value with adjacency current_table source
... | nothing = set_facet_lock_raw current_table source lock_value
... | just outward = set_facet_lock_raw
  (set_facet_lock_raw current_table source lock_value) (destination source outward) lock_value

change_facet_lock : Triangulation dimension simplex_count →
  Facet dimension simplex_count → Bool → Outcome (Transition dimension simplex_count)
change_facet_lock current source lock_value
  with bool_equal (facet_is_locked (raw_state current) source) lock_value
... | true = accepted (transition current no_change)
... | false = finish_transition locks_changed (change_facet_lock_raw (raw_state current) source lock_value)

lock_facet : Triangulation dimension simplex_count →
  Facet dimension simplex_count → Outcome (Transition dimension simplex_count)
lock_facet current source = change_facet_lock current source true

unlock_facet : Triangulation dimension simplex_count →
  Facet dimension simplex_count → Outcome (Transition dimension simplex_count)
unlock_facet current source = change_facet_lock current source false

change_simplex_lock : Triangulation dimension simplex_count →
  Fin simplex_count → Bool → Outcome (Transition dimension simplex_count)
change_simplex_lock current simplex_index lock_value
  with bool_equal (simplex_is_locked (raw_state current) simplex_index) lock_value
... | true = accepted (transition current no_change)
... | false = finish_transition locks_changed (set_simplex_lock_raw (raw_state current) simplex_index lock_value)

lock_simplex : Triangulation dimension simplex_count →
  Fin simplex_count → Outcome (Transition dimension simplex_count)
lock_simplex current simplex_index = change_simplex_lock current simplex_index true

unlock_simplex : Triangulation dimension simplex_count →
  Fin simplex_count → Outcome (Transition dimension simplex_count)
unlock_simplex current simplex_index = change_simplex_lock current simplex_index false

is_paired : RawTriangulation dimension simplex_count → Facet dimension simplex_count → Bool
is_paired current_table source with adjacency current_table source
... | nothing = false
... | just _ = true

clear_facets_raw : RawTriangulation dimension simplex_count →
  Fin simplex_count → List (Fin (suc dimension)) → RawTriangulation dimension simplex_count
clear_facets_raw current_table simplex_index [] = current_table
clear_facets_raw current_table simplex_index (local_facet ∷ remaining) =
  clear_facets_raw (clear_pair_raw current_table (facet simplex_index local_facet)) simplex_index remaining

-- Preflight ALL non-boundary locks before clearing ANY facet. This matters
-- when a later locked facet follows an earlier unlocked one.
isolate : Triangulation dimension simplex_count → Fin simplex_count →
  Outcome (Transition dimension simplex_count)
isolate {dimension} current simplex_index with any
  (λ local_facet → is_paired (raw_state current) (facet simplex_index local_facet) and
    facet_is_locked (raw_state current) (facet simplex_index local_facet)) (all_fin (suc dimension))
... | true = rejected locked_facet
... | false with any (λ local_facet → is_paired (raw_state current) (facet simplex_index local_facet))
  (all_fin (suc dimension))
... | false = accepted (transition current no_change)
... | true = finish_transition topology_changed
  (clear_facets_raw (raw_state current) simplex_index (all_fin (suc dimension)))

record GluingSpec (dimension simplex_count : Nat) : Set where
  constructor glue
  field
    source_facet : Facet dimension simplex_count
    target_simplex : Fin simplex_count
    gluing_permutation : Permutation (suc dimension)

apply_gluings : Triangulation dimension simplex_count → List (GluingSpec dimension simplex_count) →
  Outcome (Triangulation dimension simplex_count)
apply_gluings current [] = accepted current
apply_gluings current (next ∷ remaining)
  with join current (GluingSpec.source_facet next) (GluingSpec.target_simplex next)
    (GluingSpec.gluing_permutation next)
... | rejected reason = rejected reason
... | accepted completed = apply_gluings (resulting_triangulation completed) remaining

-- Triangulation::fromGluings: each pair occurs once, from either direction.
-- Repeated pairs, including reverse duplicates, fail instead of disappearing.
from_gluings : (dimension simplex_count : Nat) → List (GluingSpec dimension simplex_count) →
  Outcome (Triangulation dimension simplex_count)
from_gluings current_dimension number_of_simplices =
  apply_gluings (unpaired_simplices current_dimension number_of_simplices)

all_facets : (dimension simplex_count : Nat) → List (Facet dimension simplex_count)
all_facets current_dimension number_of_simplices = fold_right _++_ []
  (map (λ simplex_index → map (facet simplex_index) (all_fin (suc current_dimension))) (all_fin number_of_simplices))

count_unpaired : List (Facet dimension simplex_count) → RawTriangulation dimension simplex_count → Nat
count_unpaired [] current_table = zero
count_unpaired (source ∷ remaining) current_table with adjacency current_table source
... | nothing = suc (count_unpaired remaining current_table)
... | just _ = count_unpaired remaining current_table

unpaired_facet_count : Triangulation dimension simplex_count → Nat
unpaired_facet_count {dimension} {simplex_count} current =
  count_unpaired (all_facets dimension simplex_count) (raw_state current)

has_boundary_facet : Triangulation dimension simplex_count → Fin simplex_count → Bool
has_boundary_facet {dimension} current simplex_index =
  any (λ local_facet → not (is_paired (raw_state current) (facet simplex_index local_facet)))
    (all_fin (suc dimension))

-- This is a local identification across ONE facet, not the transitive
-- equivalence relation used to build the entire triangulation skeleton.
record LocalVertex (dimension simplex_count : Nat) : Set where
  constructor local_vertex
  field
    containing_simplex : Fin simplex_count
    local_number : Fin (suc dimension)
open LocalVertex public

cross_facet : Triangulation dimension simplex_count → Facet dimension simplex_count →
  Fin (suc dimension) → Maybe (LocalVertex dimension simplex_count)
cross_facet current source vertex_index with fin_equal vertex_index (opposite_vertex source)
... | true = nothing
... | false with adjacency (raw_state current) source
... | nothing = nothing
... | just outward = just (local_vertex (adjacent_simplex outward)
  (image (vertex_permutation outward) vertex_index))

-- Pointwise round trip: inverse storage restores all vertex labels,
-- including the opposite-vertex label used to name the target facet.
gluing_round_trip : (mapping : Permutation (suc dimension)) →
  (vertex_index : Fin (suc dimension)) →
  image (inverse mapping) (image mapping vertex_index) ≡ vertex_index
gluing_round_trip mapping vertex_index = preimage_image mapping vertex_index

-- A vertex lying on the source facet remains on the destination facet:
-- injectivity prevents it from mapping to that facet's excluded vertex.
gluing_preserves_facet_membership : (mapping : Permutation (suc dimension)) →
  (excluded_vertex vertex_index : Fin (suc dimension)) →
  (vertex_index ≡ excluded_vertex → ⊥) →
  (image mapping vertex_index ≡ image mapping excluded_vertex → ⊥)
gluing_preserves_facet_membership mapping excluded_vertex vertex_index different equal_images =
  different (image_injective mapping equal_images)

reciprocal_facet_returns :
  (current_table : RawTriangulation dimension simplex_count)
  (source : Facet dimension simplex_count)
  (outward inward : Gluing dimension simplex_count) →
  MatchedPair current_table source outward inward →
  image (vertex_permutation inward)
    (image (vertex_permutation outward) (opposite_vertex source)) ≡ opposite_vertex source
reciprocal_facet_returns current_table source outward inward witness =
  trans (MatchedPair.returns_every_vertex witness (image (vertex_permutation outward) (opposite_vertex source)))
    (preimage_image (vertex_permutation outward) (opposite_vertex source))
