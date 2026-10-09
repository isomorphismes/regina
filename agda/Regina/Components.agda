{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-09. License: ../../LICENSE.txt.

-- Connected simplex components and orientation propagation.
-- Derived from engine/triangulation/detail/skeleton-impl.h at
-- e3a5c7c0e0581706d9e5531b750160b322489950.
-- Copyright (c) 1999-2026, Ben Burton / The Regina development team.
-- GPL version 2 or later with Regina's distribution permission; see ../../LICENSE.txt.

module Regina.Components where

open import Regina.Foundation
open import Regina.Permutation
open import Regina.Triangulation

private
  variable
    dimension simplex_count : Nat

xor : Bool → Bool → Bool
xor false right = right
xor true false = true
xor true true = false

natLessThan : Nat → Nat → Bool
natLessThan zero zero = false
natLessThan zero (suc right) = true
natLessThan (suc left) zero = false
natLessThan (suc left) (suc right) = natLessThan left right

oddInversionsAgainst : Nat → List Nat → Bool
oddInversionsAgainst left [] = false
oddInversionsAgainst left (right ∷ remaining) =
  xor (natLessThan right left) (oddInversionsAgainst left remaining)

oddPermutationImages : List Nat → Bool
oddPermutationImages [] = false
oddPermutationImages (head ∷ tail) =
  xor (oddInversionsAgainst head tail) (oddPermutationImages tail)

-- Regina's Perm::sign() is +1 for an even permutation and -1 for an odd one.
permutationEven : {number_of_vertices : Nat} →
  Permutation number_of_vertices → Bool
permutationEven mapping = not (oddPermutationImages (image_table mapping))

filterList : {element : Set} → (element → Bool) → List element → List element
filterList predicate [] = []
filterList predicate (head ∷ tail) with predicate head
... | true = head ∷ filterList predicate tail
... | false = filterList predicate tail

concatMap : {source target : Set} →
  (source → List target) → List source → List target
concatMap function [] = []
concatMap function (head ∷ tail) = function head ++ concatMap function tail

sumNaturals : List Nat → Nat
sumNaturals [] = zero
sumNaturals (head ∷ tail) = head + sumNaturals tail

collectAdjacentSimplices : Triangulation dimension simplex_count →
  Fin simplex_count → List (Fin (suc dimension)) → List (Fin simplex_count)
collectAdjacentSimplices current source [] = []
collectAdjacentSimplices current source (localFacet ∷ remaining)
  with adjacency (raw_state current) (facet source localFacet)
... | nothing = collectAdjacentSimplices current source remaining
... | just outward = adjacent_simplex outward ∷
  collectAdjacentSimplices current source remaining

simplexNeighbors : Triangulation dimension simplex_count →
  Fin simplex_count → List (Fin simplex_count)
simplexNeighbors {dimension} current source =
  collectAdjacentSimplices current source (all_fin (suc dimension))

memberSimplex : Fin simplex_count → List (Fin simplex_count) → Bool
memberSimplex target [] = false
memberSimplex target (candidate ∷ remaining) =
  fin_equal target candidate or memberSimplex target remaining

directlySimplexConnected : Triangulation dimension simplex_count →
  Fin simplex_count → Fin simplex_count → Bool
directlySimplexConnected current first second =
  fin_equal first second or memberSimplex second (simplexNeighbors current first)

expandSimplexReachableOnce : Triangulation dimension simplex_count →
  List (Fin simplex_count) → List (Fin simplex_count) → List (Fin simplex_count)
expandSimplexReachableOnce current universe reached = filterList
  (λ candidate → any (λ known → directlySimplexConnected current known candidate) reached)
  universe

expandSimplexReachable : Nat → Triangulation dimension simplex_count →
  List (Fin simplex_count) → List (Fin simplex_count) → List (Fin simplex_count)
expandSimplexReachable zero current universe reached = reached
expandSimplexReachable (suc fuel) current universe reached =
  expandSimplexReachable fuel current universe
    (expandSimplexReachableOnce current universe reached)

simplexComponentOf : Triangulation dimension simplex_count →
  List (Fin simplex_count) → Fin simplex_count → List (Fin simplex_count)
simplexComponentOf current universe seed =
  expandSimplexReachable (length universe) current universe (seed ∷ [])

removeSimplices : List (Fin simplex_count) →
  List (Fin simplex_count) → List (Fin simplex_count)
removeSimplices removed = filterList
  (λ candidate → not (memberSimplex candidate removed))

partitionSimplexComponents : Nat → Triangulation dimension simplex_count →
  List (Fin simplex_count) → List (Fin simplex_count) →
  List (List (Fin simplex_count))
partitionSimplexComponents zero current universe remaining = []
partitionSimplexComponents (suc fuel) current universe [] = []
partitionSimplexComponents (suc fuel) current universe (seed ∷ remaining)
  with simplexComponentOf current universe seed
... | foundComponent = foundComponent ∷
  partitionSimplexComponents fuel current universe
    (removeSimplices foundComponent remaining)

simplexComponents : Triangulation dimension simplex_count →
  List (List (Fin simplex_count))
simplexComponents {simplex_count = numberOfSimplices} current =
  partitionSimplexComponents numberOfSimplices current
    (all_fin numberOfSimplices) (all_fin numberOfSimplices)

componentCount : Triangulation dimension simplex_count → Nat
componentCount current = length (simplexComponents current)

componentSizes : Triangulation dimension simplex_count → List Nat
componentSizes current = map length (simplexComponents current)

countBoundaryFacets : Triangulation dimension simplex_count →
  Fin simplex_count → List (Fin (suc dimension)) → Nat
countBoundaryFacets current simplexIndex [] = zero
countBoundaryFacets current simplexIndex (localFacet ∷ remaining)
  with adjacency (raw_state current) (facet simplexIndex localFacet)
... | nothing = suc (countBoundaryFacets current simplexIndex remaining)
... | just outward = countBoundaryFacets current simplexIndex remaining

simplexBoundaryFacetCount : Triangulation dimension simplex_count →
  Fin simplex_count → Nat
simplexBoundaryFacetCount {dimension} current simplexIndex =
  countBoundaryFacets current simplexIndex (all_fin (suc dimension))

componentBoundaryFacetCount : Triangulation dimension simplex_count →
  List (Fin simplex_count) → Nat
componentBoundaryFacetCount current componentSimplices =
  sumNaturals (map (simplexBoundaryFacetCount current) componentSimplices)

componentBoundaryFacetCounts : Triangulation dimension simplex_count → List Nat
componentBoundaryFacetCounts current = map
  (componentBoundaryFacetCount current) (simplexComponents current)

data Orientation : Set where
  positive negative : Orientation

orientationEqual : Orientation → Orientation → Bool
orientationEqual positive positive = true
orientationEqual negative negative = true
orientationEqual first second = false

flipOrientation : Orientation → Orientation
flipOrientation positive = negative
flipOrientation negative = positive

record OrientedSimplex (simplex_count : Nat) : Set where
  constructor orientedSimplex
  field
    oriented_simplex_number : Fin simplex_count
    simplex_orientation : Orientation
open OrientedSimplex public

orientedSimplexEqual : OrientedSimplex simplex_count →
  OrientedSimplex simplex_count → Bool
orientedSimplexEqual first second =
  fin_equal (oriented_simplex_number first) (oriented_simplex_number second) and
  orientationEqual (simplex_orientation first) (simplex_orientation second)

allOrientedSimplices : (numberOfSimplices : Nat) →
  List (OrientedSimplex numberOfSimplices)
allOrientedSimplices numberOfSimplices = concatMap
  (λ simplexIndex → orientedSimplex simplexIndex positive ∷
    orientedSimplex simplexIndex negative ∷ [])
  (all_fin numberOfSimplices)

crossOrientedFacet : Triangulation dimension simplex_count →
  OrientedSimplex simplex_count → Fin (suc dimension) →
  Maybe (OrientedSimplex simplex_count)
crossOrientedFacet current source localFacet
  with adjacency (raw_state current)
    (facet (oriented_simplex_number source) localFacet)
... | nothing = nothing
... | just outward with permutationEven (vertex_permutation outward)
... | true = just (orientedSimplex (adjacent_simplex outward)
  (flipOrientation (simplex_orientation source)))
... | false = just (orientedSimplex (adjacent_simplex outward)
  (simplex_orientation source))

collectOrientedNeighbors : Triangulation dimension simplex_count →
  OrientedSimplex simplex_count → List (Fin (suc dimension)) →
  List (OrientedSimplex simplex_count)
collectOrientedNeighbors current source [] = []
collectOrientedNeighbors current source (localFacet ∷ remaining)
  with crossOrientedFacet current source localFacet
... | nothing = collectOrientedNeighbors current source remaining
... | just target = target ∷ collectOrientedNeighbors current source remaining

orientedNeighbors : Triangulation dimension simplex_count →
  OrientedSimplex simplex_count → List (OrientedSimplex simplex_count)
orientedNeighbors {dimension} current source =
  collectOrientedNeighbors current source (all_fin (suc dimension))

memberOrientedSimplex : OrientedSimplex simplex_count →
  List (OrientedSimplex simplex_count) → Bool
memberOrientedSimplex target [] = false
memberOrientedSimplex target (candidate ∷ remaining) =
  orientedSimplexEqual target candidate or
  memberOrientedSimplex target remaining

directlyOrientedConnected : Triangulation dimension simplex_count →
  OrientedSimplex simplex_count → OrientedSimplex simplex_count → Bool
directlyOrientedConnected current first second =
  orientedSimplexEqual first second or
  memberOrientedSimplex second (orientedNeighbors current first)

expandOrientedReachableOnce : Triangulation dimension simplex_count →
  List (OrientedSimplex simplex_count) → List (OrientedSimplex simplex_count) →
  List (OrientedSimplex simplex_count)
expandOrientedReachableOnce current universe reached = filterList
  (λ candidate → any
    (λ known → directlyOrientedConnected current known candidate) reached)
  universe

expandOrientedReachable : Nat → Triangulation dimension simplex_count →
  List (OrientedSimplex simplex_count) → List (OrientedSimplex simplex_count) →
  List (OrientedSimplex simplex_count)
expandOrientedReachable zero current universe reached = reached
expandOrientedReachable (suc fuel) current universe reached =
  expandOrientedReachable fuel current universe
    (expandOrientedReachableOnce current universe reached)

reachableOrientationsFrom : Triangulation dimension simplex_count →
  Fin simplex_count → List (OrientedSimplex simplex_count)
reachableOrientationsFrom {simplex_count = numberOfSimplices} current root =
  expandOrientedReachable (numberOfSimplices + numberOfSimplices) current
    (allOrientedSimplices numberOfSimplices)
    (orientedSimplex root positive ∷ [])

hasBothOrientations : List (OrientedSimplex simplex_count) →
  Fin simplex_count → Bool
hasBothOrientations reached simplexIndex =
  memberOrientedSimplex (orientedSimplex simplexIndex positive) reached and
  memberOrientedSimplex (orientedSimplex simplexIndex negative) reached

componentOrientable : Triangulation dimension simplex_count →
  List (Fin simplex_count) → Bool
componentOrientable current [] = true
componentOrientable current (root ∷ remaining) with
  reachableOrientationsFrom current root
... | reached = not (any (hasBothOrientations reached) (root ∷ remaining))

componentOrientabilities : Triangulation dimension simplex_count → List Bool
componentOrientabilities current = map
  (componentOrientable current) (simplexComponents current)

triangulationOrientable : Triangulation dimension simplex_count → Bool
triangulationOrientable current = all (λ result → result)
  (componentOrientabilities current)
