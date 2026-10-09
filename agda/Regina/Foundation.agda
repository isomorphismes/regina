{-# OPTIONS --safe --without-K #-}

-- Agda translation changes: 2026-10-09. License: ../../LICENSE.txt.

-- Regina translation foundations: finite sets and executable decisions.
-- Copyright (c) 1999-2026, Ben Burton, for the Regina source being translated.
-- Distributed under GPL-2.0-or-later, with Regina's online distribution
-- exception. See ../../LICENSE.txt for the full terms and acknowledgements.

module Regina.Foundation where

open import Agda.Builtin.Nat public using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool public using (Bool; true; false)
open import Agda.Builtin.Maybe public using (Maybe; just; nothing)
open import Agda.Builtin.List public using (List; []; _∷_)
open import Agda.Builtin.Equality public using (_≡_; refl)

infixr 6 _and_
infixr 5 _or_
infixr 5 _++_

_and_ : Bool → Bool → Bool
true and right = right
false and right = false

_or_ : Bool → Bool → Bool
true or right = true
false or right = right

not : Bool → Bool
not true = false
not false = true

data ⊥ : Set where

absurd : {result : Set} → ⊥ → result
absurd ()

-- A successful decision contains a proof; a failed decision rules it out.
data Dec (proposition : Set) : Set where
  yes : proposition → Dec proposition
  no : (proposition → ⊥) → Dec proposition

decision_bool : {proposition : Set} → Dec proposition → Bool
decision_bool (yes _) = true
decision_bool (no _) = false

cong : {domain codomain : Set} (function : domain → codomain)
       {left right : domain} → left ≡ right → function left ≡ function right
cong function refl = refl

sym : {carrier : Set} {left right : carrier} → left ≡ right → right ≡ left
sym refl = refl

trans : {carrier : Set} {first middle last : carrier} →
        first ≡ middle → middle ≡ last → first ≡ last
trans refl second_equality = second_equality

subst : {carrier : Set} (property : carrier → Set)
        {left right : carrier} → left ≡ right → property left → property right
subst property refl left_property = left_property

nat_equal : Nat → Nat → Bool
nat_equal zero zero = true
nat_equal zero (suc right) = false
nat_equal (suc left) zero = false
nat_equal (suc left) (suc right) = nat_equal left right

map : {source target : Set} → (source → target) → List source → List target
map function [] = []
map function (head ∷ tail) = function head ∷ map function tail

_++_ : {element : Set} → List element → List element → List element
[] ++ right = right
(head ∷ tail) ++ right = head ∷ (tail ++ right)

length : {element : Set} → List element → Nat
length [] = zero
length (head ∷ tail) = suc (length tail)

fold_right : {element result : Set} →
             (element → result → result) → result → List element → result
fold_right combine empty_result [] = empty_result
fold_right combine empty_result (head ∷ tail) =
  combine head (fold_right combine empty_result tail)

all : {element : Set} → (element → Bool) → List element → Bool
all predicate [] = true
all predicate (head ∷ tail) = predicate head and all predicate tail

any : {element : Set} → (element → Bool) → List element → Bool
any predicate [] = false
any predicate (head ∷ tail) = predicate head or any predicate tail

find : {element : Set} → (element → Bool) → List element → Maybe element
find predicate [] = nothing
find predicate (head ∷ tail) with predicate head
... | true = just head
... | false = find predicate tail

-- Fin size consists of the vertices numbered zero through size minus one.
-- Its constructors cannot represent a negative or out-of-range vertex.
data Fin : Nat → Set where
  fzero : {remaining : Nat} → Fin (suc remaining)
  fsuc : {remaining : Nat} → Fin remaining → Fin (suc remaining)

fin_to_nat : {number_of_elements : Nat} → Fin number_of_elements → Nat
fin_to_nat fzero = zero
fin_to_nat (fsuc element) = suc (fin_to_nat element)

fin_from_nat : (number_of_elements value : Nat) → Maybe (Fin number_of_elements)
fin_from_nat zero value = nothing
fin_from_nat (suc number_of_elements) zero = just fzero
fin_from_nat (suc number_of_elements) (suc value)
  with fin_from_nat number_of_elements value
... | just element = just (fsuc element)
... | nothing = nothing

fin_equal : {number_of_elements : Nat} →
            Fin number_of_elements → Fin number_of_elements → Bool
fin_equal fzero fzero = true
fin_equal fzero (fsuc right) = false
fin_equal (fsuc left) fzero = false
fin_equal (fsuc left) (fsuc right) = fin_equal left right

fin_successor_injective : {number_of_elements : Nat}
                         {left right : Fin number_of_elements} →
                         fsuc left ≡ fsuc right → left ≡ right
fin_successor_injective refl = refl

fin_dec_equal : {number_of_elements : Nat} →
                (left right : Fin number_of_elements) → Dec (left ≡ right)
fin_dec_equal fzero fzero = yes refl
fin_dec_equal fzero (fsuc right) = no (λ ())
fin_dec_equal (fsuc left) fzero = no (λ ())
fin_dec_equal (fsuc left) (fsuc right) with fin_dec_equal left right
... | yes equality = yes (cong fsuc equality)
... | no inequality = no (λ equality →
  inequality (fin_successor_injective equality))

all_fin : (number_of_elements : Nat) → List (Fin number_of_elements)
all_fin zero = []
all_fin (suc number_of_elements) =
  fzero ∷ map fsuc (all_fin number_of_elements)

-- The length index prevents an image table from silently omitting vertices.
data Vector (element : Set) : Nat → Set where
  empty_vector : Vector element zero
  vector_cons : {number_of_entries : Nat} → element →
                Vector element number_of_entries → Vector element (suc number_of_entries)

lookup_vector : {element : Set} {number_of_entries : Nat} →
                Vector element number_of_entries → Fin number_of_entries → element
lookup_vector empty_vector ()
lookup_vector (vector_cons head tail) fzero = head
lookup_vector (vector_cons head tail) (fsuc position) = lookup_vector tail position

-- Exhaustively decide a dependent statement about every member of Fin.
-- This returns the actual function of proofs, not an unchecked true flag.
universal_fin_dec : {number_of_elements : Nat}
                    {property : Fin number_of_elements → Set} →
                    ((element : Fin number_of_elements) → Dec (property element)) →
                    Dec ((element : Fin number_of_elements) → property element)
universal_fin_dec {zero} decide = yes (λ ())
universal_fin_dec {suc number_of_elements} {property} decide
  with decide fzero |
       universal_fin_dec {number_of_elements}
         {λ element → property (fsuc element)}
         (λ element → decide (fsuc element))
... | no refute_first | _ = no (λ every_element →
  refute_first (every_element fzero))
... | yes first_proof | no refute_remaining = no (λ every_element →
  refute_remaining (λ element → every_element (fsuc element)))
... | yes first_proof | yes remaining_proofs = yes assemble
  where
  assemble : (element : Fin (suc number_of_elements)) → property element
  assemble fzero = first_proof
  assemble (fsuc element) = remaining_proofs element
