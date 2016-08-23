-- PIE: given set U and family of properties P
--
-- |elts with no properties| = ∑ J ⊆ P (-1)^|J| |A_J|

module PIE where

open import Data.Nat
open import Data.Fin.Subset

open import Relation.Binary.PropositionalEquality using (setoid)

import Data.Vec as V
open import Data.List

allSubsets : (n : ℕ) → List (Subset n)
allSubsets zero    = [ V.[] ]
allSubsets (suc n) = map (V._∷_ outside) (allSubsets n) ++ map (V._∷_ inside) (allSubsets n)

data _L∈_ {A : Set} : A → List A → Set where
  hd : {a : A} {t : List A} → a L∈ (a ∷ t)
  tl : {a b : A} {t : List A} → a L∈ t → a L∈ (b ∷ t)

∈++ : {A : Set} {a : A} {xs ys : List A} → (a L∈ xs) → a L∈ (xs ++ ys)
∈++ hd      = hd
∈++ (tl pf) = tl (∈++ pf)

++∈ : {A : Set} {a : A} {ys : List A} → (xs : List A) → (a L∈ ys) → a L∈ (xs ++ ys)
++∈ []       pf = pf
++∈ (x ∷ xs) pf = tl (++∈ xs pf)

∈map : {A B : Set} {a : A} {xs : List A} {f : A → B} → (a L∈ xs) → f a L∈ (map f xs)
∈map hd      = hd
∈map (tl pf) = tl (∈map pf)

allSubsets-all : (n : ℕ) → (s : Subset n) → s L∈ allSubsets n
allSubsets-all zero V.[] = hd
allSubsets-all (suc n) (outside V.∷ s) = ∈++                        (∈map (allSubsets-all n s))
allSubsets-all (suc n) (inside  V.∷ s) = ++∈ (map _ (allSubsets n)) (∈map (allSubsets-all n s))

SubsetFamily : (n m : ℕ) → Set
SubsetFamily n m = Vec (Subset n) m
