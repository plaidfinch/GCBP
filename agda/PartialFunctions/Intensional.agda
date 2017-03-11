module PartialFunctions.Intensional where

open import Level renaming (suc to lsuc)

open import PartialFunctions hiding (isEquivalence)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (refl ; sym)

data _⇀I_ {ℓ} : Set ℓ → Set ℓ → Set (lsuc ℓ) where
  idI   : ∀ {A}   → (A ⇀I A)
  ∅I    : ∀ {A B} → (A ⇀I B)
  singI : ∀ {A B} → (A ⇀ B) → (A ⇀I B)
  _∙I_  : ∀ {A B C} → (B ⇀I C) → (A ⇀I B) → (A ⇀I C)

⌊_⌋ : ∀ {ℓ} {A B : Set ℓ} → (A ⇀I B) → (A ⇀ B)
⌊ idI ⌋     = id
⌊ ∅I ⌋      = ∅
⌊ singI f ⌋ = f
⌊ f ∙I g ⌋  = ⌊ f ⌋ ∙ ⌊ g ⌋

_≈I_ : ∀ {ℓ} {A B : Set ℓ} → Rel (A ⇀I B) ℓ
f ≈I g = ⌊ f ⌋ ≈ ⌊ g ⌋

isEquivalence : ∀ {ℓ} {A B : Set ℓ} → IsEquivalence (_≈I_ {ℓ} {A} {B})
isEquivalence = record
  { refl  = ≈-refl
  ; sym   = ≈-sym
  ; trans = ≈-trans
  }

