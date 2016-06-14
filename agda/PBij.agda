-- Theory of partial bijections

module PBij where

open import Level renaming (zero to lzero)

open import Data.Empty
open import Data.Unit
open import Data.Sum

open import Data.Maybe
open import Category.Monad

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core

_⇀_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
A ⇀ B = A → Maybe B

-- Is associativity of _<=<_ recorded anywhere?
_•_ : ∀ {ℓ} {A B C : Set ℓ} → (B ⇀ C) → (A ⇀ B) → (A ⇀ C)
_•_ = _<=<_
  where
    open RawMonad Data.Maybe.monad

infixr 9 _•_

id : ∀ {ℓ} {A : Set ℓ} → (A ⇀ A)
id = just

_⊑M_ : {B : Set} → Rel (Maybe B) lzero
just a ⊑M just b  = a ≡ b
just x ⊑M nothing = ⊥
nothing ⊑M b      = ⊤

_⊑_ : {A B : Set} → Rel (A ⇀ B) lzero
f ⊑ g = ∀ a → f a ⊑M g a

infix 4 _⊑_

record _⇌_ (A B : Set) : Set where
  field
    fwd      : A → Maybe B
    bwd      : B → Maybe A
    left-id  : bwd • fwd ⊑ id
    right-id : fwd • bwd ⊑ id

_∘_ : {A B C : Set} → (B ⇌ C) → (A ⇌ B) → (A ⇌ C)
g ∘ f = record
  { fwd = g.fwd • f.fwd
  ; bwd = f.bwd • g.bwd
  ; left-id  = {!!}  -- for this proof need associativity of _•_ = _<=<_
  ; right-id = {!!}
  }
  where
    module f = _⇌_ f
    module g = _⇌_ g
