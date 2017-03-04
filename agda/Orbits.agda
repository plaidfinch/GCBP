module Orbits where

open import PartialBijections

open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.Maybe
open import Relation.Binary.Core using (_≡_)

-- A bijection is a partial bijection which is defined everywhere.
record _↔_ (A B : Set) : Set where
  field
    pbij  : A ⇌ B
    totalfwd : (a : A) → ∃ (λ b → _⇌_.fwd pbij a ≡ just b)
    totalbwd : (b : B) → ∃ (λ a → _⇌_.bwd pbij b ≡ just a)
    -- We could get away without totalbwd *if* we knew the sets were finite.

  fwd : A → B
  fwd a = proj₁ (totalfwd a)

  bwd : B → A
  bwd b = proj₁ (totalbwd b)

module Orbits {A B A′ B′ : Set} (h : (A ⊎ B) ↔ (A′ ⊎ B′)) (g : B ↔ B′) where

  iter : (n : ℕ) (a : A) → (A′ ⊎ B′)
  iter zero a    = _↔_.fwd h (inj₁ a)
  iter (suc n) a with iter n a
  iter (suc n) a | inj₁ a′ = inj₁ a′
  iter (suc n) a | inj₂ b′ = _↔_.fwd h (inj₂ (_↔_.bwd g b′))

  orbitsDisjoint : (x y : A) (m n : ℕ) → (iter m x ≡ iter n y) → x ≡ y
  orbitsDisjoint x y m n imx≡imy = {!!}

open Orbits public


