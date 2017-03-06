module Orbits where

open import PartialBijections

open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans)

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

  .injective : (a₁ a₂ : A) → fwd a₁ ≡ fwd a₂ → a₁ ≡ a₂
  injective a₁ a₂ eq with totalfwd a₁ | totalfwd a₂
  injective a₁ a₂ refl | b₁ , fa₁≡b₁ | .b₁ , fa₂≡b₁
    = _⇌_.injective pbij a₁ a₂ b₁ fa₁≡b₁ fa₂≡b₁

inj₁-inj : {A : Set} (B : Set) (x y : A) → _≡_ {_} {A ⊎ B} (inj₁ x) (inj₁ y) → x ≡ y
inj₁-inj _ x .x refl = refl

module Orbits {A B A′ B′ : Set} (h : (A ⊎ B) ↔ (A′ ⊎ B′)) (g : B ↔ B′) where

  iter : (n : ℕ) (a : A) → (A′ ⊎ B′)
  iter zero a    = _↔_.fwd h (inj₁ a)
  iter (suc n) a with iter n a
  iter (suc n) a | inj₁ a′ = inj₁ a′
  iter (suc n) a | inj₂ b′ = _↔_.fwd h (inj₂ (_↔_.bwd g b′))

  -- This ought to be true.  But as a start it might be easier to
  -- prove a version where m ≡ n.
  .orbitsDisjoint : (x y : A) (m n : ℕ) → (iter m x ≡ iter n y) → x ≡ y
  orbitsDisjoint x y m n imx≡imy = {!!}

  -- Version where we iterate the same number of times on both sides.
  .orbitsDisjointN : (x y : A) (n : ℕ) → (iter n x ≡ iter n y) → x ≡ y
  orbitsDisjointN x y zero ix≡iy with _↔_.totalfwd h (inj₁ x) | _↔_.totalfwd h (inj₁ y)
  orbitsDisjointN x y zero refl | hx , eqx | .hx , eqy = inj₁-inj B x y (_↔_.injective h (inj₁ x) (inj₁ y) {!!})
  orbitsDisjointN x y (suc n) ix≡iy = {!!}

open Orbits public


