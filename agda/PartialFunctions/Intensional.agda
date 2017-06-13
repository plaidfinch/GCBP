module PartialFunctions.Intensional where

open import Level renaming (suc to lsuc)

open import PartialFunctions hiding (isEquivalence)

open import Data.Maybe
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; inspect ; [_])

----------------------------------------------------------------------

-- Initial version.  However, I think this is too unconstrained to be
-- useful.  In particular all the intermediate types are existentially
-- quanitified away, there is no good way to talk about the types of
-- intermediate values.  In our application we specifically know that
-- we will be ping-ponging back and forth between specific types, so
-- we should take advantage of that.
--
-- data _⇀I_ {ℓ} : Set ℓ → Set ℓ → Set (lsuc ℓ) where
--   idI   : ∀ {A}   → (A ⇀I A)
--   ∅I    : ∀ {A B} → (A ⇀I B)
--   singI : ∀ {A B} → (A ⇀ B) → (A ⇀I B)
--   _∙I_  : ∀ {A B C} → (B ⇀I C) → (A ⇀I B) → (A ⇀I C)

-- ⌊_⌋ : ∀ {ℓ} {A B : Set ℓ} → (A ⇀I B) → (A ⇀ B)
-- ⌊ idI ⌋     = id
-- ⌊ ∅I ⌋      = ∅
-- ⌊ singI f ⌋ = f
-- ⌊ f ∙I g ⌋  = ⌊ f ⌋ ∙ ⌊ g ⌋

----------------------------------------------------------------------
-- Attempt 2.

-- An (A ⇀I B) looks like an alternating composition of partial
--   functions A ⇀ B ⇀ A ⇀ B ⇀ ... ⇀ B, but which explicitly records
--   the internal structure.

data _⇀I_ {ℓ} (A B : Set ℓ) : Set ℓ where
  singI : (A ⇀ B) → (A ⇀I B)
  snocI : (A ⇀I B) → (B ⇀ A) → (A ⇀ B) → (A ⇀I B)
    -- Note, we allow individual instances of snocI to contain
    -- *different* partial functions, to allow for modeling e.g. the
    -- thing where we plug the "hole" with a flipped version of the
    -- partial bijection built so far.

-- Interpret an (A ⇀I B) down to an (A ⇀ B).
⌊_⌋ : ∀ {ℓ} {A B : Set ℓ} → (A ⇀I B) → (A ⇀ B)
⌊ singI     h ⌋ = h
⌊ snocI i g h ⌋ = h ∙ g ∙ ⌊ i ⌋

_≈I_ : ∀ {ℓ} {A B : Set ℓ} → Rel (A ⇀I B) ℓ
f ≈I g = ⌊ f ⌋ ≈ ⌊ g ⌋

isEquivalence : ∀ {ℓ} {A B : Set ℓ} → IsEquivalence (_≈I_ {ℓ} {A} {B})
isEquivalence = record
  { refl  = ≈-refl
  ; sym   = ≈-sym
  ; trans = ≈-trans
  }

-- b is in the orbit of a under f (written 'b ∈orb⟨ f ⟩ a') if b
-- occurs somewhere along the path followed by a under the composed
-- partial function f.  That is, if f looks like
--
--   ... ∙ h₂ ∙ g₂ ∙ h₁ ∙ g₁ ∙ h
--
-- then b is in the orbit of a if either b = h a, or b = (h₁g₁h) a, or
-- b = (h₂g₂h₁g₁h) a, etc.

data _∈orb⟨_⟩_ {ℓ} {A B : Set ℓ} : B → (A ⇀I B) → A → Set ℓ where
  start : ∀ {h : A ⇀ B} {a b} → h a ≡ just b → b ∈orb⟨ singI h ⟩ a
  end   : ∀ {f : A ⇀I B} {g : B ⇀ A} {h : A ⇀ B} {a a′ : A} {b′ b : B} →
          b′ ∈orb⟨ f ⟩ a → g b′ ≡ just a′ → h a′ ≡ just b →
          b ∈orb⟨ snocI f g h ⟩ a
  mid   : ∀ {f : A ⇀I B} {g : B ⇀ A} {h : A ⇀ B} {a : A} {b : B} →
          b ∈orb⟨ f ⟩ a → b ∈orb⟨ snocI f g h ⟩ a

-- Let's see if we can prove a small lemma as a sanity check: if the
-- interpretation of f is defined at a, then its output is in the
-- orbit of a.

outputInOrbit : ∀ {ℓ} {A B : Set ℓ} {a : A} {b : B}
  (f : A ⇀I B) → ⌊ f ⌋ a ≡ just b → b ∈orb⟨ f ⟩ a
outputInOrbit (singI h)     eq = start eq
outputInOrbit {a = a} (snocI f g h) eq with ⌊ f ⌋ a | inspect ⌊ f ⌋ a
outputInOrbit (snocI f g h) () | nothing | _
outputInOrbit (snocI f g h) eq | just b′ | _ with g b′ | inspect g b′
outputInOrbit (snocI f g h) () | just b′ | _ | nothing | _
outputInOrbit (snocI f g h) eq | just b′ | [ fa≡ ] | just a′ | [ ga≡ ]
  = end (outputInOrbit f fa≡) ga≡ eq

-- Yes!  That seems to work at least.

-- Hmm, but ultimately we want this to be with partial *bijections*
-- not just partial *functions*.  For example, we want to prove things
-- about orbits being disjoint, which is not the case for partial
-- functions.
