module PartialFunctions where

open import Level renaming (zero to lzero)

open import Function using (const) renaming (_∘_ to _∘ᶠ_)

open import Data.Empty
open import Data.Unit
open import Data.Sum as Sum

open import Data.Maybe as Maybe

open import Category.Monad

open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality using ([_] ; inspect)

----------------------------------------------------------------------
-- Partial functions
----------------------------------------------------------------------

_⇀_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
A ⇀ B = A → Maybe B

infix 1 _⇀_

------------------------------------------------------------
-- Equivalence of partial functions

-- Equivalence of partial functions is defined pointwise.
_≈_ : ∀ {ℓ} {A B : Set ℓ} → Rel (A ⇀ B) ℓ
f ≈ g = ∀ a → f a ≡ g a

infix 0 _≈_

≈-refl : ∀ {ℓ} {A B : Set ℓ} {f : A ⇀ B} → f ≈ f
≈-refl = λ _ → refl

≈-sym : ∀ {ℓ} {A B : Set ℓ} {f g : A ⇀ B} → f ≈ g → g ≈ f
≈-sym f≈g a rewrite f≈g a = refl

≈-trans : ∀ {ℓ} {A B : Set ℓ} {f g h : A ⇀ B} → f ≈ g → g ≈ h → f ≈ h
≈-trans f≈g g≈h a rewrite f≈g a | g≈h a = refl

isEquivalence : ∀ {ℓ} {A B : Set ℓ} → IsEquivalence (_≈_ {ℓ} {A} {B})
isEquivalence = record
  { refl  = ≈-refl
  ; sym   = ≈-sym
  ; trans = ≈-trans
  }

-- for congruence, see ≈-cong-left below

------------------------------------------------------------
-- Some special partial functions

-- The totally undefined partial function.
∅ : ∀ {ℓ} {A B : Set ℓ} → (A ⇀ B)
∅ = const nothing

-- dom f is the identity on the domain of f, and undefined elsewhere.
dom : ∀ {ℓ} {A B : Set ℓ} → (A ⇀ B) → (A ⇀ A)
dom f a with f a
dom f a | just _  = just a
dom f a | nothing = nothing

domdom : ∀ {ℓ} {A B : Set ℓ} {f : A ⇀ B} → dom (dom f) ≈ dom f
domdom {f = f} a with f a
domdom a | just _  = refl
domdom a | nothing = refl

-- Note that given our choice of representation, the range of a
-- partial function is not computable.

------------------------------------------------------------
-- The category of partial functions

-- Identity and composition for partial functions.
id : ∀ {ℓ} {A : Set ℓ} → (A ⇀ A)
id = just

_•_ : ∀ {ℓ} {A B C : Set ℓ} → (B ⇀ C) → (A ⇀ B) → (A ⇀ C)
_•_ = _<=<_
  where
    open RawMonad Maybe.monad

infixr 9 _•_

•-assoc : ∀ {ℓ} {A B C D : Set ℓ} (f : C ⇀ D) (g : B ⇀ C) (h : A ⇀ B)
        → (f • g) • h ≈ f • (g • h)
•-assoc _ g h a with h a
... | nothing = refl
... | just b  with g b
... | nothing = refl
... | just c  = refl

•-left-id : ∀ {ℓ} {A B : Set ℓ} {f : A ⇀ B} → id • f ≈ f
•-left-id {f = f} a with f a
... | nothing = refl
... | just _  = refl

•-right-id : ∀ {ℓ} {A B : Set ℓ} {f : A ⇀ B} → f • id ≈ f
•-right-id _ = refl

∅-left-zero : ∀ {ℓ} {A B C : Set ℓ} {f : A ⇀ B} → ∅ • f ≈ (∅ {B = C})
∅-left-zero {f = f} a with f a
... | nothing = refl
... | just _  = refl

∅-right-zero : ∀ {ℓ} {A B C : Set ℓ} {f : B ⇀ C} → f • ∅ ≈ (∅ {A = A})
∅-right-zero _ = refl

dom-right-id : ∀ {ℓ} {A B : Set ℓ} {f : A ⇀ B} → f • dom f ≈ f
dom-right-id {f = f} a with f a | inspect f a
dom-right-id a | just _  | [ fa≡b ] = fa≡b
dom-right-id a | nothing | _        = refl

-- The following limited congruence principles have been enough so far.

≈-cong-left : ∀ {ℓ} {A B C : Set ℓ} (h : A ⇀ B) {f g : B ⇀ C} → f ≈ g → f • h ≈ g • h
≈-cong-left h f≈g a with h a
≈-cong-left h f≈g a | nothing = refl
≈-cong-left h f≈g a | just b  = f≈g b

≈-cong-right : ∀ {ℓ} {A B C : Set ℓ} (f : B ⇀ C) {g h : A ⇀ B} → g ≈ h → f • g ≈ f • h
≈-cong-right f g≈h a rewrite g≈h a = refl

----------------------------------------------------------------------
-- Definedness partial order for partial functions
----------------------------------------------------------------------

-- Definedness partial order for Maybe

_⊑M_ : {B : Set} → Rel (Maybe B) lzero
just a ⊑M just b  = a ≡ b
just x ⊑M nothing = ⊥
nothing ⊑M b      = ⊤

infix 4 _⊑M_

⊑M-refl : {B : Set} {b : Maybe B} → b ⊑M b
⊑M-refl {b = nothing}  = tt
⊑M-refl {b = just _ } = refl

⊑M-trans : {A : Set} (x y z : Maybe A) → x ⊑M y → y ⊑M z → x ⊑M z
⊑M-trans (just x) (just y) z x⊑y y⊑z rewrite x⊑y = y⊑z
⊑M-trans (just x) nothing z () y⊑z
⊑M-trans nothing y z x⊑y y⊑z = tt

-- Order for partial functions is just pointwise lifting of order on Maybe

_⊑_ : {A B : Set} → Rel (A ⇀ B) lzero
f ⊑ g = ∀ a → f a ⊑M g a

infix 4 _⊑_

-- ⊑ is reflexive & transitive

⊑-refl : {A B : Set} {f : A ⇀ B} → f ⊑ f
⊑-refl = λ _ → ⊑M-refl

⊑-trans : {A B : Set} (f g h : A ⇀ B) → f ⊑ g → g ⊑ h → f ⊑ h
⊑-trans f g h f⊑g g⊑h = λ a → ⊑M-trans (f a) (g a) (h a) (f⊑g a) (g⊑h a)

⊑-Preorder : Set → Set → Preorder lzero lzero lzero
⊑-Preorder A B = record
  { Carrier = A ⇀ B
  ; _≈_ = _≈_
  ; _∼_ = _⊑_
  ; isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive     = ⊑-reflexive
    ; trans         = λ {i} {j} {k} → ⊑-trans i j k
    }
  }
  where
    ⊑-reflexive : _≈_ ⇒ _⊑_
    ⊑-reflexive i≈j a rewrite (i≈j a) = ⊑M-refl

-- ...and also monotonic wrt. composition

⊑-mono-left : {A B C : Set} (f g : B ⇀ C) (h : A ⇀ B)
  → f ⊑ g → f • h ⊑ g • h
⊑-mono-left f g h f⊑g a with h a
... | just b  = f⊑g b
... | nothing = tt

⊑-mono-right : {A B C : Set} (f g : A ⇀ B) (h : B ⇀ C)
  → f ⊑ g → h • f ⊑ h • g
⊑-mono-right f g h f⊑g a with f a | g a | f⊑g a
... | just x  | just y  | x≡y rewrite x≡y = ⊑M-refl
... | just _  | nothing | ()
... | nothing | _       | _               = tt

dom⊑id : {A B : Set} {f : A ⇀ B} → dom f ⊑ id
dom⊑id {f = f} a with f a
dom⊑id a | just _  = refl
dom⊑id a | nothing = tt

----------------------------------------------------------------------
-- Sums
----------------------------------------------------------------------

inl : ∀ {ℓ} {A B : Set ℓ} → (A ⇀ A ⊎ B)
inl a = just (inj₁ a)

inr : ∀ {ℓ} {A B : Set ℓ} → (B ⇀ A ⊎ B)
inr b = just (inj₂ b)

pullMaybe : {A B : Set} → Maybe A ⊎ Maybe B ⇀ A ⊎ B
pullMaybe = [ Maybe.map inj₁ , Maybe.map inj₂ ]

_+_ : {A₀ B₀ A₁ B₁ : Set} → (A₀ ⇀ B₀) → (A₁ ⇀ B₁) → (A₀ ⊎ A₁ ⇀ B₀ ⊎ B₁)
f + g = pullMaybe ∘ᶠ Sum.map f g

•-abides-+ :
  {A₀ B₀ C₀ A₁ B₁ C₁ : Set}
  {f : B₀ ⇀ C₀} {g : A₀ ⇀ B₀} {h : B₁ ⇀ C₁} {k : A₁ ⇀ B₁}
  → (f • g) + (h • k) ≈ (f + h) • (g + k)
•-abides-+ {g = g} (inj₁ a) with g a
•-abides-+         (inj₁ _) | nothing = refl
•-abides-+ {f = f} (inj₁ _) | just b with f b
•-abides-+         (inj₁ _) | just _ | just _  = refl
•-abides-+         (inj₁ _) | just _ | nothing = refl
•-abides-+ {k = k} (inj₂ a) with k a
•-abides-+         (inj₂ _) | nothing = refl
•-abides-+ {h = h} (inj₂ _) | just b with h b
•-abides-+         (inj₂ _) | just _ | just _  = refl
•-abides-+         (inj₂ _) | just _ | nothing = refl
