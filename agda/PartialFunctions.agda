module PartialFunctions where

open import Level renaming (zero to lzero)

open import Function using (const) renaming (_∘_ to _∘ᶠ_)

open import Data.Empty
open import Relation.Nullary
open import Data.Unit
open import Data.Bool
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

-- for congruence, see ≈-cong-left and ≈-cong-right below

------------------------------------------------------------
-- Subsets

-- A subset of a set A can be thought of as a partial function A ⇀ A.
Subset : ∀ {ℓ} → Set ℓ → Set ℓ
Subset A = A ⇀ A

-- Complement of a subset.
_† : ∀ {ℓ} {A : Set ℓ} → Subset A → Subset A
(A †) a with A a
... | just _  = nothing
... | nothing = just a

------------------------------------------------------------
-- Some special partial functions

-- The totally undefined partial function.
∅ : ∀ {ℓ} {A B : Set ℓ} → (A ⇀ B)
∅ = const nothing

-- The domain of f is the subset of A on which it is defined.
dom : ∀ {ℓ} {A B : Set ℓ} → (A ⇀ B) → Subset A
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

_∙_ : ∀ {ℓ} {A B C : Set ℓ} → (B ⇀ C) → (A ⇀ B) → (A ⇀ C)
_∙_ = _<=<_
  where
    open RawMonad Maybe.monad

infixr 9 _∙_

∙-assoc : ∀ {ℓ} {A B C D : Set ℓ} (f : C ⇀ D) (g : B ⇀ C) (h : A ⇀ B)
        → (f ∙ g) ∙ h ≈ f ∙ (g ∙ h)
∙-assoc _ g h a with h a
... | nothing = refl
... | just b  with g b
... | nothing = refl
... | just c  = refl

∙-left-id : ∀ {ℓ} {A B : Set ℓ} {f : A ⇀ B} → id ∙ f ≈ f
∙-left-id {f = f} a with f a
... | nothing = refl
... | just _  = refl

∙-right-id : ∀ {ℓ} {A B : Set ℓ} {f : A ⇀ B} → f ∙ id ≈ f
∙-right-id _ = refl

∅-left-zero : ∀ {ℓ} {A B C : Set ℓ} {f : A ⇀ B} → ∅ ∙ f ≈ (∅ {B = C})
∅-left-zero {f = f} a with f a
... | nothing = refl
... | just _  = refl

∅-right-zero : ∀ {ℓ} {A B C : Set ℓ} {f : B ⇀ C} → f ∙ ∅ ≈ (∅ {A = A})
∅-right-zero _ = refl

dom-right-id : ∀ {ℓ} {A B : Set ℓ} {f : A ⇀ B} → f ∙ dom f ≈ f
dom-right-id {f = f} a with f a | inspect f a
dom-right-id a | just _  | [ fa≡b ] = fa≡b
dom-right-id a | nothing | _        = refl

-- The following limited congruence principles have been enough so far.

≈-cong-left : ∀ {ℓ} {A B C : Set ℓ} (h : A ⇀ B) {f g : B ⇀ C} → f ≈ g → f ∙ h ≈ g ∙ h
≈-cong-left h f≈g a with h a
≈-cong-left h f≈g a | nothing = refl
≈-cong-left h f≈g a | just b  = f≈g b

≈-cong-right : ∀ {ℓ} {A B C : Set ℓ} (f : B ⇀ C) {g h : A ⇀ B} → g ≈ h → f ∙ g ≈ f ∙ h
≈-cong-right f g≈h a rewrite g≈h a = refl

----------------------------------------------------------------------
-- Join
----------------------------------------------------------------------

-- Left-biased join of partial functions.
_∣_ : ∀ {ℓ} {A B : Set ℓ} → (A ⇀ B) → (A ⇀ B) → (A ⇀ B)
_∣_ {ℓ} f g a = f a ∣M g a
  where
    open RawMonadPlus (Maybe.monadPlus {f = ℓ}) renaming (_∣_ to _∣M_)

-- Join is associative.
∣-assoc : ∀ {ℓ} {A B : Set ℓ} → (f g h : A ⇀ B) → (f ∣ g) ∣ h ≈ f ∣ (g ∣ h)
∣-assoc f g h a with f a
∣-assoc f g h a | just _ = refl
∣-assoc f g h a | nothing with g a
∣-assoc f g h a | nothing | just _  = refl
∣-assoc f g h a | nothing | nothing = refl

-- Composition distributes over join from the right...
∣∙ : ∀ {ℓ} {A B C : Set ℓ} → (f g : B ⇀ C) → (h : A ⇀ B) → (f ∣ g) ∙ h ≈ (f ∙ h) ∣ (g ∙ h)
∣∙ f g h a with h a
∣∙ f g h a | nothing = refl
∣∙ f g h a | just b  with f b
∣∙ f g h a | just b | just _  = refl
∣∙ f g h a | just b | nothing = refl

-- ... but NOT from the left.  Here is a counterexample.
¬∙∣ : ¬ ({A B C : Set} → (f : B ⇀ C) → (g h : A ⇀ B) → f ∙ (g ∣ h) ≈ (f ∙ g) ∣ (f ∙ h))
¬∙∣ P with (P (λ { false → just tt ; _ → nothing })
              (const (just true))
              (const (just false)))
           tt
¬∙∣ P | ()

-- However, we can prove a weaker left distribution law using ⊑ in
-- place of ≈, see below.

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

⊑-mono-left : {A B C : Set} (h : A ⇀ B) {f g : B ⇀ C}
  → f ⊑ g → f ∙ h ⊑ g ∙ h
⊑-mono-left h f⊑g a with h a
... | just b  = f⊑g b
... | nothing = tt

⊑-mono-right : {A B C : Set} (h : B ⇀ C) {f g : A ⇀ B}
  → f ⊑ g → h ∙ f ⊑ h ∙ g
⊑-mono-right h {f} {g} f⊑g a with f a | g a | f⊑g a
... | just x  | just y  | x≡y rewrite x≡y = ⊑M-refl
... | just _  | nothing | ()
... | nothing | _       | _               = tt

dom⊑id : {A B : Set} {f : A ⇀ B} → dom f ⊑ id
dom⊑id {f = f} a with f a
dom⊑id a | just _  = refl
dom⊑id a | nothing = tt

-- Composition does not distribute over ∣ from the left (see
-- counterexample above), but we can say that distributing can only
-- make things more defined.
∙∣ : {A B C : Set} → (f : B ⇀ C) → (g h : A ⇀ B) → f ∙ (g ∣ h) ⊑ (f ∙ g) ∣ (f ∙ h)
∙∣ f g h a with g a | h a
∙∣ f g h a | nothing | _ = ⊑M-refl
∙∣ f g h a | just b  | _ with f b
∙∣ f g h a | just b  | _ | just _  = refl
∙∣ f g h a | just b  | _ | nothing = tt

-- | ⊑ is NOT monotonic on the left with respect to ∣ ...
¬-⊑-mono-∣-left : ¬({A B : Set} (h : A ⇀ B) {f g : A ⇀ B} → f ⊑ g → f ∣ h ⊑ g ∣ h)
¬-⊑-mono-∣-left P
  with P {⊤} (const (just true)) {const nothing} {const (just false)} (λ a → a) tt
¬-⊑-mono-∣-left P | ()

-- ... but it is on the right.
⊑-mono-∣-right : {A B : Set} (h : A ⇀ B) {f g : A ⇀ B} → f ⊑ g → h ∣ f ⊑ h ∣ g
⊑-mono-∣-right h f⊑g a with h a
⊑-mono-∣-right h f⊑g a | just x  = refl
⊑-mono-∣-right h f⊑g a | nothing = f⊑g a

∣-right : {A B : Set} {f g : A ⇀ B} → f ⊑ f ∣ g
∣-right {f = f} a with f a
∣-right a | just x  = refl
∣-right a | nothing = tt

----------------------------------------------------------------------
-- Some lemmas about subsets
----------------------------------------------------------------------

∙† : ∀ {A : Set} {X Y : Subset A} → (X † ∙ Y †) ⊑ (X ∙ Y) †
∙† {Y = Y} a with Y a
∙†         a | just _ = tt
∙† {X = X} a | nothing with X a
∙†         a | nothing | just _  = tt
∙†         a | nothing | nothing = refl

subset-idem : {A : Set} {X : Subset A} → X ⊑ id → X ∙ X ≈ X
subset-idem {X = X} X⊑id a with X a | inspect X a
subset-idem         X⊑id a | nothing  | _       = refl
subset-idem {X = X} X⊑id a | just a'  | [ eq ] with X⊑id a
subset-idem {X = X} X⊑id a | just _   | [ eq ] | Xa⊑ rewrite eq | Xa⊑ = eq

†⊑ : ∀ {A : Set} {X : Subset A} → X ⊑ id → X † ⊑ id
†⊑ {X = X} X⊑id a with X a
†⊑ X⊑id a | just _  = tt
†⊑ X⊑id a | nothing = refl

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

∙-abides-+ :
  {A₀ B₀ C₀ A₁ B₁ C₁ : Set}
  {f : B₀ ⇀ C₀} {g : A₀ ⇀ B₀} {h : B₁ ⇀ C₁} {k : A₁ ⇀ B₁}
  → (f ∙ g) + (h ∙ k) ≈ (f + h) ∙ (g + k)
∙-abides-+ {g = g} (inj₁ a) with g a
∙-abides-+         (inj₁ _) | nothing = refl
∙-abides-+ {f = f} (inj₁ _) | just b with f b
∙-abides-+         (inj₁ _) | just _ | just _  = refl
∙-abides-+         (inj₁ _) | just _ | nothing = refl
∙-abides-+ {k = k} (inj₂ a) with k a
∙-abides-+         (inj₂ _) | nothing = refl
∙-abides-+ {h = h} (inj₂ _) | just b with h b
∙-abides-+         (inj₂ _) | just _ | just _  = refl
∙-abides-+         (inj₂ _) | just _ | nothing = refl

----------------------------------------------------------------------
-- Compatibility
----------------------------------------------------------------------

-- XXX comment

Compatible : {A B : Set} → Rel (A ⇀ B) lzero
Compatible f g = (f ∙ dom g ≈ g ∙ dom f)
