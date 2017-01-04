module PartialFunctions where

open import Level renaming (zero to lzero)

open import Function using (const) renaming (_∘_ to _∘ᶠ_)

open import Data.Fin using (Fin) renaming (zero to fz ; suc to fs)
open import Data.Empty
open import Relation.Nullary
open import Data.Unit using (⊤ ; tt)
open import Data.Bool
open import Data.Sum as Sum

open import Data.Maybe using (Maybe ; just ; nothing)
import Data.Maybe as Maybe

open import Category.Monad

open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality using ([_] ; inspect ; sym ; cong)

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

setoid : ∀ {ℓ} (A B : Set ℓ) → Setoid ℓ ℓ
setoid A B = record
  { Carrier       = A ⇀ A
  ; _≈_           = _≈_
  ; isEquivalence = isEquivalence
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

dom-resp-≈ : ∀ {ℓ} {A B : Set ℓ} {f g : A ⇀ B} → f ≈ g → dom f ≈ dom g
dom-resp-≈ {f = f} {g = g} f≈g a rewrite f≈g a with g a
dom-resp-≈ f≈g a | just _  = refl
dom-resp-≈ f≈g a | nothing = refl

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

-- Need a better version: give it two pfuns + proof of compatibility,
-- and get back their merge + a proof that both input pfuns are
-- sub-pfuns of the result, or both compatible with it, or something like that

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
∣∙ f g h a | just b with f b
∣∙ f g h a | just b | just _  = refl
∣∙ f g h a | just b | nothing = refl

-- ... but NOT from the left.  Here is a counterexample.
¬∙∣ : ¬ ({A B C : Set} → (f : B ⇀ C) → (g h : A ⇀ B) → f ∙ (g ∣ h) ≈ (f ∙ g) ∣ (f ∙ h))
¬∙∣ P with (P {⊤} {Bool} {⊤}
              (λ { false → just tt ; _ → nothing })
              (const (just true))
              (const (just false)))
           tt
¬∙∣ P | ()

-- However, we can prove a weaker left distribution law using ⊑ in
-- place of ≈, see below.

dom-∣ : ∀ {ℓ} {A B : Set ℓ} {f g : A ⇀ B} → dom (f ∣ g) ≈ dom f ∣ dom g
dom-∣ {f = f} a with f a
dom-∣         _ | just _ = refl
dom-∣ {g = g} a | nothing with g a
dom-∣         _ | nothing | just _  = refl
dom-∣         _ | nothing | nothing = refl

∣-resp-≈ : ∀ {ℓ} {A B : Set ℓ} {f g h k : A ⇀ B} → f ≈ g → h ≈ k → (f ∣ h) ≈ (g ∣ k)
∣-resp-≈ {f = f} {g = g} f≈g h≈k a with f a | g a | f≈g a | h≈k a
∣-resp-≈ f≈g h≈k a | just _  | just _  | eq₁ | _   = eq₁
∣-resp-≈ f≈g h≈k a | just _  | nothing | ()  | _
∣-resp-≈ f≈g h≈k a | nothing | just _  | ()  | _
∣-resp-≈ f≈g h≈k a | nothing | nothing | _   | eq₂ = eq₂

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

⊑M-antisym : {A : Set} (x y : Maybe A) → x ⊑M y → y ⊑M x → x ≡ y
⊑M-antisym (just _) (just _) refl _  = refl
⊑M-antisym (just _) nothing  ()
⊑M-antisym nothing  (just x)  _    ()
⊑M-antisym nothing  nothing   _    _ = refl

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
    ; trans         = ⊑-trans _ _ _
    }
  }
  where
    ⊑-reflexive : _≈_ ⇒ _⊑_
    ⊑-reflexive i≈j a rewrite (i≈j a) = ⊑M-refl

⊑-antisym : {A B : Set} (f g : A ⇀ B) → f ⊑ g → g ⊑ f → f ≈ g
⊑-antisym f g f⊑g g⊑f = λ a → ⊑M-antisym (f a) (g a) (f⊑g a) (g⊑f a)

⊑-Poset : Set → Set → Poset lzero lzero lzero
⊑-Poset A B = record
  { Carrier        = A ⇀ B
  ; _≈_            = _≈_
  ; _≤_            = _⊑_
  ; isPartialOrder = record
    { isPreorder = Preorder.isPreorder (⊑-Preorder A B)
    ; antisym    = ⊑-antisym _ _
    }
  }

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

inl : ∀ {ℓ} {A B : Set ℓ} → (A ⇀ (A ⊎ B))
inl a = just (inj₁ a)

inr : ∀ {ℓ} {A B : Set ℓ} → (B ⇀ (A ⊎ B))
inr b = just (inj₂ b)

pullMaybe : {A B : Set} → (Maybe A ⊎ Maybe B) ⇀ (A ⊎ B)
pullMaybe = [ Maybe.map inj₁ , Maybe.map inj₂ ]

_+_ : {A₀ B₀ A₁ B₁ : Set} → (A₀ ⇀ B₀) → (A₁ ⇀ B₁) → ((A₀ ⊎ A₁) ⇀ (B₀ ⊎ B₁))
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

+-resp-≈ : {A₀ A₁ B₀ B₁ : Set} {f g : A₀ ⇀ B₀} {h k : A₁ ⇀ B₁}
         → f ≈ g → h ≈ k → (f + h) ≈ (g + k)
+-resp-≈ f≈g h≈k (inj₁ a₀) rewrite (f≈g a₀) = refl
+-resp-≈ f≈g h≈k (inj₂ a₁) rewrite (h≈k a₁) = refl

dom-+ : {A₀ A₁ B₀ B₁ : Set} {f : A₀ ⇀ B₀} {g : A₁ ⇀ B₁}
      → dom (f + g) ≈ dom f + dom g
dom-+ {f = f} (inj₁ a₀) with f a₀
dom-+         (inj₁ a₀) | just _  = refl
dom-+         (inj₁ a₀) | nothing = refl
dom-+ {g = g} (inj₂ a₁) with g a₁
dom-+         (inj₂ a₁) | just _  = refl
dom-+         (inj₂ a₁) | nothing = refl

----------------------------------------------------------------------
-- Compatibility
----------------------------------------------------------------------

-- Compatibility of partial functions.
_∥_ : {A B : Set} → Rel (A ⇀ B) lzero
f ∥ g = (f ∙ dom g ≈ g ∙ dom f)

∥-refl : {A B : Set} {f : A ⇀ B} → f ∥ f
∥-refl = λ _ → refl

∥-sym : {A B : Set} {f g : A ⇀ B} → f ∥ g → g ∥ f
∥-sym f∥g = λ a → sym (f∥g a)

-- Compatibility is NOT transitive, since being compatible says
-- nothing about what happens *outside* the intersection of domains.
-- So if h is compatible with g, it may still be incompatible with f
-- on some part of the domain that is not in g's domain --- the fact
-- that g is compatible with f says nothing about that part of the
-- domain.
--
-- The counterexample is with A = B = Fin 3.  f maps 0->0, 1->1; g
-- maps 1->1, 2->2; h maps 0->1, 2->2.
¬∥-trans : ¬({A B : Set} {f g h : A ⇀ B} → f ∥ g → g ∥ h → f ∥ h)
¬∥-trans P with (P {Fin 3} {Fin 3}
                   {λ { (fs (fs fz)) → nothing ; x → just x }}
                   {λ { fz → nothing ; x → just x }}
                   {λ { fz → just (fs fz)
                      ; (fs (fs fz)) → just (fs (fs fz))
                      ; _ → nothing
                      }}
                   (λ { fz → refl ; (fs fz) → refl ; (fs (fs fz)) → refl ; (fs (fs (fs ()))) })
                   (λ { fz → refl ; (fs fz) → refl ; (fs (fs fz)) → refl ; (fs (fs (fs ()))) }))
                fz
¬∥-trans P | ()

-- For compatible partial functions, join is commutative, i.e. unbiased.
compat-join-commute : {A B : Set} {f g : A ⇀ B} → f ∥ g → (f ∣ g ≈ g ∣ f)
compat-join-commute {f = f} {g = g} f∥g a with f a | g a | inspect f a | inspect g a | f∥g a
  -- The first three cases are true without compatibility.
compat-join-commute f∥g a | just _  | nothing | _ | _ | _ = refl
compat-join-commute f∥g a | nothing | just _  | _ | _ | _ = refl
compat-join-commute f∥g a | nothing | nothing | _ | _ | _ = refl
  -- Compatibility says what happens where both functions are defined:
  -- they must be equal.
compat-join-commute f∥g a | just b₁ | just b₂ | [ eq₁ ]  | [ eq₂ ] | fa≡ga
  rewrite sym eq₁ | sym eq₂ = fa≡ga

-- XXX A nice lemma to have, we convinced ourselves it is true.
-- Should give it a better name.
foo : {A B C : Set} (f h : B ⇀ C) (g k : A ⇀ B) → f ∥ h → g ∥ k → (f ∙ g) ∥ (h ∙ k)
foo f h g k f∥h g∥k = {!!}

-- Is this even true??
-- postulate ∣-abides-∙-compat : {A B C : Set} {f h : B ⇀ C} {g k : A ⇀ B}
--                   → f ∥ h → g ∥ k → (f ∙ g) ∣ (h ∙ k) ≈ (f ∣ h) ∙ (g ∣ k)
-- ∣-abides-∙-compat = {!!}

-- Hmmm... NO, it isn't true!

¬∣-abides-∙-compat-≈ :
  ¬( {A B C : Set} {f h : B ⇀ C} {g k : A ⇀ B}
     → f ∥ h → g ∥ k → (f ∙ g) ∣ (h ∙ k) ≈ (f ∣ h) ∙ (g ∣ k))
¬∣-abides-∙-compat-≈ P
  with P {Bool} {Bool} {Bool}
         {f = λ { false → just false ; _ → nothing }}
         {h = λ { true → just true ; _ → nothing }}
         {g = λ { true → just true ; _ → nothing }}
         {k = λ { false → just false ; _ → nothing }}
         (λ { false → refl ; true → refl })
         (λ { false → refl ; true → refl })
         true
¬∣-abides-∙-compat-≈ P | ()


-- XXX But the above is probably true when weakened to ⊑.  Prove this!

∣-abides-∙-compat : {A B C : Set} {f h : B ⇀ C} {g k : A ⇀ B}
                   → f ∥ h → g ∥ k → (f ∙ g) ∣ (h ∙ k) ⊑ (f ∣ h) ∙ (g ∣ k)
∣-abides-∙-compat = {!!}




-- Another attempt

-- blerg

-- ∣-abides-∙-compat : {A B : Set} {f g : A ⇀ B} {f⁻¹ g⁻¹ : B ⇀ A}
--                   → f⁻¹ ∥ g⁻¹ → f ∥ g
--                   → (f⁻¹ ∣ g⁻¹) ∙ (f ∣ g) ≈ (dom f ∣ dom g)
-- ∣-abides-∙-compat {f = f} {g = g} c⁻¹ c a with f a | inspect f a | g a | inspect g a | c a
-- ∣-abides-∙-compat c⁻¹ c a | nothing | q | nothing | s | t = refl
-- ∣-abides-∙-compat {f⁻¹ = f⁻¹} {g⁻¹ = g⁻¹} c⁻¹ c a | just b | q | r | s | t
--   with f⁻¹ b | inspect f⁻¹ b | g⁻¹ b | inspect g⁻¹ b | c⁻¹ b
-- ∣-abides-∙-compat c⁻¹ c a | just b | q | r | s | t | just x | [ eq ] | just x₁ | [ eq₁ ] | y = {!!}
-- ∣-abides-∙-compat c⁻¹ c a | just b | q | r | s | t | just x | [ eq ] | nothing | [ eq₁ ] | y = {!!}
-- ∣-abides-∙-compat c⁻¹ c a | just b | q | r | s | t | nothing | v | w | x | y = {!!}
-- ∣-abides-∙-compat c⁻¹ c a | nothing | q | just x | s | t = {!!}

-- More blerg

-- ∣-abides-∙-compat : {A B : Set} {f g : A ⇀ B} {f⁻¹ g⁻¹ : B ⇀ A}
--                   → f⁻¹ ∥ g⁻¹ → f ∥ g
--                   → (f⁻¹ ∣ g⁻¹) ∙ (f ∣ g) ≈ (dom f ∣ dom g)
-- ∣-abides-∙-compat {f = f} c c⁻¹ a with f a | inspect f a
-- ∣-abides-∙-compat {f⁻¹ = f⁻¹} c c⁻¹ a | just fx | _ with f⁻¹ fx | inspect f⁻¹ fx
-- ∣-abides-∙-compat c c⁻¹ a | just fx | [ eq₁ ] | just ffx | [ eq ] rewrite (sym eq) = {!!}
-- ∣-abides-∙-compat c c⁻¹ a | just fx | eq₁ | nothing | eq₂ = {!!}
-- ∣-abides-∙-compat c c⁻¹ a | nothing | eq₁ = {!!}
