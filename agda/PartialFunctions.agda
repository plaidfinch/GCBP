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
-- Overview
----------------------------------------------------------------------

-- In this file, we:

-- 1. Define partial functions A ⇀ B
--
-- 2. Define an equivalence relation ≈ on A ⇀ B
--
-- 3. Define the 'dom' operator and some properties (it is idempotent
--    and respects ≈)
--
-- 4. Define the category of partial functions: id, composition, and
--    associated laws
--
-- 5. Define the left-biased join and some properties (associative,
--    respects ≈, composition distributes over it from the right, dom
--    distributes over it)

-- 6. Define the poset of partial functions related by pointwise
--    definedness ⊑, and some related monotonicity properties of
--    composition and join.

-- 7. Define the parallel sum operator + on partial functions and
--    prove some properties (respects ≈, abides with composition,
--    abides with join, dom distributes over it)
--
-- 8. Define the compatibility relation ∥ on partial functions: it is
--    reflexive and symmetric but not transitive; join is commutative
--    on compatible functions; composition and sum both preserve
--    compatibility; and an abides-like law for composition and join
--    which requires some compatibility side conditions.


----------------------------------------------------------------------
-- 1. Partial functions
----------------------------------------------------------------------

-- A partial function from A to B, denoted A ⇀ B, can be represented
-- as a total function from A to Maybe B.

_⇀_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
A ⇀ B = A → Maybe B

infix 1 _⇀_

------------------------------------------------------------
-- 2. Equivalence of partial functions
------------------------------------------------------------

-- We begin by defining an equivalence relation on partial functions,
-- which is simply pointwise propositional equality.

_≈_ : ∀ {ℓ} {A B : Set ℓ} → Rel (A ⇀ B) ℓ
f ≈ g = ∀ a → f a ≡ g a

infix 0 _≈_

-- ≈ is an equivalence relation: it is reflexive, symmetric, and transitive.

≈-refl : ∀ {ℓ} {A B : Set ℓ} {f : A ⇀ B} → f ≈ f
≈-refl = λ _ → refl

≈-sym : ∀ {ℓ} {A B : Set ℓ} {f g : A ⇀ B} → f ≈ g → g ≈ f
≈-sym f≈g a rewrite f≈g a = refl
  -- 'rewrite' is special Agda syntax.  f arg1 arg2 rewrite expr = ...
  -- if 'expr' is a term whose type is a propositional equality, it
  -- rewrites the LHS of the equality to the RHS everywhere in the
  -- goal and the context.  See http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.PatternMatching

≈-trans : ∀ {ℓ} {A B : Set ℓ} {f g h : A ⇀ B} → f ≈ g → g ≈ h → f ≈ h
≈-trans f≈g g≈h a rewrite f≈g a | g≈h a = refl

-- Package up the fact that ≈ is an equivalence relation into a record
-- structure.
isEquivalence : ∀ {ℓ} {A B : Set ℓ} → IsEquivalence (_≈_ {ℓ} {A} {B})
isEquivalence = record
  { refl  = ≈-refl
  ; sym   = ≈-sym
  ; trans = ≈-trans
  }

-- We can also form the setoid of partial functions A ⇀ B under the
-- equivalence relation ≈ , which is sometimes useful for passing to
-- various standard library constructs that are parameterized over an
-- arbitrary setoid.
setoid : ∀ {ℓ} (A B : Set ℓ) → Setoid ℓ ℓ
setoid A B = record
  { Carrier       = A ⇀ B
  ; _≈_           = _≈_
  ; isEquivalence = isEquivalence
  }

------------------------------------------------------------
-- 3. Domains
------------------------------------------------------------

-- A subset of a set A can be represented by a partial function A ⇀
-- A. Note that not every partial function A ⇀ A corresponds to a
-- subset; the idea is to restrict ourselves to those partial
-- functions which are the identity on the elements of A for which
-- they are defined.
Subset : ∀ {ℓ} → Set ℓ → Set ℓ
Subset A = A ⇀ A

-- Complement of a subset.
_† : ∀ {ℓ} {A : Set ℓ} → Subset A → Subset A
(A †) a with A a
... | just _  = nothing
... | nothing = just a

-- The domain of f is the subset of A on which it is defined.
dom : ∀ {ℓ} {A B : Set ℓ} → (A ⇀ B) → Subset A
dom f a with f a
dom f a | just _  = just a
dom f a | nothing = nothing

-- The dom operator is idempotent.
domdom : ∀ {ℓ} {A B : Set ℓ} {f : A ⇀ B} → dom (dom f) ≈ dom f
domdom {f = f} a with f a
domdom a | just _  = refl
domdom a | nothing = refl

-- dom respects equivalence of partial functions.
dom-resp-≈ : ∀ {ℓ} {A B : Set ℓ} {f g : A ⇀ B} → f ≈ g → dom f ≈ dom g
dom-resp-≈ {f = f} {g = g} f≈g a rewrite f≈g a with g a
dom-resp-≈ f≈g a | just _  = refl
dom-resp-≈ f≈g a | nothing = refl

-- Note that given our choice of representation, the *range* of a
-- partial function (in contrast to the domain) is not computable.
-- Given our representation, to decide whether a given element of B is
-- in the range of a given partial function, we would have to be able
-- to enumerate all the elements of A, as well as decide equality on
-- B.

------------------------------------------------------------
-- 4. The category of partial functions
------------------------------------------------------------

-- Partial functions form a category under composition (which is
-- really just the Kleisli category for the Maybe monad).

-- The identity partial function, which is defined everywhere.
id : ∀ {ℓ} {A : Set ℓ} → (A ⇀ A)
id = just

-- Composition of partial functions is just Kleisli composition.
_∙_ : ∀ {ℓ} {A B C : Set ℓ} → (B ⇀ C) → (A ⇀ B) → (A ⇀ C)
_∙_ = _<=<_
  where
    open RawMonad Maybe.monad

infixr 9 _∙_

-- Prove the category laws: ∙ is associative and has id as a left and
-- right identity.

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

-- Some other miscellaneous properties of composition:

-- The totally undefined partial function.
∅ : ∀ {ℓ} {A B : Set ℓ} → (A ⇀ B)
∅ = const nothing

-- The totally undefined partial function, ∅, is a left and right zero
-- for composition.
∅-left-zero : ∀ {ℓ} {A B C : Set ℓ} {f : A ⇀ B} → ∅ ∙ f ≈ (∅ {B = C})
∅-left-zero {f = f} a with f a
... | nothing = refl
... | just _  = refl

∅-right-zero : ∀ {ℓ} {A B C : Set ℓ} {f : B ⇀ C} → f ∙ ∅ ≈ (∅ {A = A})
∅-right-zero _ = refl

-- Composing a partial function on the right with its domain is the
-- identity.
dom-right-id : ∀ {ℓ} {A B : Set ℓ} {f : A ⇀ B} → f ∙ dom f ≈ f
dom-right-id {f = f} a with f a | inspect f a
dom-right-id a | just _  | [ fa≡b ] = fa≡b
dom-right-id a | nothing | _        = refl

-- Equivalence of partial functions is a congruence with respect to
-- composition.

≈-cong-left : ∀ {ℓ} {A B C : Set ℓ} (h : A ⇀ B) {f g : B ⇀ C} → f ≈ g → f ∙ h ≈ g ∙ h
≈-cong-left h f≈g a with h a
≈-cong-left h f≈g a | nothing = refl
≈-cong-left h f≈g a | just b  = f≈g b

≈-cong-right : ∀ {ℓ} {A B C : Set ℓ} (f : B ⇀ C) {g h : A ⇀ B} → g ≈ h → f ∙ g ≈ f ∙ h
≈-cong-right f g≈h a rewrite g≈h a = refl

----------------------------------------------------------------------
-- 5. Join
----------------------------------------------------------------------

-- XXX do this later?
-- Need a better version: give it two pfuns + proof of compatibility,
-- and get back their merge + a proof that both input pfuns are
-- sub-pfuns of the result, or both compatible with it, or something like that

-- The left-biased join of partial functions.  (f ∣ g) a is equal to f
-- a if f is defined on a, otherwise g a.
--
-- [A note on notation: this is not a pipe character |, 0x7c ASCII,
-- since that is reserved Agda syntax.  Instead it is ∣ , U+2223
-- DIVIDES.  Enter it in emacs Agda mode with \| or \mid .]
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

-- (However, we can prove a weaker left distribution law using ⊑ in
-- place of ≈, see below.)

-- The domain operator distributes over join.
dom-∣ : ∀ {ℓ} {A B : Set ℓ} {f g : A ⇀ B} → dom (f ∣ g) ≈ dom f ∣ dom g
dom-∣ {f = f} a with f a
dom-∣         _ | just _ = refl
dom-∣ {g = g} a | nothing with g a
dom-∣         _ | nothing | just _  = refl
dom-∣         _ | nothing | nothing = refl

-- Join respects partial function equivalence.
∣-resp-≈ : ∀ {ℓ} {A B : Set ℓ} {f g h k : A ⇀ B} → f ≈ g → h ≈ k → (f ∣ h) ≈ (g ∣ k)
∣-resp-≈ {f = f} {g = g} f≈g h≈k a with f a | g a | f≈g a | h≈k a
∣-resp-≈ f≈g h≈k a | just _  | just _  | eq₁ | _   = eq₁
∣-resp-≈ f≈g h≈k a | just _  | nothing | ()  | _
∣-resp-≈ f≈g h≈k a | nothing | just _  | ()  | _
∣-resp-≈ f≈g h≈k a | nothing | nothing | _   | eq₂ = eq₂

----------------------------------------------------------------------
-- 6. Definedness partial order for partial functions
----------------------------------------------------------------------

-- First, the definedness partial order for Maybe:

_⊑M_ : {B : Set} → Rel (Maybe B) lzero
just a  ⊑M just b  = a ≡ b  -- just a ⊑ just b if a ≡ b.
just _  ⊑M nothing = ⊥      -- just _ is not at most as defined as nothing.
nothing ⊑M _       = ⊤      -- nothing is at most as defined as anything else.

infix 4 _⊑M_

-- ⊑M is a partial order (reflexive, transitive, and antisymmetric).

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

-- The definedness order for partial functions is just the pointwise
-- lifting of the order on Maybe.

_⊑_ : {A B : Set} → Rel (A ⇀ B) lzero
f ⊑ g = ∀ a → f a ⊑M g a

infix 4 _⊑_

-- ⊑ is a preorder (reflexive and transitive):

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

-- ⊑ is also a partial order, i.e. poset, since it is also antisymmetric:

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

-- ⊑ is also monotonic wrt. composition:

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

-- The domain operator always produces something which is a
-- subfunction of the identity:

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

-- Also, joining on the right can only make things more defined.
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
-- 7. Sums
----------------------------------------------------------------------

-- The (total) function injecting A into the left side of A ⊎ B
inl : ∀ {ℓ} {A B : Set ℓ} → (A ⇀ (A ⊎ B))
inl a = just (inj₁ a)

-- The (total) function injecting B into the right side of A ⊎ B
inr : ∀ {ℓ} {A B : Set ℓ} → (B ⇀ (A ⊎ B))
inr b = just (inj₂ b)

-- The partial function projecting out the left side of A ⊎ B
projl : ∀ {ℓ} {A B : Set ℓ} → ((A ⊎ B) ⇀ A)
projl (inj₁ a) = just a
projl _        = nothing

-- The partial function projecting out the right side of A ⊎ B
projr : ∀ {ℓ} {A B : Set ℓ} → ((A ⊎ B) ⇀ B)
projr (inj₂ b) = just b
projr _        = nothing

-- A helper partial function, which reflects the explicit Maybe types
-- in the input into its ambient partiality.
pullMaybe : {A B : Set} → (Maybe A ⊎ Maybe B) ⇀ (A ⊎ B)
pullMaybe = [ Maybe.map inj₁ , Maybe.map inj₂ ]

-- The parallel sum of two partial functions.
_+_ : {A₀ B₀ A₁ B₁ : Set} → (A₀ ⇀ B₀) → (A₁ ⇀ B₁) → ((A₀ ⊎ A₁) ⇀ (B₀ ⊎ B₁))
f + g = pullMaybe ∘ᶠ Sum.map f g

-- Abides laws for both composition and join with respect to + (the
-- "big 3").  We'll deal with an abides law for ∙ over ∣ later.

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

∣-abides-+ : {A₀ B₀ A₁ B₁ : Set}
  (f g : A₀ ⇀ B₀) (h k : A₁ ⇀ B₁) → (f ∣ g) + (h ∣ k) ≈ (f + h) ∣ (g + k)
∣-abides-+ f g h k (inj₁ a₀) with f a₀ | g a₀
∣-abides-+ f g h k (inj₁ _ ) | just _  | just _  = refl
∣-abides-+ f g h k (inj₁ _ ) | just _  | nothing = refl
∣-abides-+ f g h k (inj₁ _ ) | nothing | just _  = refl
∣-abides-+ f g h k (inj₁ _ ) | nothing | nothing = refl
∣-abides-+ f g h k (inj₂ a₁) with h a₁ | k a₁
∣-abides-+ f g h k (inj₂ _ ) | just _  | just _  = refl
∣-abides-+ f g h k (inj₂ _ ) | just _  | nothing = refl
∣-abides-+ f g h k (inj₂ _ ) | nothing | just _  = refl
∣-abides-+ f g h k (inj₂ _ ) | nothing | nothing = refl

-- Parallel sum respects equivalence.
+-resp-≈ : {A₀ A₁ B₀ B₁ : Set} {f g : A₀ ⇀ B₀} {h k : A₁ ⇀ B₁}
         → f ≈ g → h ≈ k → (f + h) ≈ (g + k)
+-resp-≈ f≈g h≈k (inj₁ a₀) rewrite (f≈g a₀) = refl
+-resp-≈ f≈g h≈k (inj₂ a₁) rewrite (h≈k a₁) = refl

-- The dom operator distributes over parallel sum.
dom-+ : {A₀ A₁ B₀ B₁ : Set} {f : A₀ ⇀ B₀} {g : A₁ ⇀ B₁}
      → dom (f + g) ≈ dom f + dom g
dom-+ {f = f} (inj₁ a₀) with f a₀
dom-+         (inj₁ a₀) | just _  = refl
dom-+         (inj₁ a₀) | nothing = refl
dom-+ {g = g} (inj₂ a₁) with g a₁
dom-+         (inj₂ a₁) | just _  = refl
dom-+         (inj₂ a₁) | nothing = refl

----------------------------------------------------------------------
-- 8. Compatibility
----------------------------------------------------------------------

-- Compatibility of partial functions.  Intuitively, f and g are
-- compatible if they never disagree at any point where they are both
-- defined.  However, here we give a definition with a higher-level
-- algebraic flavor, that avoids talking about points at all: f and g
-- are compatible if restricting f to the domain of g yields the same
-- partial function as restricting g to the domain of f.
_∥_ : {A B : Set} → Rel (A ⇀ B) lzero
f ∥ g = (f ∙ dom g ≈ g ∙ dom f)

-- Compatibility is reflexive and symmetric.

∥-refl : {A B : Set} {f : A ⇀ B} → f ∥ f
∥-refl = λ _ → refl

∥-sym : {A B : Set} {f g : A ⇀ B} → f ∥ g → g ∥ f
∥-sym f∥g = λ a → sym (f∥g a)

-- If f ⊑ g then f and g are compatible.

⊑-∥ : {A B : Set} (f g : A ⇀ B) → f ⊑ g → f ∥ g
⊑-∥ f g f⊑g a with f a | g a | inspect f a | inspect g a
⊑-∥ f g f⊑g a | just b₁ | just b₂ | [ f≡ ] | [ g≡ ] with f⊑g a
... | pf rewrite f≡ | g≡ = cong just pf
⊑-∥ f g f⊑g a | just _  | nothing | _      | [ g≡ ] = sym g≡
⊑-∥ f g f⊑g a | nothing | just _  | [ f≡ ] | _      = f≡
⊑-∥ f g f⊑g a | nothing | nothing | _      | _      = refl

-- Compatibility is NOT transitive, since being compatible says
-- nothing about what happens *outside* the intersection of domains.
-- So if h is compatible with g, it may still be incompatible with f
-- on some part of the domain that is not in g's domain --- the fact
-- that g is compatible with f says nothing about that part of the
-- domain.
--
-- The counterexample is with A = B = Fin 3.  f maps 0→0, 1→1; g
-- maps 1→1, 2→2; h maps 0→1, 2→2.
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

-- View on the results of compatible partial functions.  This,
-- together with the function viewCompat which constructs elements of
-- this type, makes it a bit easier to make use of compatibility
-- assumptions in the context.
data _-∥-_ {B : Set} : Maybe B → Maybe B → Set where
  None  :           nothing -∥- nothing
  Left  : (b : B) → just b  -∥- nothing
  Right : (b : B) → nothing -∥- just b
  Both  : (b : B) → just b  -∥- just b

viewCompat : {A B : Set} (f g : A ⇀ B) → f ∥ g → (a : A) → (f a) -∥- (g a)
viewCompat f g f∥g a with f a | g a | inspect f a | inspect g a | f∥g a
viewCompat f g f∥g a | nothing | nothing | _ | _ | _ = None
viewCompat f g f∥g a | nothing | just b  | _ | _ | _ = Right b
viewCompat f g f∥g a | just b  | nothing | _ | _ | _ = Left b
viewCompat f g f∥g a | just b₁ | just b₂ | [ eqf ] | [ eqg ] | fa≡ga
  rewrite sym eqf | sym eqg | fa≡ga | eqf = Both b₁

-- This lemma is the key that allows us to give a nice equational
-- reasoning proof that composition preserves compatibility.  For a
-- long time I was at a loss as to what we could say algebraically
-- about dom (f ∙ g).  The answer is not much, *in isolation*.  But
-- when it is composed with something else that's suitably compatible
-- we can indeed distribute the dom operator.
dom-∙ : ∀ {A B C : Set} (f : B ⇀ C) (g h : A ⇀ B) → h ∥ g → h ∙ dom (f ∙ g) ≈ dom f ∙ h ∙ dom g
dom-∙ f g h h∥g a with g a | h a | inspect g a | inspect h a | viewCompat h g h∥g a
dom-∙ f g h h∥g a | just b₁ | just b₂ | [ g≡ ] | [ h≡ ] | p with f b₁ | inspect f b₁
dom-∙ f g h h∥g a | just .b₁ | just .b₁ | [ g≡ ] | [ h≡ ] | Both b₁ | just c  | [ f≡ ] rewrite h≡ | f≡ = refl
dom-∙ f g h h∥g a | just .b₁ | just .b₁ | [ g≡ ] | [ h≡ ] | Both b₁ | nothing | [ f≡ ] rewrite h≡ | f≡ = refl
dom-∙ f g h h∥g a | just b  | nothing | [ g≡ ] | [ h≡ ] | p rewrite h≡ with f b | inspect f b
dom-∙ f g h h∥g a | just b | nothing | [ g≡ ] | [ h≡ ] | p | just c  | [ f≡ ] = h≡
dom-∙ f g h h∥g a | just b | nothing | [ g≡ ] | [ h≡ ] | p | nothing | [ f≡ ] = refl
dom-∙ f g h h∥g a | nothing | ha | [ g≡ ] | [ h≡ ] | p = refl

-- Composition preserves compatibility.
∥-∙ : {A B C : Set} (f h : B ⇀ C) (g k : A ⇀ B) → f ∥ h → g ∥ k → (f ∙ g) ∥ (h ∙ k)
∥-∙ {A = A} {C = C} f h g k f∥h g∥k =
  begin
    (f ∙ g) ∙ dom (h ∙ k)
                                        ≈⟨ ∙-assoc _ _ (dom (h ∙ k)) ⟩
    f ∙ (g ∙ dom (h ∙ k))
                                        ≈⟨ ≈-cong-right f (dom-∙ h k g g∥k) ⟩
    f ∙ (dom h ∙ g ∙ dom k)
                                        ≈⟨ ≈-sym (∙-assoc _ _ (g ∙ dom k)) ⟩
    (f ∙ dom h) ∙ (g ∙ dom k)
                                        ≈⟨ ≈-cong-left (g ∙ dom k) f∥h ⟩
    (h ∙ dom f) ∙ (g ∙ dom k)
                                        ≈⟨ ≈-cong-right (h ∙ dom f) g∥k ⟩
    (h ∙ dom f) ∙ (k ∙ dom g)
                                        ≈⟨ ∙-assoc _ _ (k ∙ dom g) ⟩
    h ∙ (dom f ∙ k ∙ dom g)
                                        ≈⟨ ≈-cong-right h (≈-sym (dom-∙ f g k (∥-sym {f = g} g∥k))) ⟩
    h ∙ (k ∙ dom (f ∙ g))
                                        ≈⟨ ≈-sym (∙-assoc _ _ (dom (f ∙ g))) ⟩
    (h ∙ k) ∙ dom (f ∙ g)
  ∎
  where
    open import Relation.Binary.EqReasoning (setoid A C)

-- Sum preserves compatibility.
∥-+ : {A₀ A₁ B₀ B₁ : Set} (f g : A₀ ⇀ B₀) (h k : A₁ ⇀ B₁) → f ∥ g → h ∥ k → (f + h) ∥ (g + k)
∥-+ {A₀} {A₁} {B₀} {B₁} f g h k f∥g h∥k = begin
  (f + h) ∙ dom (g + k)
                                        ≈⟨ ≈-cong-right (f + h) dom-+ ⟩
  (f + h) ∙ (dom g + dom k)
                                        ≈⟨ ≈-sym ∙-abides-+ ⟩
  (f ∙ dom g) + (h ∙ dom k)
                                        ≈⟨ +-resp-≈ f∥g h∥k ⟩
  (g ∙ dom f) + (k ∙ dom h)
                                        ≈⟨ ∙-abides-+ ⟩
  (g + k) ∙ (dom f + dom h)
                                        ≈⟨ ≈-cong-right (g + k) (≈-sym dom-+) ⟩
  (g + k) ∙ dom (f + h)
  ∎
  where
    open import Relation.Binary.EqReasoning (setoid (A₀ ⊎ A₁) (B₀ ⊎ B₁))

-- Is this even true??
-- postulate ∣-abides-∙-compat : {A B C : Set} {f h : B ⇀ C} {g k : A ⇀ B}
--                   → f ∥ h → g ∥ k → (f ∙ g) ∣ (h ∙ k) ≈ (f ∣ h) ∙ (g ∣ k)

-- NO, it isn't!  Here's a counterexample:

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


-- BUT the above IS true when weakened to ⊑.

∣-abides-∙-compat : {A B C : Set} (f h : B ⇀ C) (g k : A ⇀ B)
                   → f ∥ h → g ∥ k → (f ∙ g) ∣ (h ∙ k) ⊑ (f ∣ h) ∙ (g ∣ k)
∣-abides-∙-compat f h g k f∥h g∥k a with g a | k a | g∥k a | viewCompat g k g∥k a
∣-abides-∙-compat f h g k f∥h g∥k a | just b | ka | g≡k | p with f b | h b | inspect h b
∣-abides-∙-compat f h g k f∥h g∥k a | just b | ka | g≡k | p | just x | hb | _ = refl
∣-abides-∙-compat f h g k f∥h g∥k a | just b | just .b | g≡k | Both .b | nothing | hb | [ h≡ ] rewrite h≡ = ⊑M-refl
∣-abides-∙-compat f h g k f∥h g∥k a | just b | nothing | g≡k | p | nothing | hb | _ = tt
∣-abides-∙-compat f h g k f∥h g∥k a | nothing | just b | g≡k | p with f b | h b | viewCompat f h f∥h b
∣-abides-∙-compat f h g k f∥h g∥k a | nothing | just b₁ | g≡k | p | just b | just .b | Both .b = refl
∣-abides-∙-compat f h g k f∥h g∥k a | nothing | just b | g≡k | p | nothing | just x | q = refl
∣-abides-∙-compat f h g k f∥h g∥k a | nothing | just b | g≡k | p | fb | nothing | q = tt
∣-abides-∙-compat f h g k f∥h g∥k a | nothing | nothing | g≡k | p = tt


-- However, we can force it to be true with some extra side
-- conditions: essentially we need f and h to be "one-sided inverses"
-- to g and k.  It would be really nice to figure out how to write a
-- nicer proof of this.
∣-abides-∙-compat-inv : {A B : Set} (f h : B ⇀ A) (g k : A ⇀ B)
                      → f ∥ h → g ∥ k → (f ∙ g ≈ dom g) → (h ∙ k ≈ dom k) → (f ∙ g) ∣ (h ∙ k) ≈ (f ∣ h) ∙ (g ∣ k)
∣-abides-∙-compat-inv f h g k f∥h g∥k fg hk a with g a | inspect g a | k a | inspect k a | g∥k a | viewCompat g k g∥k a
∣-abides-∙-compat-inv f h g k f∥h g∥k fg hk a | just b | _ | just .b | _ | g≡k | Both .b = refl
∣-abides-∙-compat-inv f h g k f∥h g∥k fg hk a | just b | _ | nothing | _ | g≡k | p with f b | h b | inspect h b | f∥h b | viewCompat f h f∥h b
∣-abides-∙-compat-inv f h g k f∥h g∥k fg hk a | just b | _ | nothing | _ | g≡k | p | just x | hb | _ | f≡h | q = refl
∣-abides-∙-compat-inv f h g k f∥h g∥k fg hk a | just b | [ g≡ ] | nothing | _ | g≡k | p | nothing | just x | [ h≡ ] | f≡h | q with fg a
... | fga rewrite g≡ | fga with f≡h
∣-abides-∙-compat-inv f h g k f∥h g∥k fg hk a | just b | [ g≡ ] | nothing | _ | g≡k | p | nothing | just x | [ h≡ ] | f≡h | q | fga | ()
∣-abides-∙-compat-inv f h g k f∥h g∥k fg hk a | just b | _ | nothing | _ | g≡k | p | nothing | nothing | [ h≡ ] | f≡h | q = refl
∣-abides-∙-compat-inv f h g k f∥h g∥k fg hk a | nothing | _ | just b | _ | g≡k | p with f b | h b | inspect h b | f∥h b | viewCompat f h f∥h b
∣-abides-∙-compat-inv f h g k f∥h g∥k fg hk a | nothing | _ | just b | _ | g≡k | p | just x₁ | just .x₁ | [ h≡ ] | f≡h | Both .x₁ = refl
∣-abides-∙-compat-inv f h g k f∥h g∥k fg hk a | nothing | _ | just b | [ k≡ ] | g≡k | p | just x | nothing | [ h≡ ] | f≡h | q with hk a
... | hka rewrite k≡ | hka with f≡h
∣-abides-∙-compat-inv f h g k f∥h g∥k fg hk a | nothing | w | just b | [ k≡ ] | g≡k | p | just x | nothing | [ h≡ ] | f≡h | q | hka | ()
∣-abides-∙-compat-inv f h g k f∥h g∥k fg hk a | nothing | _ | just b | _ | g≡k | p | nothing | hb | _ | f≡h | q = refl
∣-abides-∙-compat-inv f h g k f∥h g∥k fg hk a | nothing | _ | nothing | _ | g≡k | p = refl
