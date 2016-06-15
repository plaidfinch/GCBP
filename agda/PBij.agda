-- Theory of partial bijections

module PBij where

open import Level renaming (zero to lzero)

open import Function using (const) renaming (_∘_ to _∘f_)

open import Data.Empty
open import Data.Unit
open import Data.Sum

open import Data.Maybe
open import Category.Monad

open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
import Relation.Binary.PreorderReasoning as Pre
  renaming (_∼⟨_⟩_ to _⊑⟨_⟩_ ; _≈⟨_⟩_ to _≡⟨_⟩_ ; _≈⟨⟩_ to _≡⟨⟩_ )

----------------------------------------------------------------------

-- Assume function extensionality, just to get nicer proofs.  We won't
-- need the computational content of the proofs.
postulate
  funext : (a b : Level) → Extensionality a b

----------------------------------------------------------------------
-- Partial functions
----------------------------------------------------------------------

_⇀_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
A ⇀ B = A → Maybe B

-- Identity and composition for partial functions.
id : ∀ {ℓ} {A : Set ℓ} → (A ⇀ A)
id = just

_•_ : ∀ {ℓ} {A B C : Set ℓ} → (B ⇀ C) → (A ⇀ B) → (A ⇀ C)
_•_ = _<=<_
  where
    open RawMonad Data.Maybe.monad

infixr 9 _•_

-- Partial functions form a category.

•-assoc-pt : ∀ {ℓ} {A B C D : Set ℓ} (f : C ⇀ D) (g : B ⇀ C) (h : A ⇀ B) (a : A)
        → ((f • g) • h) a ≡ (f • (g • h)) a
•-assoc-pt f g h a with h a
... | nothing = refl
... | just b  with g b
... | nothing = refl
... | just c  = refl

•-assoc : ∀ {ℓ} {A B C D : Set ℓ} (f : C ⇀ D) (g : B ⇀ C) (h : A ⇀ B)
        → (f • g) • h ≡ f • (g • h)
•-assoc {ℓ} f g h = funext ℓ ℓ (•-assoc-pt f g h)

•-left-id : ∀ {ℓ} {A B : Set ℓ} (f : A ⇀ B) → id • f ≡ f
•-left-id {ℓ} {A} f = funext ℓ ℓ •-left-id-pt
  where
    •-left-id-pt : ∀ a → (id • f) a ≡ f a
    •-left-id-pt a with f a
    ... | nothing = refl
    ... | just _  = refl

•-right-id : ∀ {ℓ} {A B : Set ℓ} (f : A ⇀ B) → f • id ≡ f
•-right-id {ℓ} f = funext ℓ ℓ (λ _ → refl)

----------------------------------------------------------------------
-- Definedness partial order for partial functions
----------------------------------------------------------------------

-- Definedness partial order for Maybe

_⊑M_ : {B : Set} → Rel (Maybe B) lzero
just a ⊑M just b  = a ≡ b
just x ⊑M nothing = ⊥
nothing ⊑M b      = ⊤

infix 4 _⊑M_

⊑M-refl : {B : Set} (b : Maybe B) → b ⊑M b
⊑M-refl nothing  = tt
⊑M-refl (just _) = refl

⊑M-trans : {A : Set} (x y z : Maybe A) → x ⊑M y → y ⊑M z → x ⊑M z
⊑M-trans (just x) (just y) z x⊑y y⊑z rewrite x⊑y = y⊑z
⊑M-trans (just x) nothing z () y⊑z
⊑M-trans nothing y z x⊑y y⊑z = tt

-- Order for partial functions is just pointwise lifting of order on Maybe

_⊑_ : {A B : Set} → Rel (A ⇀ B) lzero
f ⊑ g = ∀ a → f a ⊑M g a

infix 4 _⊑_

-- ⊑ is reflexive & transitive

⊑-refl : {A B : Set} (f : A ⇀ B) → f ⊑ f
⊑-refl f = λ a → ⊑M-refl (f a)

⊑-trans : {A B : Set} (f g h : A ⇀ B) → f ⊑ g → g ⊑ h → f ⊑ h
⊑-trans f g h f⊑g g⊑h = λ a → ⊑M-trans (f a) (g a) (h a) (f⊑g a) (g⊑h a)

⊑-Preorder : Set → Set → Preorder lzero lzero lzero
⊑-Preorder A B = record
  { Carrier = A ⇀ B
  ; _≈_ = _≡_
  ; _∼_ = _⊑_
  ; isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = ⊑-reflexive
    ; trans = λ {i} {j} {k} → ⊑-trans i j k
    }
  }
  where
    ⊑-reflexive : _≡_ ⇒ _⊑_
    ⊑-reflexive {_} {j} i≡j rewrite i≡j = ⊑-refl j

-- ...and also monotonic wrt. composition

⊑-mono-left : {A B C : Set} (f g : B ⇀ C) (h : A ⇀ B)
  → f ⊑ g → f • h ⊑ g • h
⊑-mono-left f g h f⊑g a with h a
... | just b  = f⊑g b
... | nothing = tt

⊑-mono-right : {A B C : Set} (f g : A ⇀ B) (h : B ⇀ C)
  → f ⊑ g → h • f ⊑ h • g
⊑-mono-right f g h f⊑g a with f a | g a | f⊑g a
... | just x  | just y  | x≡y rewrite x≡y = ⊑M-refl (h y)
... | just _  | nothing | ()
... | nothing | _       | _               = tt

----------------------------------------------------------------------
-- Partial bijections
----------------------------------------------------------------------

-- A partial bijection is a pair of partial functions f and g between
-- sets A and B such that both f∘g and g∘f are bounded above by the
-- identity function.  That is, f∘g can be undefined on some values
-- but it must be the identity for those values on which it is
-- defined.
record _⇌_ (A B : Set) : Set where
  field
    fwd      : A → Maybe B
    bwd      : B → Maybe A
    left-id  : bwd • fwd ⊑ id
    right-id : fwd • bwd ⊑ id

-- The totally undefined partial bijection.
∅ : {A B : Set} → A ⇌ B
∅ = record
  { fwd      = const nothing
  ; bwd      = const nothing
  ; left-id  = const tt
  ; right-id = const tt
  }

-- Inverting a partial bijection.
_⁻¹ : {A B : Set} → (A ⇌ B) → (B ⇌ A)
f ⁻¹ = record
  { fwd      = f.bwd
  ; bwd      = f.fwd
  ; left-id  = f.right-id
  ; right-id = f.left-id
  }
  where
    module f = _⇌_ f

-- Composing partial bijections.
_∘_ : {A B C : Set} → (B ⇌ C) → (A ⇌ B) → (A ⇌ C)
_∘_ {A} {B} {C} g f = record
  { fwd = g.fwd • f.fwd
  ; bwd = f.bwd • g.bwd
  ; left-id  = ∘-id f g
  ; right-id = ∘-id (g ⁻¹) (f ⁻¹)
  }
  where
    module f = _⇌_ f
    module g = _⇌_ g

    ∘-id : {A B C : Set} → (h : A ⇌ B) → (k : B ⇌ C)
         → (_⇌_.bwd h • _⇌_.bwd k) • (_⇌_.fwd k • _⇌_.fwd h) ⊑ id
    ∘-id {A} h k = begin
      ((h.bwd • k.bwd) • (k.fwd • h.fwd))
                                              ≡⟨ sym (•-assoc (h.bwd • k.bwd) k.fwd h.fwd ) ⟩
      ((h.bwd • k.bwd) • k.fwd) • h.fwd
                                              ≡⟨ cong (λ h → h • h.fwd)
                                                     (•-assoc h.bwd k.bwd k.fwd) ⟩
      (h.bwd • (k.bwd • k.fwd)) • h.fwd
                                              ⊑⟨ ⊑-mono-left _ _ h.fwd
                                                ( ⊑-mono-right _ _ h.bwd
                                                    k.left-id
                                                )
                                              ⟩
      (h.bwd • id) • h.fwd
                                              ≡⟨ cong (λ h → h • h.fwd) (•-right-id _) ⟩
      h.bwd • h.fwd
                                              ⊑⟨ h.left-id ⟩
      id ∎

      where
        open module h = _⇌_ h
        open module k = _⇌_ k
        open Pre (⊑-Preorder A A)
