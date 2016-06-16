-- Theory of partial bijections

module PartialBijections where

open import Level renaming (zero to lzero)

open import Function using (const) renaming (_∘_ to _∘ᶠ_)
open import Data.Unit
open import Data.Sum as Sum
open import Data.Product as Prod
open import Data.Maybe as Maybe

open import Relation.Binary
open import Relation.Binary.Core using (module IsEquivalence)
import Relation.Binary.Core as PropEq
import Relation.Binary.PreorderReasoning as Pre
  renaming (_∼⟨_⟩_ to _⊑⟨_⟩_ )

open import PartialFunctions hiding (∅ ; id ; inl ; inr ; isEquivalence)
                             renaming (_+_ to _⇀+_)
import PartialFunctions as PFun

----------------------------------------------------------------------
-- Partial bijections
----------------------------------------------------------------------

-- A partial bijection is a pair of partial functions f and g between
-- sets A and B such that both f∘g and g∘f are bounded above by the
-- identity function.  That is, f∘g can be undefined on some values
-- but it must be the identity for those values on which it is
-- defined.
record _⇌_ (A B : Set) : Set where
  constructor PBij
  field
    fwd      : A ⇀ B
    bwd      : B ⇀ A
    .left-id  : bwd • fwd ⊑ PFun.id
    .right-id : fwd • bwd ⊑ PFun.id

infix 1 _⇌_

open _⇌_

----------------------------------------------------------------------
-- Equivalence of partial bijections
----------------------------------------------------------------------

_≋_ : {A B : Set} → Rel (A ⇌ B) lzero
f ≋ g = (fwd f ≈ fwd g) × (bwd f ≈ bwd g)

infix 0 _≋_

isEquivalence : ∀ {A B : Set} → IsEquivalence (_≋_ {A} {B})
isEquivalence = record
  { refl  = ≈-refl , ≈-refl
  ; sym   = Prod.map ≈-sym ≈-sym
  ; trans = Prod.zip ≈-trans ≈-trans
  }

----------------------------------------------------------------------
-- Special partial bijections
----------------------------------------------------------------------

-- The totally undefined partial bijection.
∅ : {A B : Set} → A ⇌ B
∅ = record
  { fwd      = PFun.∅
  ; bwd      = PFun.∅
  ; left-id  = const tt
  ; right-id = const tt
  }

----------------------------------------------------------------------
-- The category of partial bijections
----------------------------------------------------------------------

-- The identity partial bijection.
id : {A : Set} → A ⇌ A
id = record
  { fwd      = PFun.id
  ; bwd      = PFun.id
  ; left-id  = λ _ → PropEq.refl
  ; right-id = λ _ → PropEq.refl
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

    .∘-id : {A B C : Set} → (h : A ⇌ B) → (k : B ⇌ C)
         → (bwd h • bwd k) • (fwd k • fwd h) ⊑ PFun.id
    ∘-id {A} h k = begin
      ((h.bwd • k.bwd) • (k.fwd • h.fwd))
                                              ≈⟨ sym (•-assoc (h.bwd • k.bwd) k.fwd h.fwd ) ⟩
      ((h.bwd • k.bwd) • k.fwd) • h.fwd
                                              ≈⟨ ≈-cong-left h.fwd
                                                  (•-assoc h.bwd k.bwd k.fwd) ⟩
      (h.bwd • (k.bwd • k.fwd)) • h.fwd
                                              ⊑⟨ ⊑-mono-left _ _ h.fwd
                                                ( ⊑-mono-right _ _ h.bwd
                                                    k.left-id
                                                )
                                              ⟩
      (h.bwd • PFun.id) • h.fwd
                                              ≈⟨ ≈-cong-left h.fwd •-right-id ⟩
      h.bwd • h.fwd
                                              ⊑⟨ h.left-id ⟩
      PFun.id ∎

      where
        open module h = _⇌_ h
        open module k = _⇌_ k
        open Pre (⊑-Preorder A A)
        open module PFEquiv = IsEquivalence (PFun.isEquivalence {A = A} {B = A})

∘-assoc : {A B C D : Set} → (f : C ⇌ D) (g : B ⇌ C) (h : A ⇌ B)
  → (f ∘ g) ∘ h ≋ f ∘ (g ∘ h)
∘-assoc {A = A} {D = D} f g h =
  •-assoc (fwd f) (fwd g) (fwd h) , sym (•-assoc (bwd h) (bwd g) (bwd f))
  where
    open module PFEquiv = IsEquivalence (PFun.isEquivalence {A = D} {B = A})

∘-left-id : {A B : Set} {f : A ⇌ B} → id ∘ f ≋ f
∘-left-id = •-left-id , (λ _ → PropEq.refl)

∘-right-id : {A B : Set} {f : A ⇌ B} → f ∘ id ≋ f
∘-right-id = (λ _ → PropEq.refl) , •-left-id

∘⁻¹ : {A B C : Set} {f : B ⇌ C} {g : A ⇌ B} → (f ∘ g) ⁻¹ ≋ (g ⁻¹ ∘ f ⁻¹)
∘⁻¹ = (λ _ → PropEq.refl) , (λ _ → PropEq.refl)

----------------------------------------------------------------------
-- Sums
----------------------------------------------------------------------

inl : {A B : Set} → (A ⇌ A ⊎ B)
inl = record
  { fwd      = λ a → just (inj₁ a)
  ; bwd      = [ just , const nothing ]
  ; left-id  = λ _ → PropEq.refl
  ; right-id = [ (λ _ → PropEq.refl) , const tt ]
  }

inr : {A B : Set} → (B ⇌ A ⊎ B)
inr = record
  { fwd      = λ b → just (inj₂ b)
  ; bwd      = [ const nothing , just ]
  ; left-id  = λ _ → PropEq.refl
  ; right-id = [ const tt , (λ _ → PropEq.refl) ]
  }

_+_ : {A₀ B₀ A₁ B₁ : Set} → (A₀ ⇌ B₀) → (A₁ ⇌ B₁) → (A₀ ⊎ A₁ ⇌ B₀ ⊎ B₁)
f + g = record
  { fwd      = fwd f ⇀+ fwd g
  ; bwd      = bwd f ⇀+ bwd g
  ; left-id  = +-left-id f g
  ; right-id = +-left-id (f ⁻¹) (g ⁻¹)
  }
  where
    .+-left-id : {A₀ B₀ A₁ B₁ : Set} → (f : A₀ ⇌ B₀) → (g : A₁ ⇌ B₁)
      → (bwd f ⇀+ bwd g) • (fwd f ⇀+ fwd g) ⊑ PFun.id
    +-left-id f g (inj₁ a₀) with fwd f a₀ | left-id f a₀
    +-left-id f g (inj₁ a₀) | nothing | _ = tt
    +-left-id f g (inj₁ a₀) | just b₀ | _ with bwd f b₀
    +-left-id f g (inj₁ a₀) | just b₀ | _ | nothing = tt
    +-left-id f g (inj₁ a₀) | just b₀ | a₀'≡a₀ | just a₀' rewrite a₀'≡a₀ = PropEq.refl
    +-left-id f g (inj₂ a₁) with fwd g a₁ | left-id g a₁
    +-left-id f g (inj₂ a₁) | nothing | _ = tt
    +-left-id f g (inj₂ a₁) | just b₁ | q with bwd g b₁
    +-left-id f g (inj₂ a₁) | just b₁ | _ | nothing = tt
    +-left-id f g (inj₂ a₁) | just b₁ | a₁'≡a₁ | just a₁' rewrite a₁'≡a₁ = PropEq.refl

∘-abides-+ :
  {A₀ B₀ C₀ A₁ B₁ C₁ : Set}
  {f : B₀ ⇌ C₀} {g : A₀ ⇌ B₀} {h : B₁ ⇌ C₁} {k : A₁ ⇌ B₁}
  → (f ∘ g) + (h ∘ k) ≋ (f + h) ∘ (g + k)
∘-abides-+ = •-abides-+ , •-abides-+

+⁻¹ :
  {A₀ B₀ A₁ B₁ : Set} {f : A₀ ⇌ B₀} {g : A₁ ⇌ B₁} →
  (f + g) ⁻¹ ≋ f ⁻¹ + g ⁻¹
+⁻¹ = (λ _ → PropEq.refl) , (λ _ → PropEq.refl)

----------------------------------------------------------------------
-- Merge
----------------------------------------------------------------------

_⋎_ : {A B : Set} (f g : A ⇌ B) → (A ⇌ B)
f ⋎ g = record
  { fwd = merge f g
  ; bwd = merge (g ⁻¹) (f ⁻¹)
  ; left-id  = foo
  ; right-id = {!!}
  }
  where
    merge : {A B : Set} (f g : A ⇌ B) → (A ⇀ B)
    merge f _ a with fwd f a
    merge _ _ _ | just b = just b
    merge _ g a | nothing with fwd g a
    merge _ _ _ | nothing | nothing = nothing
    merge f _ _ | nothing | just ga with bwd f ga
    merge _ _ _ | nothing | just ga | just _ = nothing
    merge _ _ _ | nothing | just ga | nothing = just ga

    foo : merge (g ⁻¹) (f ⁻¹) • merge f g ⊑ PFun.id
    foo a with fwd f a
    foo a | just b with bwd g b
    foo a | just b | just x = {!!}
    foo a | just b | nothing = {!!}
    foo a | nothing = {!!}
