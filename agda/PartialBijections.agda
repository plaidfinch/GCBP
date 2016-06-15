-- Theory of partial bijections

module PartialBijections where

open import Function using (const) renaming (_∘_ to _∘f_)
open import Data.Unit
open import Data.Sum
open import Data.Maybe as Maybe

open import Relation.Binary.PropositionalEquality
import Relation.Binary.PreorderReasoning as Pre
  renaming (_∼⟨_⟩_ to _⊑⟨_⟩_ ; _≈⟨_⟩_ to _≡⟨_⟩_ ; _≈⟨⟩_ to _≡⟨⟩_ )

open import PartialFunctions hiding (∅ ; id)
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

-- The totally undefined partial bijection.
∅ : {A B : Set} → A ⇌ B
∅ = record
  { fwd      = PFun.∅
  ; bwd      = PFun.∅
  ; left-id  = const tt
  ; right-id = const tt
  }

-- The identity partial bijection.
id : {A : Set} → A ⇌ A
id = record
  { fwd      = PFun.id
  ; bwd      = PFun.id
  ; left-id  = λ _ → refl
  ; right-id = λ _ → refl
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
         → (_⇌_.bwd h • _⇌_.bwd k) • (_⇌_.fwd k • _⇌_.fwd h) ⊑ PFun.id
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
      (h.bwd • PFun.id) • h.fwd
                                              ≡⟨ cong (λ h → h • h.fwd) (•-right-id _) ⟩
      h.bwd • h.fwd
                                              ⊑⟨ h.left-id ⟩
      PFun.id ∎

      where
        open module h = _⇌_ h
        open module k = _⇌_ k
        open Pre (⊑-Preorder A A)

-- To prove two partial bijections equal, it suffices to respectively
-- prove their forward and backward directions equal
⇌-≡ : {A B : Set} {f g : A ⇌ B} → fwd f ≡ fwd g → bwd f ≡ bwd g → f ≡ g
⇌-≡ {f = PBij fwdf bwdf _ _} {g = PBij fwdg bwdg _ _} fwd≡ bwd≡ rewrite fwd≡ | bwd≡ = refl

-- Partial bijections form a category.
∘-assoc : {A B C D : Set} → (f : C ⇌ D) (g : B ⇌ C) (h : A ⇌ B)
  → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
∘-assoc f g h =
  ⇌-≡ (     •-assoc (fwd f) (fwd g) (fwd h) )
      (sym (•-assoc (bwd h) (bwd g) (bwd f)))

∘-left-id : {A B : Set} (f : A ⇌ B) → id ∘ f ≡ f
∘-left-id f = ⇌-≡ (•-left-id (fwd f)) refl

∘-right-id : {A B : Set} (f : A ⇌ B) → f ∘ id ≡ f
∘-right-id f = ⇌-≡ refl (•-left-id (bwd f))

----------------------------------------------------------------------
-- Sums
----------------------------------------------------------------------

inl : {A B : Set} → (A ⇌ A ⊎ B)
inl = record
  { fwd      = λ a → just (inj₁ a)
  ; bwd      = [ just , const nothing ]
  ; left-id  = λ _ → refl
  ; right-id = [ (λ _ → refl) , const tt ]
  }

inr : {A B : Set} → (B ⇌ A ⊎ B)
inr = record
  { fwd      = λ b → just (inj₂ b)
  ; bwd      = [ const nothing , just ]
  ; left-id  = λ _ → refl
  ; right-id = [ const tt , (λ _ → refl) ]
  }

_+_ : {A₀ B₀ A₁ B₁ : Set} → (A₀ ⇌ B₀) → (A₁ ⇌ B₁) → (A₀ ⊎ A₁ ⇌ B₀ ⊎ B₁)
f + g = record
  { fwd      = [ (λ a₀ → Maybe.map inj₁ (fwd f a₀)) , (λ a₁ → Maybe.map inj₂ (fwd g a₁)) ]
  ; bwd      = [ (λ b₀ → Maybe.map inj₁ (bwd f b₀)) , (λ b₁ → Maybe.map inj₂ (bwd g b₁)) ]
  ; left-id  = {!!}
  ; right-id = {!!}
  }

