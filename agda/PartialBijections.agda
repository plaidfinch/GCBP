-- Theory of partial bijections

module PartialBijections where

open import Function using (const) renaming (_∘_ to _∘f_)

-- open import Data.Empty
open import Data.Unit
-- open import Data.Sum

open import Data.Maybe
-- open import Category.Monad

-- open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
import Relation.Binary.PreorderReasoning as Pre
  renaming (_∼⟨_⟩_ to _⊑⟨_⟩_ ; _≈⟨_⟩_ to _≡⟨_⟩_ ; _≈⟨⟩_ to _≡⟨⟩_ )

open import PartialFunctions hiding (∅)
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
  field
    fwd      : A ⇀ B
    bwd      : B ⇀ A
    left-id  : bwd • fwd ⊑ id
    right-id : fwd • bwd ⊑ id

-- The totally undefined partial bijection.
∅ : {A B : Set} → A ⇌ B
∅ = record
  { fwd      = PFun.∅
  ; bwd      = PFun.∅
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
