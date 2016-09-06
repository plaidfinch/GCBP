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
open import Relation.Binary.PropositionalEquality using (inspect)
  renaming ([_] to ins_)

open import PartialFunctions hiding (∅ ; id ; inl ; inr ; isEquivalence
                                    ; dom ; _∥_ ; ∥-refl ; ∥-sym)
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
    fwd        : A ⇀ B
    bwd        : B ⇀ A
    .left-dom   : bwd ∙ fwd ≈ PFun.dom fwd
    .right-dom  : fwd ∙ bwd ≈ PFun.dom bwd

infix 1 _⇌_

open _⇌_


-- The properties left-dom and right-dom imply both the properties we
-- had before.  So if those properties were strong enough to properly
-- characterize partial bijections, then this property must be as
-- well.

-- First, bwd ∙ fwd is a partial identity, that is, the forward and
-- backwards directions match wherever they are defined.
.⇌-left-id : {A B : Set} → (f : A ⇌ B) → bwd f ∙ fwd f ⊑ PFun.id
⇌-left-id {A} f = begin
  f.bwd ∙ f.fwd
                                          ≈⟨ f.left-dom ⟩
  PFun.dom f.fwd
                                          ⊑⟨ dom⊑id ⟩
  PFun.id ∎
  where
    open module f = _⇌_ f
    open Pre (⊑-Preorder A A)
    open module PFEquiv = IsEquivalence (PFun.isEquivalence {A = A} {B = A})

-- Second, the backward direction is no less defined than the forward
-- direction.
.⇌-left-def : {A B : Set} → (f : A ⇌ B)
            → PFun.dom (fwd f) ≈ PFun.dom (bwd f ∙ fwd f)
⇌-left-def {A} f = begin
  PFun.dom f.fwd
                                          ≈⟨ ≈-sym domdom ⟩
  PFun.dom (PFun.dom f.fwd)
                                          ≈⟨ dom-resp-≈ (≈-sym f.left-dom) ⟩
  PFun.dom (f.bwd ∙ f.fwd) ∎
  where
    open module f = _⇌_ f
    open import Relation.Binary.EqReasoning (PFun.setoid A A)

-- The symmetric properties can be obtained by inverting.

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
  { fwd       = PFun.∅
  ; bwd       = PFun.∅
  ; left-dom  = const PropEq.refl
  ; right-dom = const PropEq.refl
  }

dom : {A B : Set} → (A ⇌ B) → (A ⇌ A)
dom {A} f = record
  { fwd       = PFun.dom (fwd f)
  ; bwd       = PFun.dom (fwd f)
  ; left-dom  = dom∙dom
  ; right-dom = dom∙dom
  }
  where
    dom∙dom : {A B : Set} {f : A ⇀ B} → PFun.dom f ∙ PFun.dom f ≈ PFun.dom (PFun.dom f)
    dom∙dom {A = A} {f = f} = begin
      PFun.dom f ∙ PFun.dom f
                                        ≈⟨ subset-idem dom⊑id ⟩
      PFun.dom f
                                        ≈⟨ ≈-sym domdom ⟩
      PFun.dom (PFun.dom f) ∎
      where
        open import Relation.Binary.EqReasoning (PFun.setoid A A)

----------------------------------------------------------------------
-- The category of partial bijections
----------------------------------------------------------------------

-- The identity partial bijection.
id : {A : Set} → A ⇌ A
id = record
  { fwd       = PFun.id
  ; bwd       = PFun.id
  ; left-dom  = λ _ → PropEq.refl
  ; right-dom = λ _ → PropEq.refl
  }

-- Inverting a partial bijection.
_⁻¹ : {A B : Set} → (A ⇌ B) → (B ⇌ A)
f ⁻¹ = record
  { fwd       = f.bwd
  ; bwd       = f.fwd
  ; left-dom  = f.right-dom
  ; right-dom = f.left-dom
  }
  where
    module f = _⇌_ f

rng : {A B : Set} → (A ⇌ B) → (B ⇌ B)
rng f = dom (f ⁻¹)

-- Composing partial bijections.
_∘_ : {A B C : Set} → (B ⇌ C) → (A ⇌ B) → (A ⇌ C)
_∘_ {A} g f = record
  { fwd       = g.fwd ∙ f.fwd
  ; bwd       = f.bwd ∙ g.bwd
  ; left-dom  = ∘-left-dom f g
  ; right-dom = ∘-left-dom (g ⁻¹) (f ⁻¹)
  }
  where
    module f = _⇌_ f
    module g = _⇌_ g

    lemma : {A B C : Set} {f⁻¹ : B ⇀ A} {f : A ⇀ B} {g : B ⇀ C}
          → f⁻¹ ∙ f ≈ PFun.dom f → f⁻¹ ∙ PFun.dom g ∙ f ≈ PFun.dom (g ∙ f)
    lemma {f = f} eq a with f a | inspect f a | eq a
    lemma         _  _ | nothing | _       | _ = PropEq.refl
    lemma {g = g} _  _ | just b  | ins _   | _ with g b
    lemma         _  _ | just _  | ins _   | _   | nothing = PropEq.refl
    lemma         _  _ | just _  | ins _   | eq₂ | just _  = eq₂
    -- The above looks simple enough but it took me a REALLY long time
    -- to figure out the right order to pattern-match and 'inspect'
    -- things to make it all go through.  Proof assistants really need
    -- a better story for this kind of thing.  Grumble grumble.

    .∘-left-dom : {A B C : Set} (h : A ⇌ B) (k : B ⇌ C)
               → (bwd h ∙ bwd k) ∙ fwd k ∙ fwd h ≈ PFun.dom (fwd k ∙ fwd h)
    ∘-left-dom {A} h k = begin
      (h.bwd ∙ k.bwd) ∙ k.fwd ∙ h.fwd
                                         ≈⟨ sym (∙-assoc _ _ h.fwd ) ⟩
      ((h.bwd ∙ k.bwd) ∙ k.fwd) ∙ h.fwd
                                         ≈⟨ ≈-cong-left h.fwd
                                               (∙-assoc _ _ k.fwd) ⟩
      (h.bwd ∙ (k.bwd ∙ k.fwd)) ∙ h.fwd
                                         ≈⟨ ≈-cong-left h.fwd
                                           ( ≈-cong-right h.bwd
                                               k.left-dom
                                           )
                                         ⟩
      (h.bwd ∙ PFun.dom k.fwd) ∙ h.fwd
                                        ≈⟨ ∙-assoc _ _ h.fwd ⟩
      h.bwd ∙ PFun.dom k.fwd ∙ h.fwd
                                        ≈⟨ lemma h.left-dom ⟩
      PFun.dom (k.fwd ∙ h.fwd) ∎
      where
        module h = _⇌_ h
        module k = _⇌_ k

        open import Relation.Binary.EqReasoning (PFun.setoid A A)
        open module PFEquiv = IsEquivalence (PFun.isEquivalence {A = A} {B = A})

∘-assoc : {A B C D : Set} → (f : C ⇌ D) (g : B ⇌ C) (h : A ⇌ B)
  → (f ∘ g) ∘ h ≋ f ∘ (g ∘ h)
∘-assoc {A = A} {D = D} f g h =
  ∙-assoc (fwd f) (fwd g) (fwd h) , sym (∙-assoc (bwd h) (bwd g) (bwd f))
  where
    open module PFEquiv = IsEquivalence (PFun.isEquivalence {A = D} {B = A})

∘-left-id : {A B : Set} {f : A ⇌ B} → id ∘ f ≋ f
∘-left-id = ∙-left-id , (λ _ → PropEq.refl)

∘-right-id : {A B : Set} {f : A ⇌ B} → f ∘ id ≋ f
∘-right-id = (λ _ → PropEq.refl) , ∙-left-id

∘⁻¹ : {A B C : Set} {f : B ⇌ C} {g : A ⇌ B} → (f ∘ g) ⁻¹ ≋ (g ⁻¹ ∘ f ⁻¹)
∘⁻¹ = (λ _ → PropEq.refl) , (λ _ → PropEq.refl)

----------------------------------------------------------------------
-- Sums
----------------------------------------------------------------------

inl : {A B : Set} → (A ⇌ A ⊎ B)
inl = record
  { fwd       = λ a → just (inj₁ a)
  ; bwd       = [ just , (const nothing) ]
  ; left-dom  = λ _ → PropEq.refl
  ; right-dom = [ (λ _ → PropEq.refl) , (λ _ → PropEq.refl) ]
  }

inr : {A B : Set} → (B ⇌ A ⊎ B)
inr = record
  { fwd       = λ b → just (inj₂ b)
  ; bwd       = [ const nothing , just ]
  ; left-dom  = λ _ → PropEq.refl
  ; right-dom = [ (λ _ → PropEq.refl) , (λ _ → PropEq.refl) ]
  }

_+_ : {A₀ B₀ A₁ B₁ : Set} → (A₀ ⇌ B₀) → (A₁ ⇌ B₁) → (A₀ ⊎ A₁ ⇌ B₀ ⊎ B₁)
_+_ {A₀} {B₀} {A₁} {B₁} f g = record
  { fwd       = f.fwd ⇀+ g.fwd
  ; bwd       = f.bwd ⇀+ g.bwd
  ; left-dom  = +-left-dom f g
  ; right-dom = +-left-dom (f ⁻¹) (g ⁻¹)
  }
  where
    module f = _⇌_ f
    module g = _⇌_ g

    .+-left-dom : {C₀ C₁ D₀ D₁ : Set} → (h : C₀ ⇌ D₀) → (k : C₁ ⇌ D₁)
               → (bwd h ⇀+ bwd k) ∙ (fwd h ⇀+ fwd k) ≈ PFun.dom (fwd h ⇀+ fwd k)
    +-left-dom {C₀} {C₁} h k = begin
      (h.bwd ⇀+ k.bwd) ∙ (h.fwd ⇀+ k.fwd)
                                        ≈⟨ ≈-sym ∙-abides-+ ⟩
      (h.bwd ∙ h.fwd) ⇀+ (k.bwd ∙ k.fwd)
                                        ≈⟨ +-resp-≈ h.left-dom k.left-dom ⟩
      PFun.dom h.fwd ⇀+ PFun.dom k.fwd
                                        ≈⟨ ≈-sym dom-+ ⟩
      PFun.dom (h.fwd ⇀+ k.fwd) ∎
      where
        module h = _⇌_ h
        module k = _⇌_ k
        open import Relation.Binary.EqReasoning (PFun.setoid (C₀ ⊎ C₁) (C₀ ⊎ C₁))

∘-abides-+ :
  {A₀ B₀ C₀ A₁ B₁ C₁ : Set}
  {f : B₀ ⇌ C₀} {g : A₀ ⇌ B₀} {h : B₁ ⇌ C₁} {k : A₁ ⇌ B₁}
  → (f ∘ g) + (h ∘ k) ≋ (f + h) ∘ (g + k)
∘-abides-+ = ∙-abides-+ , ∙-abides-+

+⁻¹ :
  {A₀ B₀ A₁ B₁ : Set} {f : A₀ ⇌ B₀} {g : A₁ ⇌ B₁} →
  (f + g) ⁻¹ ≋ f ⁻¹ + g ⁻¹
+⁻¹ = (λ _ → PropEq.refl) , (λ _ → PropEq.refl)

----------------------------------------------------------------------
-- Compatibility
----------------------------------------------------------------------

-- Compatibility of partial bijections.
_∥_ : {A B : Set} → Rel (A ⇌ B) lzero
f ∥ g = (fwd f PFun.∥ fwd g) × (bwd f PFun.∥ bwd g)

∥-refl : {A B : Set} {f : A ⇌ B} → f ∥ f
∥-refl {f = f} = PFun.∥-refl {f = fwd f}, PFun.∥-refl {f = bwd f}

∥-sym : {A B : Set} {f g : A ⇌ B} → f ∥ g → g ∥ f
∥-sym {f = f} {g = g} (x , y) = (PFun.∥-sym {f = fwd f} {g = fwd g} x)
                              , (PFun.∥-sym {f = bwd f} {g = bwd g} y)

----------------------------------------------------------------------
-- Merge
----------------------------------------------------------------------

-- Try defining an alternate version of merge which requires a proof
-- that f and g are compatible, i.e. agree where they are both defined?
-- i.e. (f . dom g ≈ g . dom f) and (rng g . f ≈ rng f . g)
-- Then we can just join both directions.

_⋎_ : {A B : Set} (f g : A ⇌ B) → {{compat : f ∥ g}} → (A ⇌ B)
_⋎_ {A} f g {{cr , cl}} = record
  { fwd       = f.fwd ∣ g.fwd
  ; bwd       = f.bwd ∣ g.bwd
  ; left-dom  = {!!}

  -- The following proof doesn't work since ∣-abides-∙-compat is false
  -- (see counterexample in PartialFunctions.agda)

  -- ; left-dom  = begin
  --     f.bwd ∣ g.bwd ∙ f.fwd ∣ g.fwd
  --                                       ≈⟨ ≈-sym
  --                                           (∣-abides-∙-compat
  --                                             {f = f.bwd} {h = g.bwd} {g = f.fwd} {k = g.fwd}
  --                                             cl cr
  --                                           )
  --                                        ⟩
  --     (f.bwd ∙ f.fwd) ∣ (g.bwd ∙ g.fwd)
  --                                       ≈⟨ ∣-resp-≈ f.left-dom g.left-dom ⟩
  --     PFun.dom f.fwd ∣ PFun.dom g.fwd
  --                                       ≈⟨ ≈-sym (dom-∣ {f = f.fwd}) ⟩
  --     PFun.dom (f.fwd ∣ g.fwd) ∎
  ; right-dom = {!!}
  }
  where
    module f = _⇌_ f
    module g = _⇌_ g
    open import Relation.Binary.EqReasoning (PFun.setoid A A)

