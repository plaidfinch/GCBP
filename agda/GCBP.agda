open import Data.Maybe
open import Data.Sum
open import Data.List

infix 0 _↔_
record _↔_ (A B : Set) : Set where
  constructor _:↔:_
  field
    fwd : A → B
    bwd : B → A

infix 0 _⇌_
record _⇌_ (A B : Set) : Set where
  constructor _:⇌:_
  field
    fwd : (A → Maybe B)
    bwd : (B → Maybe A)

partial : {A B : Set} → (A ↔ B) → (A ⇌ B)
partial (fwd :↔: bwd) = (λ z → just (fwd z)) :⇌: (λ z → just (bwd z))

-- fromJust : {A : Set} → Maybe A → A
-- fromJust (just x) = x

unsafeTotal : {A B : Set} → (A ⇌ B) → (A ↔ B)
unsafeTotal = {!!}
-- unsafeTotal (fwd :⇌: bwd) = λ x → fromJust (fwd x) :↔: λ x → fromJust (bwd x)

infixr 9 _∙_
_∙_ : {A B C : Set} → (B → Maybe C) → (A → Maybe B) → (A → Maybe C)
(f ∙ g) a with g a
(f ∙ g) a | just b  = f b
(f ∙ g) a | nothing = nothing

infixr 9 _∘_
_∘_ : {A B C : Set} → (B ⇌ C) → (A ⇌ B) → (A ⇌ C)
(fwd₁ :⇌: bwd₁) ∘ (fwd₂ :⇌: bwd₂) = (fwd₁ ∙ fwd₂) :⇌: (bwd₂ ∙ bwd₁)


∅ : {A B : Set} → (A ⇌ B)
∅ = (λ _ → nothing) :⇌: (λ _ → nothing)

_⁻¹ : {A B : Set} → (A ⇌ B) → (B ⇌ A)
(fwd :⇌: bwd) ⁻¹ = bwd :⇌: fwd

_∥M_ : {A B C D : Set} → (A → Maybe B) → (C → Maybe D) → ((A ⊎ C) → Maybe (B ⊎ D))
(f ∥M g) (inj₁ a) with (f a)
(f ∥M g) (inj₁ a) | just b  = just (inj₁ b)
(f ∥M g) (inj₁ a) | nothing = nothing
(f ∥M g) (inj₂ c) with (g c)
(f ∥M g) (inj₂ c) | just d  = just (inj₂ d)
(f ∥M g) (inj₂ c) | nothing = nothing

_∥_ : {A B C D : Set} → (A ⇌ B) → (C ⇌ D) → ((A ⊎ C) ⇌ (B ⊎ D))
(fwd₁ :⇌: bwd₁) ∥ (fwd₂ :⇌: bwd₂) = (fwd₁ ∥M fwd₂) :⇌: (bwd₁ ∥M bwd₂)

ext : {A B A' B' : Set} → (g : B ⇌ B') → (h : (A ⊎ B) ⇌ (A' ⊎ B')) → ((A ⊎ B) ⇌ (A' ⊎ B')) → ((A ⊎ B) ⇌ (A' ⊎ B'))
ext g h k = h ∘ (∅ ∥ (g ⁻¹)) ∘ k

gcbp : {A B C D : Set} → (A ⊎ C ↔ B ⊎ D) → (C ↔ D) → (A ↔ B)
gcbp h g = {!? (iterate (ext g' h') h')!}
  where
    h' = partial h
    g' = partial g
