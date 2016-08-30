_\\_ : {A B : Set} (f g : A ⇌ B) → (A ⇌ B)
_\\_ {A} {B} f g = record
  { fwd      = fwd (rng g) † ∙ fwd f ∙ fwd (dom g) †
  ; bwd      = bwd (dom g) † ∙ bwd f ∙ bwd (rng g) †
  ; left-id  = thereAndBack {X = bwd (dom g) †} {Y = bwd (rng g) †} {f = f ⁻¹}
                 (†⊑ dom⊑id) (†⊑ dom⊑id)
  ; right-id = thereAndBack {X = fwd (rng g) †} {Y = fwd (dom g) †} {f = f}
                 (†⊑ dom⊑id) (†⊑ dom⊑id)
  }
  where
    .thereAndBack : {C D : Set} {X : Subset D} {Y : Subset C} {f : C ⇌ D}
        → X ⊑ PFun.id → Y ⊑ PFun.id → (X ∙ fwd f ∙ Y) ∙ (Y ∙ bwd f ∙ X) ⊑ PFun.id
    thereAndBack {C} {D} {X} {Y} {f} X⊑id Y⊑id = begin
      (X ∙ fwd f ∙ Y) ∙ (Y ∙ bwd f ∙ X)
                                              ≈⟨⟩
      (X ∙ (fwd f ∙ Y)) ∙ (Y ∙ (bwd f ∙ X))
                                              ≈⟨ ≈-cong-left (Y ∙ bwd f ∙ X)
                                                  (EqC⇀D.sym (∙-assoc _ _ Y))
                                               ⟩
      ((X ∙ fwd f) ∙ Y) ∙ (Y ∙ (bwd f ∙ X))
                                              ≈⟨ ∙-assoc _ _ (Y ∙ (bwd f ∙ X)) ⟩
      (X ∙ fwd f) ∙ (Y ∙ (Y ∙ (bwd f ∙ X)))
                                              ≈⟨ ≈-cong-right (X ∙ fwd f)
                                                  (EqD⇀C.sym (∙-assoc _ _ (bwd f ∙ X)))
                                               ⟩
      (X ∙ fwd f) ∙ ((Y ∙ Y) ∙ (bwd f ∙ X))
                                              ≈⟨ ≈-cong-right (X ∙ fwd f)
                                                  (≈-cong-left (bwd f ∙ X)
                                                    (subset-idem Y⊑id))
                                               ⟩
      (X ∙ fwd f) ∙ (Y ∙ (bwd f ∙ X))
                                              ⊑⟨ ⊑-mono-right (X ∙ fwd f)
                                                  (⊑-mono-left (bwd f ∙ X) Y⊑id)
                                               ⟩
      (X ∙ fwd f) ∙ (PFun.id ∙ (bwd f ∙ X))
                                              ≈⟨ ≈-cong-right (X ∙ fwd f)
                                                  (∙-left-id {f = bwd f ∙ X})
                                               ⟩
      (X ∙ fwd f) ∙ (bwd f ∙ X)
                                              ≈⟨ ∙-assoc _ _ (bwd f ∙ X) ⟩
      X ∙ (fwd f ∙ (bwd f ∙ X))
                                              ≈⟨ ≈-cong-right X (EqD⇀D.sym (∙-assoc _ _ X)) ⟩
      X ∙ ((fwd f ∙ bwd f) ∙ X)
                                              ⊑⟨ ⊑-mono-right X (⊑-mono-left X
                                                  (right-id f)) ⟩
      X ∙ (PFun.id ∙ X)
                                              ≈⟨ ≈-cong-right X (∙-left-id {f = X}) ⟩
      X ∙ X
                                              ≈⟨ subset-idem X⊑id ⟩
      X
                                              ⊑⟨ X⊑id ⟩
      PFun.id ∎
      where
        open Pre (⊑-Preorder D D)
        module EqC⇀D = IsEquivalence (PFun.isEquivalence {A = C} {B = D})
        module EqD⇀C = IsEquivalence (PFun.isEquivalence {A = D} {B = C})
        module EqD⇀D = IsEquivalence (PFun.isEquivalence {A = D} {B = D})

_⋎_ : {A B : Set} (f g : A ⇌ B) → (A ⇌ B)
f ⋎ g = record
  { fwd = merge f g
  ; bwd = merge (f ⁻¹) (g ⁻¹)
  ; left-id  = {!!}
  ; right-id = {!!}
  }
  where
    merge : {A B : Set} (f g : A ⇌ B) → (A ⇀ B)
    merge f g = fwd f ∣ fwd (g \\ f)

    -- (fwd (f ⁻¹) ∣ (fwd (g ⁻¹ \\ f ⁻¹))) ∙ (fwd f ∣ fwd (g \\ f)) ⊑ id  ?

    --   (fwd (f ⁻¹) ∣ (fwd (g ⁻¹ \\ f ⁻¹))) ∙ (fwd f ∣ fwd (g \\ f))
    -- ≈
    --   (fwd (f ⁻¹) ∙ (fwd f ∣ fwd (g \\ f))) ∣ (fwd (g ⁻¹ \\ f ⁻¹)) ∙ (fwd f ∣ fwd (g \\ f)))
    -- ⊑
    --   (fwd (f ⁻¹) ∙ (fwd f ∣ fwd (g \\ f)))
    --   ∣ (fwd (g ⁻¹ \\ f ⁻¹) ∙ fwd f)
    --   ∣ (fwd (g ⁻¹ \\ f ⁻¹) ∙ fwd (g \\ f))
    -- ⊑                                         { should be true? }
    --   (fwd (f ⁻¹) ∙ (fwd f ∣ fwd (g \\ f)))
    --   ∣ (fwd (g ⁻¹ \\ f ⁻¹) ∙ fwd f)
    --   ∣ id


    -- How do  ∣ and ∙ interact?

    -- (f ∣ g) ∙ (h ∣ k) ⊑ (f ∙ h) ∣ (g ∙ k) ?  no, think it's the
    -- other way around.

    -- (f ∣ g) ∙ h ≈ (f ∙ h) ∣ (g ∙ h) ?  Yes!
    -- but NOT from the left (only ⊑)

    -- So (f ∣ g) ∙ (h ∣ k) ≈ (f ∙ (h ∣ k)) ∣ (g ∙ (h ∣ k))
    -- which in turn is ⊑ (f ∙ (h ∣ k)) ∣ (g ∙ h) ∣ (g ∙ k)
    -- since we ⊑ is a congruence with respect to the right side of ∣ (but not the left!)
    -- Not sure if we can say any more than that.

    -- Hmm, need to prove some lemmas about \\ too.

    -- Is f ⊑ f | g?  Yes, but not sure that really helps.
