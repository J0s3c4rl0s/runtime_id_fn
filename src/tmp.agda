module tmp where
    module A where
        data ⊤ : Set where
            tt : ⊤

        module C where
            data B : Set where
                c₁_c₂_ : ⊤ → ⊤ → B
            _specialguy_ = B → B → Set

        open C public

    open A using (_specialguy_)

    f : {A.B} → A.B → A.⊤ 
    f {A.c₁ x c₂ x₁} _ = {!   !}