module QTTCalcExamples where

open import Data.Unit

open import QTTCalc

private variable
    Γ Δ Θ : PreContext
    cΓ cΓ' cΓ'' : Context Γ
    cΔ cΔ' cΔ'' : Context Δ
    cΘ : Context Θ
    A B C D P : Term
    σ σ' π π' ρ ρ' ρ'' ρ''' : Quantity
    a b c d e f g h l m n  : Term
    as cs : Term
    nb cb zb sb : Term

-- Id example

idTy : Term 
idTy = ∶ Sett 𝕢 𝟘 ⟶ (∶ var 0 𝕢 ω ⟶ (var 1))

idDef : Term
idDef = ƛ∶ Sett 𝕢 𝟘 ♭ (ƛ∶ var 0 𝕢 ω ♭ (var 0))

idTyped : [] ⊢ idDef 𝕢 ω ∶ idTy
idTyped = ⊢lam  (⊢lam (⊢var Z) (⊢var Z)) ⊢Sett


listLengthTy : Term 
listLengthTy = ∶ Sett 𝕢 𝟘 ⟶ (∶ List (var 0) 𝕢 ω ⟶ Nat)

listLengthDef : Term
listLengthDef = 
    ƛ∶ Sett 𝕢 𝟘 ♭ 
        (ƛ∶ List (var 0) 𝕢 ω ♭ 
            (eliml var 0 P∶ ƛ∶ List (var 1) 𝕢 ω ♭ Nat ty∶ var 1 
                nb∶ z 
                cb∶ (ƛ∶ var 1 𝕢 𝟘 ♭ (ƛ∶ List (var 1) 𝕢 ω ♭ (ƛ∶ Nat 𝕢 ω ♭ s (var 0))))))

-- Should work in any arbitrary mode
listLengthTyped : [] ⊢ listLengthDef 𝕢 σ ∶ listLengthTy
listLengthTyped {σ = 𝟘} = 
    ⊢TM-𝟘
        (listLengthTyped {σ = ω})
listLengthTyped {σ = ω} =
    ⊢lam
        (⊢lam
            (⊢conv
                (⊢listel 
                    (⊢var Z)
                    (⊢lam ⊢Nat ⊢List)
                    (⊢conv ⊢z (＝sym ＝beta))
                    (⊢conv
                        (⊢lam 
                            (⊢lam
                                (⊢lam
                                    (⊢s (⊢var Z))
                                    ⊢Nat)
                                ⊢List)
                            (⊢var (S Z)))
                        (＝pi
                            ＝refl
                            (＝pi
                                ＝refl
                                (＝pi
                                    (＝sym ＝beta)
                                    (＝sym ＝beta))))))
                ＝beta)
            ⊢List)
        ⊢Sett

listLengthDefComp : [] ⊢ (listLengthDef · Nat) · (z ∷l nill) ＝ s z
listLengthDefComp = 
    ＝trans
        (＝app
            ＝beta
            ＝refl)
        (＝trans
            ＝beta
            (＝trans
                (＝listelc
                    ＝refl
                    (＝listeln ＝refl))
                (＝trans
                    (＝app
                        (＝app 
                            ＝beta
                            ＝refl)
                        ＝refl)
                    (＝trans
                        (＝app
                            ＝beta
                            ＝refl)
                        ＝beta))))
listToVecTy : Term 
listToVecTy = ∶ List Nat 𝕢 ω ⟶ Vec (((listLengthDef · Nat) · var 0) 𝕢 𝟘 ) Nat

listToVecDef : Term
listToVecDef = 
    ƛ∶ List Nat 𝕢 ω ♭ 
        (eliml var 0 P∶ ƛ∶ List Nat 𝕢 𝟘 ♭ Vec (((listLengthDef · Nat) · var 0) 𝕢 𝟘) Nat ty∶ Nat 
            nb∶ nilv 
            cb∶ (ƛ∶ Nat 𝕢 ω ♭ 
                    (ƛ∶ List Nat 𝕢 ω ♭ 
                        (ƛ∶ Vec (((listLengthDef · Nat) · var 0) 𝕢 𝟘) Nat 𝕢 ω ♭ (var 2 ∷v var 0)))))

-- common patterm
betapp : cΓ ⊢ f · a ＝  g → cΓ ⊢ g · c ＝ d → cΓ ⊢ (f · a) · c ＝ d
betapp inApp outApp = 
    ＝trans
        (＝app
            inApp
            ＝refl)
        outApp
listToVecTyped : [] ⊢ listToVecDef 𝕢 σ ∶ listToVecTy
listToVecTyped {𝟘} = ⊢TM-𝟘 (listToVecTyped {σ = ω})
listToVecTyped {ω} = 
    ⊢lam
        (⊢conv
            (⊢listel
                (⊢var Z)
                (⊢lam ⊢Vec ⊢List)
                (⊢conv
                    (⊢nilv {π = 𝟘} {A = Nat}) 
                    (＝sym (＝trans
                        ＝beta
                        (＝vec
                            (＝trans
                                (＝app
                                    ＝beta
                                    ＝refl)
                                (＝trans
                                    ＝beta
                                    (＝listeln ＝refl)))
                            ＝refl))))
                (⊢lam
                    (⊢lam
                        (⊢conv
                            (⊢lam
                                (⊢∷v (⊢var (S (S Z))) (⊢var Z))
                                ⊢Vec)
                            (＝pi
                                (＝sym ＝beta)
                                (＝sym (＝trans
                                    ＝beta
                                    (＝vec
                                        (＝trans
                                            (＝app
                                                ＝beta
                                                ＝refl)
                                            (＝trans
                                                ＝beta
                                                (＝trans
                                                    (＝listelc
                                                        ＝refl
                                                        ＝refl)
                                                    (betapp
                                                        (betapp
                                                            ＝beta
                                                            ＝beta)
                                                        (＝trans
                                                            ＝beta
                                                            (＝s (＝sym (betapp
                                                                ＝beta
                                                                (＝trans
                                                                    ＝beta
                                                                    ＝refl)))))))))
                                        ＝refl)))))
                        ⊢List)
                    ⊢Nat))
            ＝beta)
        ⊢List