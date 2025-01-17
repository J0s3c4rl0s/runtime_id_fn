module QTTCalcExamples where

open import Data.Unit

open import QTTCalc

-- Id example

idTy : Term 
idTy = ∶ Sett 𝕢 𝟘 ⟶ (∶ var 0 𝕢 ω ⟶ (var 1))

idDef : Term
idDef = ƛ∶ Sett 𝕢 𝟘 ♭ (ƛ∶ var 0 𝕢 ω ♭ (var 0))

idTyped : [] ⊢ idDef 𝕢 ω ∶ idTy
idTyped = ⊢lam (⊢lam (⊢var Z tt) (⊢var Z tt)) ⊢Sett

{-

listLengthTy : Term 
listLengthTy = ∶ Sett ⟶ (∶ List (var 0) ⟶ Nat)

listLengthDef : Term
listLengthDef = 
    ƛ∶ Sett ♭ 
        (ƛ∶ List (var 0) ♭ 
            (eliml var 0 P∶ ƛ∶ List (var 1) ♭ Nat ty∶ var 1 
                nb∶ z 
                cb∶ (ƛ∶ var 1 ♭ (ƛ∶ List (var 1) ♭ (ƛ∶ Nat ♭ s (var 0))))))
 
listLengthTyped : [] ⊢ listLengthDef ∶ listLengthTy
listLengthTyped = 
    ⊢lam 
        (⊢lam 
            (⊢conv 
            (⊢listel 
                (⊢var Z) 
                (⊢lam ⊢Nat ⊢List) 
                (⊢conv ⊢z (＝sym ＝beta)) 
                (⊢lam 
                    (⊢lam 
                        (⊢conv (⊢lam (⊢s (⊢var Z)) ⊢Nat) (＝sym (＝pi ＝beta ＝beta))) 
                        ⊢List) 
                    (⊢var (S Z))) 
                ) 
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
listToVecTy = ∶ List Nat ⟶ Vec ((listLengthDef · Nat) · var 0) Nat

listToVecDef : Term
listToVecDef = 
    ƛ∶ List Nat ♭ 
        (eliml var 0 P∶ ƛ∶ List Nat ♭ Vec ((listLengthDef · Nat) · var 0) Nat ty∶ Nat 
            nb∶ nilv 
            cb∶ (ƛ∶ Nat ♭ 
                    (ƛ∶ List Nat ♭ 
                        (ƛ∶ Vec ((listLengthDef · Nat) · var 0) Nat ♭ (var 2 ∷v var 0)))))

listToVecTyped : [] ⊢ listToVecDef ∶ listToVecTy
listToVecTyped = 
    ⊢lam 
        (⊢conv 
            (⊢listel 
                (⊢var Z) 
                (⊢lam ⊢Vec ⊢List) 
                (⊢conv 
                    (⊢nilv {A = Nat}) 
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
                                                    (＝trans
                                                        (＝app
                                                            (＝app
                                                                ＝beta
                                                                (＝refl))
                                                            ＝refl)
                                                        (＝trans
                                                            (＝app
                                                                ＝beta
                                                                ＝refl)
                                                            (＝trans
                                                                ＝beta
                                                                (＝s (＝sym (＝trans
                                                                    (＝app
                                                                        ＝beta
                                                                        ＝refl)
                                                                    ＝beta)))))))))
                                        ＝refl)))))
                        ⊢List) 
                    ⊢Nat)) 
            ＝beta) 
        ⊢List    
-} 