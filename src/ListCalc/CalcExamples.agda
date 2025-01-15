module CalcExamples where

open import Calc



-- Id example

idTy : Term 
idTy = ∶ Sett ⟶ (∶ var 0 ⟶ (var 0))

idDef : Term
idDef = ƛ∶ Sett ♭ (ƛ∶ var 0 ♭ (var 0))

idTyped : [] ⊢ idDef ∶ idTy
idTyped = ⊢lam (⊢lam (⊢conv (⊢var Z) (＝sym (＝var Z))) (⊢var Z)) ⊢Sett

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
                (⊢conv (⊢var Z) ＝refl) 
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
{-
lemmaIndStep : ∀ {bs} → (((([] , List Nat) , Nat) , List Nat) ,
     Vec ((listLengthDef · Nat) · var 0) Nat)
    ⊢
    (((eliml var 0 P∶ ƛ∶ List (var 1) ♭ Nat ty∶ var 1 nb∶ z cb∶
       (ƛ∶ var 1 ♭ (ƛ∶ List (var 1) ♭ (ƛ∶ Nat ♭ s (var 0)))))
      [ var 2 ∷l var 1 / S (S Z) ])
     [ Nat [ var 2 ∷l var 1 / Z ] / S Z ])
    [ var 0 [ var 2 ∷l var 1 / Z ] / Z ]
    ＝
    s
    (((ƛ∶ Sett ♭
       (ƛ∶ List (var 1) ♭ (eliml var 1 P∶ var 1 ty∶ var 2 nb∶ z cb∶ z)))
      · Nat)
     · var 1)
lemmaIndStep {bs} = 
    ＝trans
        (＝listelc 
            ＝refl
            ＝refl)
        (＝trans
            (＝app
                (＝app
                    ＝refl
                    (＝var (S Z)))
                ＝refl)
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
                    (＝trans
                        ＝beta
                        (＝s (＝sym (＝trans 
                            {!   !}
                            ({!   !})))))))) -- for some reason it inserts z into the cb


lemmaVecCmp : (((([] , List Nat) , Nat) , List Nat) ,
       Vec ((listLengthDef · Nat) · var 0) Nat)
      ⊢
      Vec
      (s
       (((ƛ∶ Sett ♭
          (ƛ∶ List (var 1) ♭ (eliml var 1 P∶ var 1 ty∶ var 2 nb∶ z cb∶ z)))
         · Nat)
        · var 1))
      Nat
      ＝
      ((ƛ∶ List Nat ♭ Vec ((listLengthDef · Nat) · var 0) Nat) ·
       (var 2 ∷l var 1))
lemmaVecCmp = 
    ＝sym (＝trans 
        ＝beta
        (＝trans 
            (＝vec 
                (＝trans
                    (＝app 
                        ＝beta
                        ＝refl)
                    ＝beta)
                ＝refl)
            (＝vec
                {!   !}
                ＝refl)))
-}

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
                            {!   !})
                        ⊢List) 
                    ⊢Nat)) 
            ＝beta) 
        ⊢List  