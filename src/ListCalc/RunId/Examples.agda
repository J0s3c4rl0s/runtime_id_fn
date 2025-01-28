module ListCalc.RunId.Examples where

open import Data.Unit
open import Data.Empty
open import Relation.Nullary using (¬_)

open import ListCalc.RunId.Syntax
open import ListCalc.RunId.Utils
open import ListCalc.RunId.TypeRules

private variable
    Γ : PreContext
    cΓ : Context Γ
    σ π : Quantity
    A B C : Term
    a b c d f g n m : Term

-- common patterm
betapp : cΓ ⊢ f · a ＝  g → cΓ ⊢ g · c ＝ d → cΓ ⊢ (f · a) · c ＝ d
betapp inApp outApp = 
    ＝trans
        (＝app
            inApp
            ＝refl)
        outApp


-- Id example

idTy : Term 
idTy = ∶ Sett 0  𝕢 𝟘 ⟶ (∶ var 0 𝕢 ω ⟶ (var 1))

idDef : Term
idDef = ƛ∶ Sett 0  𝕢 𝟘 ♭ (ƛ∶ var 0 𝕢 ω ♭ (var 0))

idTyped : [] ⊢ idDef 𝕢 ω ∶ idTy
idTyped = ⊢lam  (⊢lam (⊢var Z) (⊢var Z)) ⊢Sett 


listLengthTy : Term 
listLengthTy = ∶ Sett 0  𝕢 𝟘 ⟶ (∶ List (var 0) 𝕢 ω ⟶ Nat)

listLengthDef : Term
listLengthDef = 
    ƛ∶ Sett 0  𝕢 𝟘 ♭ 
        (ƛ∶ List (var 0) 𝕢 ω ♭ 
            (eliml var 0 P∶ ƛ∶ List (var 1) 𝕢 ω ♭ Nat 
                nb∶ z 
                cb∶ s (var 0)))

lemmaContConv : [] ⊢ a 𝕢 σ ∶ A → cΓ ⊢  a 𝕢 σ ∶ A
lemmaContConv d = {!   !}

-- Should work in any arbitrary mode
listLengthTyped : [] ⊢ listLengthDef 𝕢 σ ∶ listLengthTy
listLengthTyped {σ = 𝟘} = 
    ⊢TM-𝟘
        (listLengthTyped {σ = ω})
listLengthTyped {σ = ω} =
    ⊢lam
        (⊢lam
            (⊢conv
                (⊢listel {𝓁 = 0}
                    (⊢var Z)
                    (⊢lam ⊢Nat (⊢List (⊢var (S Z))))
                    (⊢conv ⊢z (＝sym ＝beta))
                    (⊢conv 
                        (⊢s (⊢conv 
                            (⊢var Z)
                            ＝beta))
                        (＝sym ＝beta)))
                ＝beta)
            (⊢List (⊢var Z)))
        ⊢Sett
    
listLengthDefComp : [] ⊢ (listLengthDef · Nat) · (z ∷l nill) ＝ s z
listLengthDefComp = 
    ＝trans
        (betapp
            ＝beta
            ＝beta)
        (＝trans
            (＝listelc
                ＝refl
                (＝listeln ＝refl))
            ＝refl)

{-
-- fuck it
vecLengthTy : Term
vecLengthTy = ∶ Vec (_ 𝕢 _) _ 𝕢 _ ⟶ Nat
vecLengthDef : {n : Term} → Term
vecLengthDef {n} = 
    ƛ∶ Vec (n 𝕢 _) _ 𝕢 𝟘 ♭ 
        n
-}

listToVecTy : Term 
listToVecTy = ∶ List Nat 𝕢 ω ⟶ Vec (((listLengthDef · Nat) · var 0) 𝕢 𝟘 ) Nat


listToVecDef : Term
listToVecDef = 
    ƛ∶ List Nat 𝕢 ω ♭ 
        (eliml var 0 P∶ ƛ∶ List Nat 𝕢 𝟘 ♭ Vec (((listLengthDef · Nat) · var 0) 𝕢 𝟘) Nat 
            nb∶ nilv 
            -- Too lazy to just fetch it directly from the vector 
            cb∶ (var 2 ∷v var 0 𝕟 ((listLengthDef · Nat) · var 1)))  

lconv0 : ([] , List Nat 𝕢 𝟘) ⊢ Vec (z 𝕢 𝟘) Nat ＝
      ((ƛ∶ List Nat 𝕢 𝟘 ♭ Vec (((listLengthDef · Nat) · var 0) 𝕢 𝟘) Nat)
       · nill)
lconv0 = 
    ＝sym (＝trans
        ＝beta
        (＝vec 
            (betapp
                ＝beta
                (＝trans
                    ＝beta
                    (＝listeln ＝refl)))
            ＝refl))

lconv1 : (((([] , List Nat 𝕢 𝟘) , Nat 𝕢 𝟘) , List Nat 𝕢 𝟘) ,
       ((ƛ∶ List Nat 𝕢 𝟘 ♭ Vec (((listLengthDef · Nat) · var 0) 𝕢 𝟘) Nat)
        · var 0)
       𝕢 𝟘)
      ⊢ Vec (s ((listLengthDef · Nat) · var 1) 𝕢 𝟘) Nat ＝
      ((ƛ∶ List Nat 𝕢 𝟘 ♭ Vec (((listLengthDef · Nat) · var 0) 𝕢 𝟘) Nat)
       · (var 2 ∷l var 1))
lconv1 = 
    ＝sym (＝trans
        ＝beta
        (＝vec
            (betapp 
                ＝beta
                (＝trans
                    ＝beta
                    (＝listelc
                        ＝refl
                        (＝sym (betapp
                            ＝beta
                            ＝beta)))))
            ＝refl))

{-
lt1 : (((([] , List Nat 𝕢 𝟘) , Nat 𝕢 ω) , List Nat 𝕢 ω) ,
       ((ƛ∶ List Nat 𝕢 𝟘 ♭ Vec (((listLengthDef · Nat) · var 0) 𝕢 𝟘) Nat)
        · var 0)
       𝕢 ω)
      ⊢ ((listLengthDef · Nat) · var 1) 𝕢 ω ∶ Nat
lt1 = 
    ⊢app
        (⊢app
            (⊢lam
                (⊢lam 
                    (⊢conv
                        (⊢listel
                            (⊢var Z)
                            (⊢lam ⊢Nat (⊢List (⊢var (S Z))))
                            (⊢conv ⊢z (＝sym ＝beta))
                            (⊢conv
                                (⊢s (⊢conv
                                    (⊢var Z)
                                    ＝beta))
                                (＝sym ＝beta)))
                        ＝beta)
                    (⊢List (⊢var Z)))
                ⊢Sett )
            ⊢Nat)
        (⊢var (S Z))
-}

listToVecTyped : [] ⊢ listToVecDef 𝕢 σ ∶ listToVecTy
listToVecTyped {𝟘} = ⊢TM-𝟘 (listToVecTyped {σ = ω})
listToVecTyped {ω} = 
    ⊢lam {𝓁 = 0}
        (⊢conv
            (⊢listel {𝓁 = 0} 
                (⊢var Z)
                (⊢lam {𝓁 = 0} (⊢Vec ⊢Nat ⊢Nat) (⊢List ⊢Nat))
                (⊢conv
                    (⊢nilv {𝓁 = 0} ⊢Nat)
                    lconv0) 
                (⊢conv 
                    (⊢∷v
                        (⊢var (S (S Z)))
                        (⊢app
                            (⊢app
                                (lemmaContConv {cΓ = lemmaContext} listLengthTyped)
                                ⊢Nat)
                            (⊢var (S Z)))
                        (⊢conv 
                            (⊢var Z)
                            ＝beta)) 
                    lconv1))
            ＝beta)
        (⊢List ⊢Nat)
        where
            lemmaContext = (((([] , List Nat 𝕢 𝟘) , Nat 𝕢 ω) , List Nat 𝕢 ω) , ((ƛ∶ List Nat 𝕢 𝟘 ♭ Vec (((listLengthDef · Nat) · var 0) 𝕢 𝟘) Nat) · var 0)  𝕢 ω)
 
vecLType : {A n : Term} → Term
vecLType {A} {n} = ∶ Vec (n 𝕢 𝟘) A 𝕢 ω ⟶ Nat

vecLTerm : {A n : Term} →  Term
vecLTerm {A} {n}  = 
    ƛ∶ Vec (n 𝕢 𝟘) A 𝕢 ω ♭ 
        (elimv var 0 P∶ ƛ∶ Nat 𝕢 𝟘 ♭ (ƛ∶ Vec (var 0 𝕢 𝟘) A 𝕢 ω ♭ Nat) 
            nb∶ z 
            -- fetch length from constructors in non-erased position
            cb∶ var 3)

vecLTyped : {n : Term} {p : [] ⊢ n 𝕢 𝟘 ∶ Nat } → ([] ⊢ (vecLTerm {A = Nat} {n = n}) 𝕢 𝟘 ∶ vecLType {A = Nat} {n = n})
vecLTyped {n} {p} = 
    ⊢lam {𝓁 = 0}
        (⊢conv
            (⊢vecel {𝓁 = 0}
                (⊢var Z)
                (⊢lam {𝓁 = 0}
                    (⊢lam {𝓁 = 0} ⊢Nat (⊢Vec ⊢Nat ⊢Nat))
                    ⊢Nat)
                (⊢conv 
                    ⊢z 
                    (＝sym (betapp ＝beta ＝beta)))
                (⊢conv
                    (⊢var (S (S (S Z))))
                    (＝sym (betapp ＝beta ＝beta))))
            (betapp ＝beta ＝beta))
        (⊢Vec ⊢Nat ⊢Nat)

-- Perhaps make the type in question generic, to prove the term is generally invalid
-- Keep it simple with A for now
¬vecLTyped : {n : Term} {p : [] ⊢ n 𝕢 𝟘 ∶ Nat } → ¬ ([] ⊢ (vecLTerm {A = Nat} {n = n}) 𝕢 ω ∶ vecLType {A = Nat} {n = n})
¬vecLTyped {n} {p} (⊢lam (⊢conv d x) d₁) = {!   !}
¬vecLTyped {n} {p} (⊢conv d x) = {!   !}