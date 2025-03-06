module RunId.Examples where

open import Data.Unit
open import Data.Empty
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RunId.Syntax
open import RunId.Utils
open import RunId.TypeRules

private variable
    Γ : PreContext
    cΓ : Context Γ
    σ π : Quantity
    A B C : Term
    a b c d f g n m : Term
-- common patterm
betapp : (f · a 𝕢 σ) ＝  g → (g · c 𝕢 π) ＝ d → ((f · a 𝕢 σ) · c 𝕢 π) ＝ d
betapp inApp outApp = 
    ＝trans
        (＝app
            inApp
            ＝refl)
        outApp

-- may want to make lambda have 0 use
jesper-ex : Term
jesper-ex = (ƛ∶ (r∶ Nat ⟶ Nat) 𝕢 ω ♭ (var 0 ·ᵣ s z)) ·ω (ƛ∶ Nat 𝕢 ω ♭ z)

jesper-l : jesper-ex ~ᵣ s z
jesper-l = 
    ~ᵣtrans
        (~ᵣappω
            (~ᵣlamω ~ᵣappr)
            ~ᵣrefl)
        ~ᵣbetaω

jesper-r : jesper-ex ~ᵣ z
jesper-r = 
    ~ᵣtrans
        ~ᵣbetaω
        -- I cant do normal beta reduction bc application is marked
        (~ᵣtrans
            ~ᵣappr
            -- Stuck with s z ~ z which is not provable
            {!   !})


jesper-ex0D : Term
jesper-ex0D = ƛ∶ (r∶ Nat ⟶ Nat) 𝕢 𝟘 ♭ (var 0 ·ᵣ s z)

jesper-ex0T : Type
jesper-ex0T = ∶ (r∶ Nat ⟶ Nat) 𝕢 𝟘 ⟶ Nat

-- This should be allowed, maybe even use runid as info
jesper-ex0Typed : [] ⊢ jesper-ex0D 𝕢 ω ∶ jesper-ex0T
jesper-ex0Typed = 
    ⊢lam
        (⊢appᵣ
            (⊢var {!   !})
            (⊢s ⊢z))
        (⊢rpi ~ᵣrefl ⊢Nat ⊢Nat)

-- Id example

idTy : Term 
idTy = ∶ Sett 0  𝕢 𝟘 ⟶ (∶ var 0 𝕢 ω ⟶ (var 1))

idDef : Term
idDef = ƛ∶ Sett 0  𝕢 𝟘 ♭ (ƛ∶ var 0 𝕢 ω ♭ (var 0))

idTyped : [] ⊢ idDef 𝕢 ω ∶ idTy
idTyped = ⊢lam  (⊢lam (⊢var Z {eq = refl}) (⊢var Z {eq = refl})) ⊢Sett 


listLengthTy : Term 
listLengthTy = ∶ Sett 0 𝕢 𝟘 ⟶ (∶ List (var 0) 𝕢 ω ⟶ Nat)

listLengthDef : Term
listLengthDef = 
    ƛ∶ Sett 0 𝕢 𝟘 ♭ 
        (ƛ∶ List (var 0) 𝕢 ω ♭ 
            (eliml var 0 P∶ ƛ∶ List (var 1) 𝕢 ω ♭ Nat 
                nb∶ z 
                cb∶ s (var 0)))

lemmaContConv : [] ⊢ a 𝕢 σ ∶ A → cΓ ⊢  a 𝕢 σ ∶ A
lemmaContConv {var x} {A = A} {cΓ = cΓ} (⊢conv d x₁) = {!   !}
lemmaContConv {var x} {A = A} {cΓ = cΓ} (⊢TM-𝟘 d) = {!   !}
lemmaContConv {ƛ∶ x ♭ a} {A = A} {cΓ = cΓ} (⊢lam d d₁) = ⊢lam {!   !} {!   !}
lemmaContConv {ƛ∶ x ♭ a} {A = A} {cΓ = cΓ} (⊢conv d x₁) = {!   !}
lemmaContConv {ƛ∶ x ♭ a} {A = A} {cΓ = cΓ} (⊢TM-𝟘 d) = {!   !}
lemmaContConv {ƛr∶ x ♭ a} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {a · a₁ 𝕢 x} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {a ·ᵣ a₁} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {z} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {s a} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {nill} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {a ∷l a₁} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {nilv𝕢 x} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {a ∷v a₁ 𝕟 a₂ 𝕢 x} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {elimnat a P∶ a₁ zb∶ a₂ sb∶ a₃} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {eliml a P∶ a₁ nb∶ a₂ cb∶ a₃} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {elimv a P∶ a₁ nb∶ a₂ cb∶ a₃} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {Nat} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {List a} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {Vec x a} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {∶ x ⟶ a} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {r∶ x ⟶ a} {A = A} {cΓ = cΓ} d = {!   !}
lemmaContConv {Sett x} {A = A} {cΓ = cΓ} d = {!   !}

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
listLengthDefComp : ((listLengthDef ·𝟘 Nat) ·ω (z ∷l nill)) ＝ s z
listLengthDefComp =
    ＝trans
        (betapp
            ＝beta
            ＝beta)
        (＝listelc ＝refl (＝listeln ＝refl))
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
listToVecTy = r∶ List Nat ⟶ Vec Nat (((listLengthDef ·𝟘 Nat) ·ω var 0) 𝕢 𝟘 )

listToVecDef : Term
listToVecDef = 
    ƛr∶ List Nat ♭ 
        (eliml var 0 P∶ ƛ∶ List Nat 𝕢 𝟘 ♭ Vec Nat (((listLengthDef ·𝟘 Nat) ·ω var 0) 𝕢 𝟘) 
            nb∶ nilv𝟘 
            -- Too lazy to just fetch it directly from the vector 
            cb∶ (var 2 ∷v var 0 𝕟𝟘 ((listLengthDef ·𝟘 Nat) ·ω var 1)))  

~ᵣlemma : 
    (eliml var 0 P∶
       ƛ∶ List Nat 𝕢 𝟘 ♭
       Vec Nat (((listLengthDef · Nat 𝕢 𝟘) · var 0 𝕢 ω) 𝕢 𝟘)
       nb∶ nilv𝕢 𝟘 
       cb∶ (var 2 ∷v var 0 𝕟 (listLengthDef · Nat 𝕢 𝟘) · var 1 𝕢 ω 𝕢 𝟘))
      ~ᵣ 
    var 0
~ᵣlemma = 
    ~ᵣηlist
        ~ᵣnilv𝟘        
        {!   !} 

listToVecTyped : [] ⊢ listToVecDef 𝕢 ω ∶ listToVecTy
listToVecTyped = ⊢rlam
        ~ᵣlemma
        (⊢conv 
            (⊢listel {𝓁 = 0} 
                (⊢var Z {eq = refl}) 
                (⊢lam
                    (⊢Vec {!   !} ⊢Nat)                     
                    (⊢List ⊢Nat)) 
                {!   !}
                {!   !}) 
            {!   !}) 
        (⊢List ⊢Nat)
        
listToVecTyped2 : [] ⊢ listToVecTy 𝕢 𝟘 ∶ Sett 0
listToVecTyped2 = 
    ⊢rpi 
        (~ᵣsym (~ᵣvec𝟘 ~ᵣrefl))
        (⊢List ⊢Nat)
        {!   !}

{-
lconv0 : Vec (z 𝕢 𝟘) Nat ＝
      ((ƛ∶ List Nat 𝕢 𝟘 ♭ Vec (((listLengthDef ·𝟘 Nat) ·ω var 0) 𝕢 𝟘) Nat)
       ·𝟘 nill)
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

lconv1 : Vec (s ((listLengthDef ·𝟘 Nat) ·ω var 1) 𝕢 𝟘) Nat ＝
      ((ƛ∶ List Nat 𝕢 𝟘 ♭ Vec (((listLengthDef ·𝟘 Nat) ·ω var 0) 𝕢 𝟘) Nat)
       ·𝟘 (var 2 ∷l var 1))
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

listToVecTyped : [] ⊢ listToVecDef 𝕢 σ ∶ listToVecTy
listToVecTyped {𝟘} = ⊢TM-𝟘 (listToVecTyped {σ = ω})
listToVecTyped {ω} = 
    ⊢lam {𝓁 = 0}
        (⊢conv
            (⊢listel {𝓁 = 0} 
                (⊢var Z {eq = refl})
                (⊢lam {𝓁 = 0} (⊢Vec (⊢app (⊢app 
                        -- (lemmaContConv {cΓ = {!   !}} listLengthTyped) 
                        {!   !}
                    ⊢Nat) (⊢var Z {eq = refl})) ⊢Nat) (⊢List ⊢Nat))
                (⊢conv
                    (⊢nilv {𝓁 = 0} ⊢Nat)
                    lconv0)
                (⊢conv
                    (⊢∷v
                        (⊢var (S (S Z)) {eq = refl})
                        (⊢app 
                            (⊢app 
                                {!   !} -- (lemmaContConv {cΓ = {!   !}} listLengthTyped)
                                ⊢Nat) 
                            (⊢var (S Z) {eq = refl}))
                        (⊢conv
                            (⊢var Z {eq = refl})
                            ＝beta))
                    lconv1))
            ＝beta)
        (⊢List ⊢Nat)

    {- 
        where
            lemmaContext = (((([] , List Nat 𝕢 𝟘) , Nat 𝕢 ω) , List Nat 𝕢 ω) , ((ƛ∶ List Nat 𝕢 𝟘 ♭ Vec (((listLengthDef ·𝟘 Nat) ·ω var 0) 𝕢 𝟘) Nat) ·𝟘 var 0)  𝕢 ω)
    -}
-}
{-    
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
-}