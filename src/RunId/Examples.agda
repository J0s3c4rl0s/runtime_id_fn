module RunId.Examples where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RunId.Syntax
open import RunId.Utils
open import RunId.TypeRules

private variable
    Γ : PreContext
    cΓ : Context Γ
    σ π ρ : Quantity
    A B C : Term
    a b c d f g n m : Term
    𝓁 𝓁' : ℕ

module utilsTests where
    test : {!   !}


module typeRuleTests where

    -- common patterm
    betapp : (f · a 𝕢 σ) ＝  g → (g · c 𝕢 π) ＝ d → ((f · a 𝕢 σ) · c 𝕢 π) ＝ d
    betapp inApp outApp = 
        ＝trans
            (＝app
                inApp
                ＝refl)
            outApp

    module var where
        testZ : (cΓ , Nat 𝕢 σ) ⊢ var 0 𝕢 σ ∶ Nat
        testZ = ⊢var Z {eq = refl}

        testSZ : ((cΓ , Nat 𝕢 σ) , List Nat 𝕢 ρ) ⊢ var 1 𝕢 σ ∶ Nat
        testSZ = ⊢var (S Z) {eq = refl}
        

    module functions where

        module id where
            idTy : Type 
            idTy = ∶ Sett 0  𝕢 𝟘 ⟶ (∶ var 0 𝕢 ω ⟶ (var 1))

            idDef : Term
            idDef = ƛ∶ Sett 0  𝕢 𝟘 ♭ (ƛ∶ var 0 𝕢 ω ♭ (var 0))

            idTyped : [] ⊢ idDef 𝕢 ω ∶ idTy
            idTyped = ⊢lam  (⊢lam (⊢var Z {eq = refl}) (⊢var Z {eq = refl})) ⊢Sett 
    
        module const where
            testTy : Term
            testTy = {!   !}

        module regular where
            testTy : Term
            testTy = {!   !}
        
        module runid where
            testTy : Term
            testTy = {!   !}
    
    module application where

        module regular where
            testTy : Term
            testTy = {!   !}

        module erased where
            testTy : Term
            testTy = {!   !}
        
        module runid where    
            testTy : Term
            testTy = {!   !}
    
    module datatypes where

        module nats where

            module formers where
                test : zeroC Γ ⊢ Nat 𝕢 𝟘 ∶ Sett 0 
                test = ⊢Nat

            module constructors where 
                testz : zeroC Γ ⊢ z 𝕢 σ ∶ Nat
                testz = ⊢z 

                -- Why is it zeroC for z?
                testsz :  cΓ ⊢ s z 𝕢 σ ∶ Nat
                testsz = ⊢s {!   !}
            

            -- Maybe also some tests for dependent P?
            module eliminators where
                -- Green slime from _+c_ in result
                test : cΓ ⊢ 
                    (elimnat z P∶ Nat 
                        zb∶ s z 
                        sb∶ s (var 0)) 𝕢 σ ∶ Nat
                test = 
                    {!  ⊢natel ? ? ? ?  !}                
        
        module lists where

            module formers where
                testNat : zeroC Γ ⊢ List Nat 𝕢 𝟘 ∶ Sett 0
                testNat = ⊢List ⊢Nat

                testNest : zeroC Γ ⊢ List (List Nat) 𝕢 𝟘 ∶ Sett 0
                testNest = ⊢List (⊢List ⊢Nat)

            module constructors where 
                testnil : zeroC Γ ⊢ nill 𝕢 σ ∶ List A
                testnil = ⊢nill
             
                -- same problem for 0 contxt...
                testcons : cΓ ⊢ (z ∷l nill) 𝕢 σ ∶ List Nat
                testcons = ⊢∷l {!   !} {!   !}
            
            -- Maybe also some tests for dependent P?
            module eliminators where
                test : {!   !} ⊢ 
                    (eliml {!   !} ty∶ {!   !} P∶ {!   !} 
                        nb∶ {!   !} 
                        cb∶ {!   !}) 𝕢 {!   !} ∶ {!   !}
                test = {!   !}
                
        module vectors where

            module formers where
                test : {!   !} ⊢ {!   !} 𝕢 {!   !} ∶ {!   !}
                test = {!   !}

            module constructors where 
                test : {!   !} ⊢ {!   !} 𝕢 {!   !} ∶ {!   !}
                test = {!   !}
            
            module eliminators where
                test : {!   !} ⊢ {!   !} 𝕢 {!   !} ∶ {!   !}
                test = {!   !}


    module listToVec where    

        listLengthTy : Term 
        listLengthTy = ∶ Sett 0 𝕢 𝟘 ⟶ (∶ List (var 0) 𝕢 ω ⟶ Nat)

        listLengthDef : Term
        listLengthDef = 
            ƛ∶ Sett 0 𝕢 𝟘 ♭ 
                (ƛ∶ List (var 0) 𝕢 ω ♭ 
                    (eliml (var 0) ty∶ var 1 P∶ Nat 
                        nb∶ z 
                        cb∶ s (var 0)))
                        
        -- Should work in any arbitrary mode
        listLengthTyped : [] ⊢ listLengthDef 𝕢 σ ∶ listLengthTy
        listLengthTyped {σ = 𝟘} = 
            ⊢TM-𝟘
                (listLengthTyped {σ = ω})
        listLengthTyped {σ = ω} = 
            ⊢lam
                (⊢lam
                    (⊢listel {𝓁 = 0}
                        (⊢var Z {eq = refl})
                        ⊢Nat
                        ⊢z
                        (⊢s (⊢var Z {eq = refl})))
                    (⊢List (⊢var Z {eq = refl})))
                ⊢Sett
                
        listLengthDefComp : ((listLengthDef ·𝟘 Nat) ·ω (z ∷l nill)) ＝ s z
        listLengthDefComp =
            ＝trans
                (betapp
                    ＝beta
                    ＝beta)
                (＝listelc ＝refl (＝listeln ＝refl))


        listToVecTy : Term 
        listToVecTy = r∶ List Nat ⟶ Vec Nat (((listLengthDef ·𝟘 Nat) ·ω var 0) 𝕢 𝟘 )

        listToVecDef : Term
        listToVecDef = 
            ƛr∶ List Nat ♭ 
                (eliml var 0 ty∶ Nat P∶ Vec Nat (((listLengthDef ·𝟘 Nat) ·ω var 0) 𝕢 𝟘) 
                    nb∶ nilv𝟘 
                    -- Too lazy to just fetch it directly from the vector 
                    cb∶ (var 2 ∷v var 0 𝕟𝟘 ((listLengthDef ·𝟘 Nat) ·ω var 1)))  

        ~ᵣlemma : 
            (eliml var 0 ty∶ Nat P∶ Vec Nat (((listLengthDef · Nat 𝕢 𝟘) · var 0 𝕢 ω) 𝕢 𝟘) 
            nb∶ nilv𝕢 𝟘 
            cb∶ (var 2 ∷v var 0 𝕟 (listLengthDef · Nat 𝕢 𝟘) · var 1 𝕢 ω 𝕢 𝟘))
            ~ᵣ 
            var 0
        ~ᵣlemma = 
            ~ᵣηlist
                ~ᵣnilv𝟘  
                (~ᵣ∷v𝟘 ~ᵣrefl ~ᵣrefl) 
            {-
            ~ᵣηlist
                ~ᵣnilv𝟘        
                (inj₁ (~ᵣ∷v𝟘 ~ᵣrefl ~ᵣrefl)) 
            -}
        ~ᵣlemma2 : 
            (eliml var 0 ty∶ Nat P∶
            ƛ∶ List Nat 𝕢 𝟘 ♭ List Nat
            nb∶ nilv𝕢 𝟘 
            cb∶ (var 2 ∷v var 1 𝕟 (listLengthDef · Nat 𝕢 𝟘) · var 1 𝕢 ω 𝕢 𝟘))
            ~ᵣ 
            var 0
        ~ᵣlemma2 = 
            ~ᵣηlist
                ~ᵣnilv𝟘
                (~ᵣ∷v𝟘 ~ᵣrefl ~ᵣrefl)

        lemmaListLengthApp : cΓ ⊢ ((listLengthDef · Nat 𝕢 𝟘) · var 0 𝕢 ω) 𝕢 𝟘 ∶ Nat
        lemmaListLengthApp = 
            {!   !}

        lemmaVec＝base : Vec Nat (z 𝕢 𝟘) ＝
            Vec Nat
            ((((ƛ∶ Sett 0 𝕢 𝟘 ♭
                (ƛ∶ List (var 0) 𝕢 ω ♭
                (eliml var 0 ty∶ var 1 P∶ Nat nb∶ z cb∶ s (var 0))))
                ·𝟘 Nat)
                ·ω nill)
            𝕢 𝟘)
        lemmaVec＝base = 
            ＝sym (＝vec
                (betapp
                    ＝beta
                    (＝trans
                        ＝beta
                        (＝listeln ＝refl)))
                ＝refl)

        lemmaVec＝ind : Vec Nat (s ((listLengthDef · Nat 𝕢 𝟘) · var 1 𝕢 ω) 𝕢 𝟘) ＝
            Vec Nat
            ((((ƛ∶ Sett 0 𝕢 𝟘 ♭
                (ƛ∶ List (var 0) 𝕢 ω ♭
                (eliml var 0 ty∶ var 1 P∶ Nat nb∶ z cb∶ s (var 0))))
                ·𝟘 Nat)
                ·ω (var 2 ∷l var 1))
            𝕢 𝟘)
        lemmaVec＝ind = 
            ＝sym (＝vec
                (betapp
                    ＝beta
                    (＝trans
                        ＝beta
                        (＝listelc
                            ＝refl
                            (＝sym (betapp
                                ＝beta
                                ＝beta)))))
                ＝refl)

        listToVecTyped : [] ⊢ listToVecDef 𝕢 ω ∶ listToVecTy
        listToVecTyped = 
            ⊢rlam {𝓁 = 0}
                ~ᵣlemma
                (⊢listel {𝓁 = 0}
                    (⊢var Z {eq = refl})
                    (⊢Vec
                        (⊢app
                            (⊢app 
                                {!  listLengthTyped  !}
                                (⊢Nat {𝓁 = 0}))
                            (⊢var Z {eq = refl}))
                        ⊢Nat)
                    (⊢conv 
                        (⊢nilv {𝓁 = 0} ⊢Nat)
                        lemmaVec＝base)
                    (⊢conv 
                        (⊢∷v 
                            (⊢var (S (S Z)) {eq = refl})
                            (⊢app 
                                (⊢app {!  listLengthTyped  !} ⊢Nat {eq = refl}) 
                                (⊢var (S Z) {eq = refl})  {eq = refl})
                            (⊢var Z {eq = refl})) 
                        lemmaVec＝ind))
                (⊢List ⊢Nat) 



    module jesperEx where
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
        {-
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
        -}