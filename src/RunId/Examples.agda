module RunId.Examples where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Bool
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (_≡_; refl)

open import RunId.Syntax
open import RunId.Utils
open import RunId.TypeRules

private variable
    Γ : PreContext
    cΓ : Context Γ
    σ π ρ : Quantity
    A B C : Term
    a b c d f g n m : Term
    i j k : ℕ

module utilsTests where

    module weaken where
        -- proof : ∀ {cΓ : Context Γ} →           
        --     (i : ℕ) → 
        --     (p : i ≤ conLen Γ) → 
        --     cΓ ⊢ a 𝕢 σ ∶ A →
        --     insertType cΓ i p B ρ
        --         ⊢ shiftindices a 1 i 𝕢 σ ∶ A
        -- proof zero z≤n (⊢var i) = ⊢var {! S i  !} {eq = {!   !}}
        -- proof zero z≤n (⊢pi ⊢ ⊢₁) = {!   !}
        -- proof zero z≤n (⊢rpi x ⊢ ⊢₁) = {!   !}
        -- proof zero z≤n (⊢lam ⊢ ⊢₁) = {!   !}
        -- proof zero z≤n (⊢rlam x ⊢ ⊢₁) = {!   !}
        -- proof zero z≤n (⊢app ⊢ ⊢₁) = {!   !}
        -- proof zero z≤n (⊢appᵣ ⊢ ⊢₁) = {!   !}
        -- proof zero z≤n ⊢Nat = {!   !}
        -- proof zero z≤n ⊢z = {!   !}
        -- proof zero z≤n (⊢s ⊢) = {!   !}
        -- proof zero z≤n (⊢natel ⊢ ⊢₁ ⊢₂ ⊢₃) = {!   !}
        -- proof zero z≤n (⊢List ⊢) = {!   !}
        -- proof zero z≤n ⊢nill = {!   !}
        -- proof zero z≤n (⊢∷l ⊢ ⊢₁) = {!   !}
        -- proof zero z≤n (⊢listel ⊢ ⊢₁ ⊢₂ ⊢₃) = {!   !}
        -- proof zero z≤n (⊢Vec ⊢ ⊢₁) = {!   !}
        -- proof zero z≤n (⊢nilv ⊢) = {!   !}
        -- proof zero z≤n (⊢∷v ⊢ ⊢₁ ⊢₂) = {!   !}
        -- proof zero z≤n (⊢vecel ⊢ ⊢₁ ⊢₂ ⊢₃) = {!   !}
        -- proof zero z≤n ⊢Sett = {!   !}
        -- proof zero z≤n (⊢conv ⊢ x) = {!   !}
        -- proof zero z≤n (⊢TM-𝟘 ⊢) = {!   !}

    module substitution where
        lemmaRefl : (i ≡ᵇ i) ≡ true
        lemmaRefl {zero} = refl
        lemmaRefl {suc i} = lemmaRefl {i = i}

        testSimple : var i [ i / a ] ≡ a
        testSimple {i} rewrite lemmaRefl {i = i} = refl

        lemmaSuc : (i ≡ᵇ suc i) ≡ false
        lemmaSuc {zero} = refl
        lemmaSuc {suc i} = lemmaSuc {i = i}

        testIrrelevant : var (suc i) [ i / a ] ≡ var (suc i)
        testIrrelevant {i} rewrite lemmaSuc {i} = refl

        module free where
            testLam : (ƛ∶ Nat 𝕢 σ ♭ var 1) [ 0 / z ] ≡ ((ƛ∶ Nat 𝕢 σ ♭ z))
            testLam = refl

            testLam2 : (ƛ∶ Nat 𝕢 σ ♭ var 1) [ 0 / var 0 ] ≡ ((ƛ∶ Nat 𝕢 σ ♭ var 1))
            testLam2 = refl

        module caught where
            testLam : (ƛ∶ Nat 𝕢 σ ♭ var 0) [ 0 / a ] ≡ ((ƛ∶ Nat 𝕢 σ ♭ var 0))
            testLam = refl

module ~ᵣTests where

    --- TEST CASES FOR SUBBING I IN

    -- -- module etalist where

    -- --     ~ᵣelimlId0 :  
    -- --         (eliml var 0 ty∶ Nat P∶ Vec Nat (n 𝕢 𝟘) 
    -- --         nb∶ var 0 
    -- --         cb∶ var 3)
    -- --         ~ᵣ 
    -- --         var 0
    -- --     ~ᵣelimlId0 =
    -- --         ~ᵣηlist
    -- --             ~ᵣrefl
    -- --             ~ᵣrefl

    -- --     ~ᵣelimlId1 :  
    -- --         (eliml var 1 ty∶ Nat P∶ Vec Nat (n 𝕢 𝟘) 
    -- --         nb∶ var 1 
    -- --         cb∶ var 4)
    -- --         ~ᵣ 
    -- --         var 1
    -- --     ~ᵣelimlId1 =
    -- --         ~ᵣηlist
    -- --             ~ᵣrefl
    -- --             ~ᵣrefl

    -- --     ~ᵣelimlAcc :  
    -- --         (eliml var 0 ty∶ Nat P∶ Vec Nat (n 𝕢 𝟘) 
    -- --         nb∶ nilv𝕢 𝟘 
    -- --         -- value of index (n/m) doesnt matter for this test
    -- --         cb∶ (var 2 ∷v var 0 𝕟 m 𝕢 𝟘))
    -- --         ~ᵣ 
    -- --         var 0
    -- --     ~ᵣelimlAcc =
    -- --             ~ᵣηlist
    -- --                 ~ᵣnilv𝟘  
    -- --                 (~ᵣ∷v𝟘 ~ᵣrefl ~ᵣrefl)
                    
    -- --     ~ᵣelimlTail : 
    -- --         (eliml var 0 ty∶ Nat P∶ Vec Nat (n 𝕢 𝟘)
    -- --         nb∶ nilv𝕢 𝟘 
    -- --         -- value of index (n/m) doesnt matter for this test
    -- --         cb∶ (var 2 ∷v var 1 𝕟 m 𝕢 𝟘))
    -- --         ~ᵣ 
    -- --         var 0
    -- --     ~ᵣelimlTail = 
    -- --         ~ᵣηlist
    -- --             ~ᵣnilv𝟘
    -- --             (~ᵣ∷v𝟘 ~ᵣrefl ~ᵣrefl)

    -- module etavec where

    --     ~ᵣelimvId0 :  
    --         -- should be independent of σ?
    --         (elimv (var 0 𝕢 σ) ty∶ Nat P∶ Vec Nat (n 𝕢 𝟘) 
    --         nb∶ var 0 
    --         cb∶ var 4)
    --         ~ᵣ 
    --         var 0
    --     ~ᵣelimvId0 =
    --         ~ᵣηvec 
    --             ~ᵣrefl 
    --             ~ᵣrefl

    --     ~ᵣelimvId1 :  
    --         (elimv (var 0 𝕢 𝟘) ty∶ Nat P∶ Vec Nat (n 𝕢 𝟘) 
    --         nb∶ var 1 
    --         cb∶ var 5)
    --         ~ᵣ 
    --         var 1
    --     ~ᵣelimvId1 =
    --         ~ᵣηvec 
    --             ~ᵣrefl 
    --             ~ᵣrefl

    --     ~ᵣelimvAcc :  
    --         (elimv (var 0 𝕢 𝟘) ty∶ Nat P∶ List Nat 
    --         nb∶ nill 
    --         cb∶ (var 2 ∷l var 0))
    --         ~ᵣ 
    --         var 0
    --     ~ᵣelimvAcc =
    --         ~ᵣηvec 
    --             (~ᵣsym ~ᵣnilv𝟘) 
    --             (~ᵣsym (~ᵣ∷v𝟘 ~ᵣrefl ~ᵣrefl))
                    
    --     ~ᵣelimvTail :  
    --         (elimv (var 0 𝕢 𝟘) ty∶ Nat P∶ List Nat 
    --         nb∶ nill 
    --         cb∶ (var 2 ∷l var 1))
    --         ~ᵣ 
    --         var 0
    --     ~ᵣelimvTail = 
    --         ~ᵣηvec 
    --             (~ᵣsym ~ᵣnilv𝟘) 
    --             (~ᵣsym (~ᵣ∷v𝟘 ~ᵣrefl ~ᵣrefl))


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
        testZ = ⊢var Z refl

        testSZ : ((cΓ , Nat 𝕢 σ) , List Nat 𝕢 ρ) ⊢ var 1 𝕢 σ ∶ Nat
        testSZ = ⊢var (S Z) refl
        

    module functions where

        module id where
            idTy : Type 
            idTy = ∶ Sett 0  𝕢 𝟘 ⟶ (∶ var 0 𝕢 ω ⟶ (var 1))

            idDef : Term
            idDef = ƛ∶ Sett 0  𝕢 𝟘 ♭ (ƛ∶ var 0 𝕢 ω ♭ (var 0))

            idTyped : [] ⊢ idDef 𝕢 ω ∶ idTy
            idTyped = ⊢lam  (⊢lam (⊢var Z refl) (⊢var Z refl)) ⊢Sett 

            idTypedGen : cΓ ⊢ idDef 𝕢 ω ∶ idTy
            idTypedGen = ⊢lam (⊢lam (⊢var Z refl) (⊢var Z refl)) ⊢Sett
    
        module const where
            -- testTy : Term
            -- testTy = {!   !}

        module regular where
            -- testTy : Term
            -- testTy = {!   !}
        module runid where
            -- testTy : Term
            -- testTy = {!   !}
    
    module application where

        module regular where
            open import Relation.Binary.PropositionalEquality
            -- testTy : Term
            -- testTy = {!   !}
            tmp : cΓ ≡ ((cΓ +c (𝟘 *c zeroC Γ)) +c (ω *c zeroC Γ))
            tmp {[]} {cΓ = []} = refl
            tmp {Γ , x} {cΓ = cΓ , .x 𝕢 σ} = cong (λ cΓ' → cΓ' , x 𝕢 σ) (tmp {cΓ = cΓ})

            idAppTyped : cΓ  ⊢ (functions.id.idDef ·𝟘 Nat ·ω z) 𝕢 ω ∶ Nat
            idAppTyped {Γ} {cΓ = cΓ} = ⊢app (⊢app functions.id.idTypedGen ⊢Nat {sym +c-rightid0}) ⊢z {sym +c-rightid0} 

        module erased where
            -- testTy : Term
            -- testTy = {!   !}
        
        module runid where    
            -- testTy : Term
            -- testTy = {!   !}
    
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
                testsz = ⊢s {!  !}
            

            -- Maybe also some tests for dependent P?
            module eliminators where
                -- -- Green slime from _+c_ in result
                -- test : cΓ ⊢ 
                --     (elNat z Nat 
                --         (s z) 
                --         (s (var 0))) 𝕢 σ ∶ Nat
                -- test = 
                --     {!  ⊢natel ? ? ? ?  !}                
        
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
                testconsNat : cΓ ⊢ (z ∷l nill) 𝕢 σ ∶ List Nat
                testconsNat = ⊢∷l {!   !} {!   !}

                testcons : 
                    cΓ ⊢ a 𝕢 σ ∶ A →
                    cΓ ⊢ (a ∷l nill) 𝕢 σ ∶ List A
                testcons ⊢a = ⊢∷l ⊢a {!   !}
            
            -- Maybe also some tests for dependent P?
            module eliminators where
                -- test : {!   !} ⊢ 
                --     (eliml {!   !} ty∶ {!   !} P∶ {!   !} 
                --         nb∶ {!   !} 
                --         cb∶ {!   !}) 𝕢 {!   !} ∶ {!   !}
                -- test = {!   !}
                
        module vectors where

            module formers where
                -- test : {!   !} ⊢ {!   !} 𝕢 {!   !} ∶ {!   !}
                -- test = {!   !}

            module constructors where 
                -- test : {!   !} ⊢ {!   !} 𝕢 {!   !} ∶ {!   !}
                -- test = {!   !}
            
            module eliminators where
                -- test : {!   !} ⊢ {!   !} 𝕢 {!   !} ∶ {!   !}
                -- test = {!   !}
    module mapHOF where
        idNatDef : Term
        idNatDef = ƛr∶ Nat ♭ var 0

        idNatTyped : cΓ ⊢ idNatDef 𝕢 ω ∶ (r∶ Nat ⟶ Nat)
        idNatTyped = 
            {!   !}

        mapType : Type
        mapType = 
            -- A
            ∶ Sett 0 𝕢 𝟘 ⟶
            -- B 
            ∶ Sett 0 𝕢 𝟘 ⟶ 
            -- (f : A ->r B)
            ∶ r∶ var 1 ⟶ var 1 𝕢 ω ⟶ 
            r∶ List (var 2) ⟶ List (var 2)

        mapDef : Term 
        mapDef = 
            ƛ𝟘∶ Sett 0 ♭ ƛ𝟘∶ Sett 0 ♭
                ƛω∶ r∶ var 1 ⟶ var 1 ♭ 
                    ƛr∶  List (var 2) ♭ 
                        elimlᵣ var 0 ty∶ var 3 P∶ ƛ𝟘∶ (List (var 3)) ♭ (List (var 4)) 
                            nb∶ nill 
                            cb∶ ((var 4 ·ᵣ var 2) ∷l var 0)
        
        mapTyped : cΓ ⊢ mapDef 𝕢 σ ∶ mapType
        mapTyped {cΓ = cΓ} = 
            ⊢lam 
                (⊢lam 
                    (⊢lam 
                        (⊢rlam 
                            ~ᵣelimlᵣ 
                            (⊢conv 
                                (⊢listelᵣ 
                                    {!   !} {!   !} {!   !} 
                                    (⊢var Z refl) 
                                    {!   !} 
                                    (~ᵣsym (~ᵣbeta𝟘 ~ᵣrefl)) 
                                    {!   !} 
                                    ~ᵣrefl 
                                    (⊢conv 
                                        (⊢∷l 
                                            (⊢appᵣ 
                                                (⊢var (S (S (S (S Z)))) refl) 
                                                (⊢var (S (S Z)) refl)) 
                                            (⊢conv (⊢var Z refl) {!   !})) 
                                        {!   !}) 
                                    (inj₁ (~ᵣ∷l ~ᵣappr ~ᵣrefl))) 
                                {!   !})
                            {!   !})
                        -- stuck because cant compare types
                        (⊢rpi (⊢var (S Z) refl) (⊢var (S Z) refl))) 
                    ⊢Sett) 
                ⊢Sett

    module mapHOFBeta where
        liftHOF : ℕ → Term → Term
        liftHOF i (var x) = var x
        liftHOF i (ƛ∶ x ♭ e) = ƛ∶ x ♭ liftHOF (suc i) e
        liftHOF i (ƛr∶ x ♭ e) = {!   !}
        liftHOF i (var j ·ω e₁) = if (i ≡ᵇ j) then var j ·ᵣ e₁ else var j ·ω e₁
        liftHOF i (e · e₁ 𝕢 x) = {!   !}
        liftHOF i (e ·ᵣ e₁) = {!   !}
        liftHOF i z = {!   !}
        liftHOF i (s e) = {!   !}
        liftHOF i nill = nill
        liftHOF i (e ∷l e₁) = liftHOF i e ∷l liftHOF i e₁
        liftHOF i (nilv𝕢 x) = {!   !}
        liftHOF i (e ∷v e₁ 𝕟 e₂ 𝕢 x) = {!   !}
        liftHOF i (elNat e P∶ e₁ zb∶ e₂ sb∶ e₃) = {!   !}
        liftHOF i (eliml e ty∶ innerty P∶ P nb∶ nb cb∶ cb) = 
            eliml liftHOF i e ty∶ liftHOF i innerty P∶ liftHOF (suc i) P nb∶ liftHOF i nb cb∶ liftHOF (3 + i) cb
        liftHOF i (elimv x ty∶ innerty P∶ e nb∶ e₁ cb∶ e₂) = {!   !}
        liftHOF i Nat = Nat
        liftHOF i (List x) = List (liftHOF i x)
        liftHOF i (Vec x x₁) = {!   !}
        liftHOF i (∶ x ⟶ x₁) = {!   !}
        liftHOF i (r∶ x ⟶ x₁) = {!   !}
        liftHOF i (Sett x) = {!   !}

        idNatDef : Term
        idNatDef = ƛr∶ Nat ♭ var 0

        idNatTyped : cΓ ⊢ idNatDef 𝕢 ω ∶ (r∶ Nat ⟶ Nat)
        idNatTyped = 
            {!   !}

        mapDef : Term 
        mapDef = ƛω∶ ∶ (Nat 𝕢 ω) ⟶ Nat ♭ ƛω∶ List Nat ♭ (eliml var 0 ty∶ Nat P∶ List Nat nb∶ nill cb∶ ((var 4 ·ω var 2) ∷l var 0))

        mapBody = ƛω∶ List Nat ♭ (eliml var 0 ty∶ Nat P∶ List Nat nb∶ nill cb∶ ((var 4 ·ω var 2) ∷l var 0))
        
        mapRBody = ƛr∶ List Nat ♭ (eliml var 0 ty∶ Nat P∶ List Nat nb∶ nill cb∶ ((var 4 ·ω var 2) ∷l var 0))

        exDef : Term
        exDef = ƛr∶ List Nat ♭ (((ƛω∶ r∶ Nat ⟶ Nat ♭ liftHOF 0 mapBody) ·ω idNatDef) ·ω (var 0))

        ~betaex : (ƛ∶ r∶ Nat ⟶ Nat 𝕢 ω ♭ liftHOF 0 mapBody ·ω idNatDef ·ω var 0) ~ᵣ var 0
        ~betaex = (~ᵣtrans (~ᵣappω ~ᵣbetaω ~ᵣrefl) (~ᵣtrans ~ᵣbetaω (~ᵣηlist ~ᵣrefl (~ᵣ∷l ~ᵣappr ~ᵣrefl)))) 

        convRule : 
            a ＝ b → 
            b ~ᵣ c → 
            a ~ᵣ c

        ~betaexConv : (ƛ∶ r∶ Nat ⟶ Nat 𝕢 ω ♭ liftHOF 0 mapBody ·ω idNatDef ·ω var 0) ~ᵣ var 0
        ~betaexConv = convRule 
            (betapp ＝beta ＝beta) 
            (~ᵣηlist ~ᵣrefl (~ᵣ∷l ~ᵣappr ~ᵣrefl))

        exTyped : [] ⊢ exDef 𝕢 ω ∶ (r∶ List Nat ⟶ List Nat)
        exTyped = 
            ⊢rlam {𝓁 = 0}
                -- body ~ var 0
                ~betaex
                -- [], List Nat ⊢ body : List Nat 
                (⊢app 
                    {cΓ = [] , (List Nat 𝕢  ω)}
                    {cΓ' = [] , (List Nat 𝕢 ω)}
                    -- Do I here need to "upgrade" map?
                    -- ? ⊢ map ·ω idNat : List Nat -> List Nat
                    (⊢app 
                        {cΓ = [] , (List Nat) 𝕢 ω}
                        {cΓ' = [] , (List Nat 𝕢 ω)}
                        -- ? ⊢ map : (Nat ->r Nat) -> (List Nat -> List Nat)
                        (⊢lam {𝓁 = 0} 
                            -- how about upgrade here to runid?
                            -- ?, Nat ->r Nat ⊢ λ : List Nat ♭ elimbody : List Nat → List Nat 
                            (⊢lam {𝓁 = 0}
                                -- ?, Nat ->r Nat, List Nat ⊢ elimbody : List Nat
                                (let cΓPresent = [] , List Nat 𝕢 ω , (r∶ Nat ⟶ Nat) 𝕢 ω , List Nat 𝕢 ω in 
                                ⊢listel {𝓁 = 0}
                                    {cΓ = cΓPresent}
                                    {cΓ' = zeroC ([] , List Nat , (r∶ Nat ⟶ Nat) , List Nat)}
                                    {cΓ'' = cΓPresent}
                                    -- var 0 : List Nat  
                                    (⊢var Z refl) 
                                    -- List Nat : Set
                                    (⊢List ⊢Nat) 
                                    ⊢nill
                                    -- List Nat, Nat ->r Nat, List Nat , Nat, List Nat, List Nat ⊢ (var 4 ·ᵣ var 2) ∷l var 0 : List Nat
                                    (⊢∷l 
                                        (let cΓCur = cΓPresent , Nat 𝕢 ω , List Nat 𝕢 ω , List Nat 𝕢 ω in 
                                        (⊢appᵣ 
                                            {cΓ = cΓCur}
                                            {cΓ' = cΓCur}
                                            (⊢var (S (S (S (S Z)))) refl) 
                                            (⊢var (S (S Z)) refl) 
                                            {refl})) 
                                        (⊢var Z refl))
                                    {refl})
                                --  
                              (⊢List ⊢Nat))
                            -- ? ⊢ Nat ->r Nat : Set 
                            {!   !}) -- (⊢rpi ⊢Nat ⊢Nat))
                        -- ? ⊢ idNat : Nat ->r Nat  
                        idNatTyped
                        {refl}) 
                    -- [], List Nat ⊢ var 0 : List Nat
                    (⊢var Z refl)
                    {refl})
                -- List Nat : Set 
                {!   !} -- (⊢List ⊢Nat) 
                
        -- cant do this
        -- Which itself is not a type rule that can organically happen, I dont have point free programming
        exTyped2 : [] ⊢ ((ƛω∶ r∶ Nat ⟶ Nat ♭ liftHOF 0 mapBody) ·ω idNatDef) 𝕢 ω ∶ (r∶ List Nat ⟶ List Nat)
        exTyped2 = 
            ⊢app {cΓ = contFun} {cΓ' = contArg} 
                (⊢lam
                    -- (contFun , List Nat 𝕢 ω) ⊢ (eliml var 0 ty∶ Nat P∶ List Nat nb∶ nill cb∶ ((var 4 ·ᵣ var 2) ∷l var 0)) 
                    {!  ⊢lam ?  ?!}
                    (⊢rpi ⊢Nat ⊢Nat)) 
                idNatTyped
                where
                    contFun = {!   !}
                    contArg = {!   !}  
            
        exTyped3Fail : [] ⊢ (((ƛω∶ r∶ Nat ⟶ Nat ♭ liftHOF 0 mapBody) ·ω idNatDef) ·ᵣ var 0) 𝕢 ω ∶ List Nat
        exTyped3Fail = 
            ⊢appᵣ {cΓ = []} {cΓ' = []} 
                (⊢conv 
                    (let
                            contFun = {!   !}
                            contArg = {!   !}
                        in 
                    ⊢app {cΓ = contFun} {cΓ' = contArg}
                        (⊢lam 
                            (⊢lam 
                                {!   !} 
                                {!   !}) 
                            (⊢rpi ⊢Nat ⊢Nat)) 
                        idNatTyped) 
                    -- A -> B = A ->r B no bueno
                    {!   !}) 
                {!   !}
    
        exDefR : Term
        exDefR = ƛr∶ List Nat ♭ (((ƛω∶ r∶ Nat ⟶ Nat ♭ liftHOF 0 mapBody) ·ω idNatDef) ·ᵣ (var 0))

        inferRule : 
            cΓ ⊢ (ƛr∶ A ♭ b) 𝕢 ω ∶ (r∶ A ⟶ B) → 
            cΓ ⊢ (ƛω∶ A ♭ b) 𝕢 ω ∶ (r∶ A ⟶ B)  
            
        exTypedInfer : ([] , List Nat 𝕢 ω) ⊢ (((ƛω∶ r∶ Nat ⟶ Nat ♭ liftHOF 0 mapBody) ·ω idNatDef) ·ᵣ var 0) 𝕢 ω ∶ List Nat
        exTypedInfer = -- {!   !}
            ⊢appᵣ {cΓ = [] , List Nat 𝕢 ω} {cΓ' = [] , List Nat 𝕢 ω} 
                (let
                    contFun = [] , List Nat 𝕢 ω
                    contArg = contFun
                in 
                ⊢app {cΓ = contFun} {cΓ' = contArg}
                    (⊢lam {𝓁 = 0} 
                        (inferRule 
                            (⊢rlam {𝓁 = 0} 
                                (~ᵣηlist ~ᵣrefl (~ᵣ∷l ~ᵣappr ~ᵣrefl)) 
                                (let 
                                    contScr = (contFun , (r∶ Nat ⟶ Nat) 𝕢 ω) , List Nat 𝕢 ω 
                                    contNil = zeroC ([] , List Nat , (r∶ Nat ⟶ Nat) , List Nat) 
                                    contCons = contScr
                                in 
                                    ⊢listel {𝓁 = 0} {cΓ = contScr} {cΓ' = contNil} {cΓ'' = contCons} 
                                        (⊢var Z refl) 
                                        (⊢List ⊢Nat) 
                                        ⊢nill 
                                        (let 
                                            contHead : Context ([] , List Nat , (r∶ Nat ⟶ Nat) , List Nat , Nat , List Nat , List Nat)
                                            contHead = contScr , Nat 𝕢 ω , List Nat 𝕢 ω , List Nat 𝕢 ω 
                                            -- contTail = {!   !} 
                                        in 
                                            ⊢∷l {cΓ = contHead} 
                                                (let
                                                    contRFun : Context ([] , List Nat , (r∶ Nat ⟶ Nat) , List Nat , Nat , List Nat , List Nat) 
                                                    contRFun = contHead 
                                                    contRArg = contHead 
                                                in
                                                    ⊢appᵣ {cΓ = contRFun} {cΓ' = contRArg} 
                                                        (⊢var (S (S (S (S Z)))) refl) 
                                                        (⊢var (S (S Z)) refl) 
                                                        {refl}) 
                                                (⊢var Z refl))
                                        {refl}) 
                                (⊢List ⊢Nat))) 
                        (⊢rpi ⊢Nat ⊢Nat)) 
                    idNatTyped
                    {refl}) 
                (⊢var Z refl)
                {refl}

    module listToVec where    

        listLengthTy : Term 
        listLengthTy = ∶ Sett 0 𝕢 𝟘 ⟶ ∶ List (var 0) 𝕢 ω ⟶ Nat

        listLengthDef : Term
        listLengthDef = 
            ƛ∶ Sett 0 𝕢 𝟘 ♭ 
                ƛ∶ List (var 0) 𝕢 ω ♭ 
                    eliml (var 0) ty∶ var 1 P∶ Nat 
                        nb∶ z 
                        cb∶ s (var 0)

        listLengthTyped : cΓ ⊢ listLengthDef 𝕢 σ ∶ listLengthTy
        listLengthTyped {cΓ = cΓ} {σ = σ} = 
            {!   !}
            -- ⊢lam
            --     (⊢lam 
            --         (⊢listel 
            --             (⊢var Z refl) 
            --             (⊢Nat {𝓁 = 0}) 
            --             ⊢z 
            --             (⊢s (⊢var Z refl)) 
            --             {?}
            --             -- {cong (λ x → (x , Sett 0 𝕢 𝟘) , List (var 0) 𝕢 σ) (sym +c-rightid0)})
            --         (⊢List (⊢var Z refl))) 
            --     ⊢Sett
                        
        -- Should work in any arbitrary mode
        listLengthTypedEmpty : [] ⊢ listLengthDef 𝕢 σ ∶ listLengthTy
        listLengthTypedEmpty {σ = 𝟘} = 
            ⊢TM-𝟘
                (listLengthTypedEmpty {σ = ω})
        listLengthTypedEmpty {σ = ω} = 
            ⊢lam
                (⊢lam
                    (⊢listel {𝓁 = 0}
                        (⊢var Z refl)
                        ⊢Nat
                        ⊢z
                        (⊢s (⊢var Z refl))
                        {eq = refl})
                    (⊢List (⊢var Z refl)))
                ⊢Sett
                
        listLengthDefComp : ((listLengthDef ·𝟘 Nat) ·ω (z ∷l nill)) ＝ s z
        listLengthDefComp =
            ＝trans
                (betapp
                    ＝beta
                    ＝beta)
                (＝listelc ＝refl (＝listeln ＝refl))

        module Anned where 
            listToVecTy : Term 
            listToVecTy = r∶ List Nat ⟶ Vec𝟘 Nat (listLengthDef ·𝟘 Nat ·ω var 0)

            listToVecDef : Term
            listToVecDef = 
                ƛr∶ List Nat ♭ 
                    elimlᵣ var 0 ty∶ Nat P∶ Vec𝟘 Nat (listLengthDef ·𝟘 Nat ·ω var 0) 
                        nb∶ nilv𝟘 
                        -- Too lazy to just fetch it directly from the vector 
                        cb∶ (var 2 ∷v var 0 𝕟𝟘 (listLengthDef ·𝟘 Nat ·ω var 1))  
            listToVecTyped : cΓ ⊢ listToVecDef 𝕢 ω ∶ listToVecTy 
            -- listToVecTyped {Γ} {cΓ = cΓ} = 
            --     ⊢rlam 
            --         ~ᵣelimlᵣ 
            --         (let 
            --             contScr = {!   !} 
            --             contNil = {!   !} 
            --             contCons = {!   !}
            --         in 
            --             ⊢listelᵣ
            --                 contScr contNil contCons 
            --                 (⊢var Z refl) 
            --                 {!   !} 
            --                 (~ᵣsym (~ᵣvec𝟘 ~ᵣrefl)) 
            --                 {!   !} 
            --                 ~ᵣnilv𝟘 
            --                 {!   !} 
            --                 (inj₁ (~ᵣ∷v𝟘 ~ᵣrefl ~ᵣrefl))) 
            --         (⊢List ⊢Nat)
            


        listToVecTy : Term 
        listToVecTy = r∶ List Nat ⟶ Vec𝟘 Nat (listLengthDef ·𝟘 Nat ·ω var 0) 

        listToVecDef : Term
        listToVecDef = 
            ƛr∶ List Nat ♭ 
                (eliml var 0 ty∶ Nat P∶ Vec𝟘 Nat (listLengthDef ·𝟘 Nat ·ω var 0) 
                    nb∶ nilv𝟘 
                    -- Too lazy to just fetch it directly from the vector 
                    cb∶ (var 2 ∷v var 0 𝕟𝟘 (listLengthDef ·𝟘 Nat ·ω var 1)))  

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

        listToVecTyped : cΓ ⊢ listToVecDef 𝕢 ω ∶ listToVecTy 
        listToVecTyped {Γ} {cΓ = cΓ} = 
            ⊢rlam {𝓁 = 0} 
                (~ᵣηlist ~ᵣnilv𝟘 (~ᵣ∷v𝟘 ~ᵣrefl ~ᵣrefl)) 
                (⊢listel {𝓁 = 0} 
                    (⊢var Z refl) 
                    (⊢Vec {𝓁 = 0} {cΓ = cΓ , List Nat 𝕢 𝟘 , List Nat 𝕢 𝟘}
                        (⊢app {cΓ = cΓ , List Nat 𝕢 𝟘 , List Nat 𝕢 𝟘} 
                            (⊢app (listLengthTyped) (⊢Nat {𝓁 = 0}) {sym +c-rightid0}) 
                            (⊢var Z refl)
                            {cong (λ x → x , ((List Nat) 𝕢 𝟘) , (List Nat 𝕢 𝟘)) (sym +c-idempotent)}) 
                        (⊢Nat {𝓁 = 0})) 
                    (⊢conv 
                        (⊢nilv {𝓁 = 0} ⊢Nat) 
                        lemmaVec＝base) 
                    (⊢conv 
                        (⊢∷v 
                            (⊢var (S (S Z)) refl)
                            (⊢app {cΓ = cΓ∷} 
                                (⊢app listLengthTyped (⊢Nat {𝓁 = 0}) {sym +c-rightid0}) 
                                (⊢var 
                                    {cΓ = zeroC (Γ , List Nat , Nat , List Nat , Vec𝟘 Nat (listLengthDef ·𝟘 Nat ·ω var 0))} 
                                    (S Z) 
                                    refl) 
                                {cong (λ x → x , List Nat 𝕢 ω , Vec𝟘 Nat (listLengthDef ·𝟘 Nat ·ω var 0) 𝕢 ω) (sym +c-idempotent)})
                            (⊢var Z refl)) 
                        lemmaVec＝ind)
                    {cong (λ x → x , List Nat 𝕢 ω) (sym (trans (cong (λ x → cΓ +c x) +c-idempotent) +c-rightid0))})
                (⊢List ⊢Nat)
                where
                    cΓ∷ = zeroC Γ , List Nat 𝕢 𝟘 , Nat 𝕢 ω , List Nat 𝕢 ω , (Vec𝟘 Nat (listLengthDef ·𝟘 Nat ·ω var 0)) 𝕢 ω

        lenAppLemma :  ∀ {xs} →
            cΓ ⊢ A 𝕢 𝟘 ∶ Sett 0 →
            cΓ ⊢ xs 𝕢 σ ∶ List A →
            cΓ ⊢ ((listLengthDef ·𝟘 A) ·ω xs) 𝕢 σ ∶ Nat
        lenAppLemma ⊢A ⊢xs = 
            ⊢app 
                (⊢app {cΓ = {!   !}}
                    listLengthTyped 
                    ⊢A
                    {eq = refl})
                ⊢xs
                {eq = {! refl  !}} 

        listToVecGenTy : Type
        listToVecGenTy =
            -- A 
            ∶ (Sett 0) 𝕢 𝟘 ⟶ 
                -- B
                ∶ (Sett 0) 𝕢 𝟘 ⟶
                --  f: A -->r B
                ∶ (r∶ (var 1) ⟶ (var 1)) 𝕢 ω ⟶ 
                -- (xs : List A) -> Vec B (len xs)
                (r∶ List (var 2) ⟶ Vec𝟘 (var 1) ((listLengthDef ·𝟘 var 2) ·ω (var 0)))

        listToVecGenDef : Term
        listToVecGenDef = 
            ƛ𝟘∶ (Sett 0) ♭ 
                ƛ𝟘∶ (Sett 0) ♭ 
                    ƛω∶ (r∶ (var 1) ⟶ (var 1)) ♭ 
                        ƛr∶ (List (var 2)) ♭ 
                            eliml (var 0) ty∶ var 3 P∶ (Vec𝟘 (var 3) ((listLengthDef ·𝟘 (var 4)) ·ω (var 0))) 
                                nb∶ nilv𝟘 
                                cb∶ ((var 2) ∷v (var 0) 𝕟𝟘 ((listLengthDef ·𝟘 Nat) ·ω var 1))

        listToVecGenTypedEmpty : [] ⊢ listToVecGenDef 𝕢 ω ∶ listToVecGenTy
        listToVecGenTypedEmpty = 
            ⊢lam 
                (⊢lam 
                    (⊢lam 
                        (⊢rlam 
                            (~ᵣηlist ~ᵣnilv𝟘 (~ᵣ∷v𝟘 ~ᵣrefl ~ᵣrefl)) 
                            (⊢conv 
                                (⊢listel 
                                    (⊢var Z refl) 
                                    (⊢Vec (lenAppLemma (⊢var (S (S (S (S Z)))) refl) (⊢var Z refl)) (⊢var (S (S (S Z))) refl)) 
                                    (⊢conv 
                                        (⊢nilv (⊢var (S (S (S Z))) refl)) 
                                        {!   !}) 
                                    (⊢conv 
                                        (⊢∷v (⊢var (S (S Z)) refl) {!   !} {!   !}) 
                                        -- invalid bc 6 != 3
                                        {!   !})
                                    {eq = {!   !}}) 
                                -- invalid bc 3 != 1
                                {!   !}) 
                            (⊢List (⊢var (S (S Z)) refl))) 
                        -- Cant prove this since its var 2 ~ var 1, I dont know yet that they will 
                        -- I would rather like to assume it
                        (⊢rpi (⊢var (S Z) refl) (⊢var (S Z) refl))) 
                    ⊢Sett)
                ⊢Sett

        listFoldrTy : Type
        listFoldrTy = 
            -- A : Set
            ∶ (Sett 0) 𝕢 𝟘 ⟶
            -- P : Set
            ∶ (Sett 0) 𝕢 𝟘 ⟶
            -- p : P 
            ∶ (var 0) 𝕢 ω ⟶
            -- (a : A) -> (as : List A) -> (p : P) -> P
            ∶ (∶ var 2 𝕢 ω ⟶ ∶ List (var 3) 𝕢 ω ⟶ ∶ var 3 𝕢 ω ⟶ var 4) 𝕢 ω ⟶ 
            ∶ List (var 3) 𝕢 ω ⟶ 
            var 3

        listFoldrDef : Term 
        listFoldrDef = 
            -- A : Set    P : Set
            ƛ𝟘∶ (Sett 0) ♭ ƛ𝟘∶ (Sett 0) ♭ 
                -- base : P
                ƛω∶ (var 0) ♭
                -- step : A -> List A -> P -> P
                ƛω∶ ∶ var 2 𝕢 ω ⟶ ∶ List (var 3) 𝕢 ω ⟶ ∶ var 3 𝕢 ω ⟶ var 4 ♭ 
                    -- xs 
                    ƛω∶ List (var 3) ♭ 
                        eliml (var 0) ty∶ var 4 P∶ var 4 
                            nb∶ var 2 
                            cb∶ var 4 ·ω var 2 ·ω var 1 ·ω var 0  
        vecToListTy : Type
        vecToListTy = 
            -- A : Set
            ∶ Sett 0 𝕢 𝟘 ⟶
            -- n : N 
            ∶ Nat 𝕢 𝟘 ⟶ 
            -- Vec A n
            r∶ Vec𝟘 (var 1) (var 0) ⟶
            List (var 2)
        vecToListDef : Term    
        vecToListDef = 
            {!   !}

        module mapTest where
            mapListTy : Type
            mapListTy = 
                -- A : Set 
                ∶ Sett 0 𝕢 𝟘 ⟶
                -- B : Set 
                ∶ Sett 0 𝕢 𝟘 ⟶ 
                -- f : A -->r B
                ∶ r∶ {!   !} ⟶ {!   !} 𝕢 ω ⟶ 
                {!   !}

            mapRListTy : Type
            mapRListTy =
                -- A : Set 
                ∶ Sett 0 𝕢 𝟘 ⟶
                -- B : Set 
                ∶ Sett 0 𝕢 𝟘 ⟶ 
                -- f : A -->r B
                ∶ (r∶ (var 1) ⟶ (var 1)) 𝕢 ω ⟶ 
                -- List A
                r∶ List (var 2) ⟶
                List (var 3)
            
            mapRListDef : Term
            mapRListDef = 
                -- A 
                ƛ𝟘∶ {!   !} ♭ {!   !}
        
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
                (⊢rpi ⊢Nat ⊢Nat)
        -}                      