module Proofs.Sound where

open import RunId  
-- open import RunIdComp
-- open import Proofs.Relations

private variable
    A B C : Type 
    a b c d : Term 
    Γ : PreContext 
    cΓ : Context Γ

open import Relation.Nullary


module Denot where

    open import Data.List as AgdaList using ([]; _∷_)
    import Data.Vec as AgdaVec

    open import Data.Nat
    open import Data.Unit 
    open import Data.Empty 
    open import Data.Product renaming (_,_ to ⟨_,_⟩)

    module NBETut where


        module logreltut where
            open import Data.Sum
            private variable 
                i j : ℕ
                I : ℕ → Term → Set
                P : Term → Set

            -- Pretend normalization exists 
            _⇒*_ : Term → Term → Set
            
            data ⟦_⟧_x_↓_ : Type → ℕ → (I : ℕ → Term → Set) → (P : Term → Set) → Set where
                I-Set : 
                    ⟦ Sett j ⟧ i x I ↓ I i

                I-Nat : 
                    -- What should m in suc m come from
                    ⟦ Nat ⟧ i x I ↓ λ x → (x ⇒* z) ⊎ (x ⇒* s {!   !}) 

                I-List : 
                    ⟦ A ⟧ i x I ↓ P → 
                    ⟦ List A ⟧ i x I ↓ λ xs → (xs ⇒* nill) ⊎ Σ[ x ∈ Term ] {!   !}


                I-Pi : 
                    ⟦ A ⟧ i x I ↓ P → 
                    (F : Term → (Term → Set) → (Term → Set)) →
                    (∀ (a : Term) → (pa : P a)  → ⟦ B [ 0 / a ] ⟧ i x I ↓ F a P) →
                    -- what to do with erasure 
                    ⟦ ∶ (A 𝕢 {!   !}) ⟶ B ⟧ i x I ↓ λ b → {!   !}

        -- https://davidchristiansen.dk/tutorials/implementing-types-hs.pdf
        data Value : Set
            
        -- data Env : Context Γ → Set where
        --     [] : Env [] 
        --     -- just make skip?
        --     _,v𝟘_ : (ρ : Env cΓ) → ⊤ → Env (cΓ , A 𝕢 𝟘)
        --     _,vω_ : (ρ : Env cΓ) → Value → Env (cΓ , A 𝕢 ω)
        Env = AgdaList.List Value

        -- Closure : {cΓ : Context Γ} → Set
        -- Closure {cΓ = cΓ} = (Env cΓ) × Term 
        Closure = Env × Term
        data Neutral : Set

        data Value where 
            ---- Functions
            VPi : Value → Closure → Value 
            VLam : Closure → Value 
            ---- Nats
            VNat : Value
            VZero : Value
            VSuc : Value → Value
            ---- Lists
            VList : Value → Value
            VNill : Value
            VConsl : Value → Value  
            ---- Vecs 
            VVec : Value → Value → Value 
            -- annotate type?
            VNilv : Value 
            VConsv : Value → Value → Value → Value 
            VSet : ℕ → Value
            VNeutral : Value → Neutral → Value 

        data Neutral where
            NVar : ℕ → Neutral
            NApp : Neutral → Term → Neutral
            -- include scrutinee?
            -- Can scrutinee be neutral?
            NElimNat : Neutral → Term → Term → Term → Neutral
            -- include type annotations?
            NElimList : Neutral → (innerty : Type) → (P : Term) → (nilB : Term) → (∷B : Term) → Neutral
            NElimVec : Neutral → (innerty : Type) → (P : Term) → (nilB : Term) → (∷B : Term) → Neutral
        
        ⟦_⟧_＝_ : Env → Term → Value → Set 

        -- only defined for some cases, make this relation?
        eval : Env → Term → Value
        -- uncertain how to make this total 
        eval ρ (var x) = {!   !}
        eval ρ (ƛ𝟘∶ A ♭ t) = {!   !}
        eval ρ (ƛω∶ A ♭ t) = {!   !}
        eval ρ (ƛr∶ A ♭ t) = VLam ⟨ eval ρ A ∷ ρ , t ⟩
        eval ρ (t · t₁ 𝕢 x) = {!   !}
        eval ρ (t ·ᵣ t₁) = {!   !}
        eval ρ z = {!   !}
        eval ρ (s t) = {!   !}
        eval ρ nill = {!   !}
        eval ρ (t ∷l t₁) = {!   !}
        eval ρ (nilv𝕢 x) = {!   !}
        eval ρ (t ∷v t₁ 𝕟 t₂ 𝕢 x) = {!   !}
        eval ρ (elimnat t P∶ t₁ zb∶ t₂ sb∶ t₃) = {!   !}
        eval ρ (eliml t ty∶ innerty P∶ t₁ nb∶ t₂ cb∶ t₃) = {!   !}
        eval ρ (elimv x ty∶ innerty P∶ t nb∶ t₁ cb∶ t₂) = {!   !}
        eval ρ Nat = {!   !}
        eval ρ (List x) = {!   !}
        eval ρ (Vec x x₁) = {!   !}
        eval ρ (∶ x ⟶ x₁) = {!   !}
        eval ρ (r∶ x ⟶ x₁) = {!   !}
        eval ρ (Sett x) = {!   !}

    
    module NBEDyb where
        -- https://phdopen.mimuw.edu.pl/zima07/dybjer.pdf

        -- separate out type from term?
        TypeF = ℕ → Type 
        TermF = ℕ → Term

        data ValTe : Set where 
            -- why type and not ValTy?
            LamD : Type → (ValTe → ValTe) 
            ZeroD : ValTe 
            SucD : ValTe → ValTe

            
        data ValTy : Set where
            FunD : ValTy → (ValTe → ValTy) → ValTy -- function types
            NatD : ValTy -- normal nat type 
            SetD : ℕ → ValTy -- normal universe type 
            ListD : ValTy → ValTy -- normal list type? 
            VecD : ValTy → ValTe → ValTy -- Normal vecs?
            NeutD : TypeF → ValTy -- neutral type family (?)


    Value : Type → Set 
    -- uncertain how to deal with this
    Value A = {!   !}

      
    data Env : Context Γ → Set
    ⟦_⟧ty : Term → Env cΓ → Set
    ⟦_∶_⟧te : (t : Term) → (A : Type) → (ρ : Env cΓ) → ⟦ A ⟧ty ρ 
    ⟦_⟧ : cΓ ⊢ a 𝕢 {!   !} ∶ A → Set

    data Env where
        []v : Env [] 
        -- just make skip?
        _,v𝟘_ : (ρ : Env cΓ) → ⊤ → Env (cΓ , A 𝕢 𝟘)
        _,vω_ : (ρ : Env cΓ) → ⟦ A ⟧ty ρ → Env  (cΓ , A 𝕢 ω)

    -- Env [] = ⊤
    -- -- Just accept empty types? Reject them? 
    -- Env (cΓ , A 𝕢 𝟘) = Σ[ ρ ∈ Env cΓ ] ⊤
    -- Env (cΓ , A 𝕢 ω) = Σ[ ρ ∈ Env cΓ ] ⟦ A ⟧ty ρ

    lookupTy : ℕ → Env cΓ → Set

    ⟦ var x ⟧ty ρ = lookupTy x ρ
    ⟦ Nat ⟧ty ρ = ℕ
    ⟦ List A ⟧ty ρ = AgdaList.List (⟦ A ⟧ty ρ)
    ⟦ Vec𝟘 A _ ⟧ty ρ = AgdaList.List (⟦ A ⟧ty ρ)
    -- stuck bc need ℕ not set
    ⟦ Vecω A n ⟧ty ρ = AgdaVec.Vec (⟦ A ⟧ty ρ) (⟦ n ∶ Nat ⟧te ρ)
    -- reduce like pi0?
    ⟦ ∶ A 𝕢 𝟘 ⟶ B ⟧ty ρ = {!   !}
    ---- break strict positivity?
    ⟦ ∶ A 𝕢 ω ⟶ B ⟧ty ρ = (a : ⟦ A ⟧ty ρ) → ⟦ B ⟧ty (ρ ,vω a)
    -- Change to identity like rule?
    ⟦_⟧ty {cΓ = cΓ} (r∶ A ⟶ B) ρ = (a : ⟦ A ⟧ty ρ) → ⟦ B ⟧ty (ρ ,vω a)
    -- need set levels
    ⟦ Sett n ⟧ty ρ = {!  Set ? !}
    ---- Terms in type positions
    ⟦ ƛ∶ x ♭ t ⟧ty ρ = {!   !}
    ⟦ ƛr∶ x ♭ t ⟧ty ρ = {!   !}
    ⟦ t · t₁ 𝕢 x ⟧ty ρ = {!   !}
    ⟦ t ·ᵣ t₁ ⟧ty ρ = {!   !}
    ⟦ z ⟧ty ρ = {!   !}
    ⟦ s t ⟧ty ρ = {!   !}
    ⟦ nill ⟧ty ρ = {!   !}
    ⟦ t ∷l t₁ ⟧ty ρ = {!   !}
    ⟦ nilv𝕢 x ⟧ty ρ = {!   !}
    ⟦ t ∷v t₁ 𝕟 t₂ 𝕢 x ⟧ty ρ = {!   !}
    ⟦ elimnat t P∶ t₁ zb∶ t₂ sb∶ t₃ ⟧ty ρ = {!   !}
    ⟦ eliml t ty∶ innerty P∶ t₁ nb∶ t₂ cb∶ t₃ ⟧ty ρ = {!   !}
    ⟦ elimv x ty∶ innerty P∶ t nb∶ t₁ cb∶ t₂ ⟧ty ρ = {!   !}

    lookupTe : ℕ → Env cΓ → {!   !}

module CtxEquiv where

    -- Maybe will just produce Nat terms 
    --  indexed by Typing context and type of hole
    -- Maybe keep track of target type
    TermCtx : Context Γ → Type → Set

    -- Maybe context can take two types A ~r B 
    -- But ~r would be baked into it...
    -- Would perhaps use ~r to select which eliminator to use....
    TermCtx2 : Context Γ → Type → Set


    -- Plugs hole with a term, check type?
    _[_] : 
        TermCtx cΓ A →
        -- index on well typed terms?
        Term → 
        Term

    _⊢_＝ctx_∶_,_ : Context Γ → Term → Term → Type → Type → Set
    cΓ ⊢ a ＝ctx b ∶ A , B = 
        (CtxA : TermCtx cΓ A) →
        (CtxB : TermCtx cΓ B) →
        {!   !} →
        {!   !}

    sound : 
        cΓ ⊢ a 𝕢 ω ∶ A →
        cΓ ⊢ b 𝕢 ω ∶ B →
        A ~ᵣ B →
        a ~ᵣ b → 
        {!   !}

module Erasure where 
    -- Erase terms? 
    -- Isnt this just... compiler?
    -- Wont this just... sanctify the previous relation?
    -- Could be a relation to sanctify erasing terms, could take well typed terms only
    ⟦_⟧ty : Term → Term
    ⟦ nilv𝟘 ⟧ty = nill
    ⟦ a ∷v as 𝕟𝟘 n ⟧ty = a ∷l as
    ⟦ var x ⟧ty = {!   !}
    ⟦ ƛ∶ A 𝕢 σ ♭ a ⟧ty = {!   !}
    ⟦ ƛr∶ x ♭ a ⟧ty = {!   !}
    ⟦ a · a₁ 𝕢 x ⟧ty = {!   !}
    ⟦ a ·ᵣ a₁ ⟧ty = {!   !}
    ⟦ z ⟧ty = {!   !}
    ⟦ s a ⟧ty = {!   !}
    ⟦ nill ⟧ty = {!   !}
    ⟦ a ∷l a₁ ⟧ty = {!   !}
    ⟦ nilv𝕢 x ⟧ty = {!   !}
    ⟦ a ∷v a₁ 𝕟 a₂ 𝕢 x ⟧ty = {!   !}
    ⟦ elimnat a P∶ a₁ zb∶ a₂ sb∶ a₃ ⟧ty = {!   !}
    ⟦ eliml a ty∶ innerty P∶ a₁ nb∶ a₂ cb∶ a₃ ⟧ty = {!   !}
    ⟦ elimv x ty∶ innerty P∶ a nb∶ a₁ cb∶ a₂ ⟧ty = {!   !}
    ⟦ Nat ⟧ty = {!   !}
    ⟦ List x ⟧ty = {!   !}
    ⟦ Vec x x₁ ⟧ty = {!   !}
    ⟦ ∶ x ⟶ x₁ ⟧ty = {!   !}
    ⟦ r∶ x ⟶ x₁ ⟧ty = {!   !}
    ⟦ Sett x ⟧ty = {!   !}  

