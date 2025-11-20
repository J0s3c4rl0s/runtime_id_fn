module Semantics where

open import Data.Nat
open import Data.Maybe 

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Language

data Value : Set

Env = ℕ → Maybe Value

data Value where 
    FunClos : Term → Env → Value
    NatClos : Term → Term → Env → Value
    Num : ℕ → Value

    SetTy : ℕ → Value
    -- Second argument to FunTy should only be a function ie FunClos...
    FunTy : Value → Value → Value
    NatTy : Value


extend : Env → Value → Env
extend γ v zero = just v
extend γ v (suc x) = extend γ v x

weaken : Env → Env
weaken γ zero = nothing
weaken γ (suc x) = (γ x)

private variable
    a a' b c d m p f g A B C F : Value
    Aₜ Bₜ Cₜ Dₜ : Type
    aₜ bₜ cₜ fₜ Pₜ : Term
    γ γ' : Env

    n i j : ℕ

data _app_↓_ : Value → Value → Value → Set

data ⟦_⟧_↓_ : Term → Env → Value → Set where
    ------ Terms
    ---- Vars 
    evalVar : 
        γ i ≡ just a → 
        ⟦ (var i) ⟧ γ ↓ a
    ---- Functions
    evalLam :
        ⟦ ƛω∶ Aₜ ♭ bₜ ⟧ γ ↓ FunClos bₜ γ 
    evalApp : 
        ⟦ fₜ ⟧ γ ↓ FunClos bₜ γ → 
        ⟦ aₜ ⟧ γ ↓ a →
        FunClos bₜ γ app a ↓ c → 
        ⟦ (fₜ ·ω aₜ) ⟧ γ ↓ c
    -- Erased functions
    evalLam0 :
        ⟦ bₜ ⟧ weaken γ ↓ b → 
        ⟦ ƛ𝟘∶ Aₜ ♭ bₜ ⟧ γ ↓ b 
    evalApp0 : 
        ⟦ fₜ ⟧ γ ↓ c → 
        ⟦ (fₜ ·𝟘 aₜ) ⟧ γ ↓ c
    -- runid functions
    evalLamR : 
        ⟦ ƛr∶ Aₜ ♭ bₜ ⟧ γ ↓ FunClos bₜ γ 
    evalAppR : 
        ⟦ fₜ ⟧ γ ↓ FunClos bₜ γ → 
        ⟦ aₜ ⟧ γ ↓ a →
        FunClos bₜ γ app a ↓ c → 
        ⟦ (fₜ ·ᵣ aₜ) ⟧ γ ↓ c
    
    ---- Nats 
    evalZ :  
        ⟦ z ⟧ γ ↓ Num 0
    evalS : 
        ⟦ aₜ ⟧ γ ↓ Num n → 
        ⟦ s aₜ ⟧ γ ↓ Num (suc n) 
    -- Either Nats produce functions (give a closure) or they compute already
    evalElNat : 
        ⟦ elNat Pₜ bₜ cₜ ⟧ γ ↓ NatClos bₜ cₜ γ
    evalElNatR :
        ⟦ elᵣNat Pₜ bₜ cₜ ⟧ γ ↓ NatClos bₜ cₜ γ

    ------ Types 
    evalNat : 
        ⟦ Nat ⟧ γ ↓ NatTy
    evalFunTy : 
        ⟦ Aₜ ⟧ γ ↓ A → 
        ⟦ (Aₜ 𝕢 ω) ⟶ Bₜ ⟧ γ ↓ (FunTy A (FunClos Bₜ γ))
    evalFunTyE : 
        ⟦ Bₜ ⟧ (weaken γ) ↓ C → 
        ⟦ (Aₜ 𝕢 𝟘) ⟶ Bₜ ⟧ γ ↓ C 
    evalSetTy : 
        ⟦ (Sett i) ⟧ γ ↓ SetTy i

data _app_↓_ where 
    appFun : 
        ⟦ bₜ ⟧ (extend γ a) ↓ c →
        FunClos bₜ γ app a ↓ c 
    
    appNatZ : 
        ⟦ bₜ ⟧ γ ↓ b → 
        (NatClos bₜ cₜ γ) app Num 0 ↓ b
    appNatS : 
        (NatClos bₜ cₜ γ) app (Num n) ↓ p →
        ⟦ cₜ ⟧ extend (extend γ (Num n)) p ↓ d → 
        (NatClos bₜ cₜ γ) app Num (suc n) ↓ d 

data SemTy : Set where 
    SemNat : SemTy
    SemFun : 
        SemTy →
        (Value → SemTy) → 
        SemTy
    SemSet : 
        ℕ → 
        SemTy

open import Data.Unit
open import Data.Empty
open import Data.Product renaming (_,_ to _,p_)

private variable
    𝓐 𝓑 : SemTy

[_]⇒_ : Value → SemTy → Set
[ NatTy ]⇒ SemNat = ⊤
[ FunTy A F ]⇒ SemFun 𝓐 𝓕 = 
    ([ A ]⇒ 𝓐) × 
        (∀ {a C} → 
            F app a ↓ C → 
            [ C ]⇒ 𝓕 a)
[ SetTy i ]⇒ SemSet x = i ≡ x
[ _ ]⇒ _ = ⊥


{-# TERMINATING #-}
_≅_∶_ : Value → Value → SemTy → Set 
Num n ≅ Num m ∶ SemNat = n ≡ m
Num _ ≅ _ ∶ _ = ⊥
-- _ ≅ Num _ ∶ _ = ⊥
f ≅ f' ∶ SemFun 𝓐 𝓕 =
    -- Add condition somewhere that F is "well formed?" 
    ∀  {a a' c c'} → 
        a ≅ a' ∶ 𝓐 → 
        f app a ↓ c → 
        f' app a' ↓ c' → 
        c ≅ c' ∶ 𝓕 a
NatTy ≅ NatTy ∶ SemSet l = ⊤ 
NatTy ≅ _ ∶ _ = ⊥
-- _ ≅ NatTy ∶ _ = ⊥  
FunTy A F ≅ FunTy A' F' ∶ SemSet l = 
    (A ≅ A' ∶ SemSet l) × 
        (∀ {a a' C C' 𝓐} →
            [ A ]⇒ 𝓐 → 
            a ≅ a' ∶ 𝓐 → 
            F app a ↓ C → 
            F' app a' ↓ C' → 
            C ≅ C' ∶ SemSet l) 
SetTy i ≅ SetTy j ∶ SemSet l = 
    (i ≡ j) × (i < l) 
_ ≅ _ ∶ _ = ⊥

≅sym : 
    a ≅ b ∶ 𝓐 → 
    b ≅ a ∶ 𝓐 

≅trans : 
    a ≅ b ∶ 𝓐 → 
    b ≅ c ∶ 𝓐 → 
    a ≅ c ∶ 𝓐 

⟦_⟧T_↓_ : Type → Env → SemTy → Set
⟦ Aₜ ⟧T γ ↓ 𝓐 = 
    Σ[ A ∈ Value ] ((⟦ Aₜ ⟧ γ ↓ A) × ([ A ]⇒ 𝓐))
    -- ∀ {A} →
    -- ⟦ Aₜ ⟧ γ ↓ A →
    -- [ A ]⇒ 𝓐

private variable
    Γ : Context

∅env : Env
∅env x = nothing

data _≅_∶⟦C_⟧ : Env → Env → Context → Set where
    ∅ : ∅env ≅ ∅env ∶⟦C [] ⟧

    skip : 
        γ ≅ γ' ∶⟦C Γ ⟧ → 
        weaken γ ≅ weaken γ' ∶⟦C (Γ , (Aₜ 𝕢 𝟘)) ⟧

    present : 
        γ ≅ γ' ∶⟦C Γ ⟧ →
        ⟦ Aₜ ⟧T γ ↓ 𝓐 → 
        a ≅ a' ∶ 𝓐 → 
        extend γ a ≅ extend γ' a' ∶⟦C Γ , (Aₜ 𝕢 ω) ⟧

≅Csym : 
    γ ≅ γ' ∶⟦C Γ ⟧ → 
    γ' ≅ γ ∶⟦C Γ ⟧

proof : 
    Γ ⊢ (aₜ 𝕢 ω) ∶ Aₜ → 
    ⟦ Aₜ ⟧T γ ↓ 𝓐 → 
    aₜ ~ᵣ bₜ → 
    γ ≅ γ' ∶⟦C Γ ⟧ →
    ⟦ aₜ ⟧ γ ↓ a →
    ⟦ bₜ ⟧ γ' ↓ b → 
    a ≅ b ∶ 𝓐


extLemma : ∀ {𝓕} →
    -- Functions are related
    f ≅ g ∶ SemFun 𝓐 𝓕 →
    -- inputs are related
    a ≅ a' ∶ 𝓐 →
    -- outputs are related
    f app a ↓ c → 
    g app a' ↓ d → 
    c ≅ d ∶ (𝓕 a)


weakenLemma : 
    ⟦ aₜ ⟧ γ ↓ a →
    ⟦ (aₜ ↑ 1 ≥ 0) ⟧ (weaken γ) ↓ a 


lemma : {a a' : Value} {C : Value} {C' : Value} {𝓐 : SemTy} →
    Bₜ ~ᵣ Dₜ →
    γ ≅ γ' ∶⟦C Γ ⟧ →
    ⟦ Aₜ ⟧ γ ↓ A  →
    [ A ]⇒ 𝓐 →
    a ≅ a' ∶ 𝓐 →
    FunClos Bₜ γ app a ↓ C →
    FunClos Dₜ γ' app a' ↓ C' → 
    C ≅ C' ∶ SemSet i
lemma {C = C} ~ γ≅ A↓ [A] a≅ (appFun evB) (appFun evD) =  
    -- Missing proof that Aₜ evals to 𝓐
    proof {!   !} {!   !} ~ (present γ≅ (_ ,p A↓ ,p [A]) a≅) evB evD

proof ⊢a 𝓐↓ ~ᵣrefl γ≅ a↓ b↓ = {!   !}
proof ⊢a 𝓐↓ (~ᵣsym ~) γ≅ a↓ b↓ = {!   !}
proof ⊢a 𝓐↓ (~ᵣtrans ~ ~₁) γ≅ a↓ b↓ = {!   !}
proof {𝓐 = SemFun 𝓐 𝓕} {a = FunClos b γᵢ} {b = FunClos b' γᵢ'} (⊢lam ⊢a ⊢a₁) (FunTy A (FunClos B γᵢ) ,p evalFunTy fst ,p [A] ,p snd) (~ᵣlamω ~) γ≅ evalLam evalLam a≅ (appFun b↓) (appFun b'↓) =  
    -- Uncertain how to prove that ⟦ B ⟧T extend γᵢ a ↓ 𝓕 a
    proof ⊢a ({!   !} ,p ({!   !} ,p {!   !})) ~ (present γ≅ (A ,p (fst ,p [A])) a≅) b↓ b'↓
proof (⊢lam ⊢a ⊢A) (fst ,p evalFunTyE B↓ ,p snd) (~ᵣlam𝟘 {b = bₜ} ~) γ≅ (evalLam0 a↓) b↓ = proof ⊢a (fst ,p B↓ ,p snd) ~ (skip γ≅) a↓ (weakenLemma b↓)
proof ⊢a 𝓐↓ ~ᵣlamr γ≅ a↓ b↓ = {!   !}
proof {𝓐 = SemNat} {a = Num (suc n)} {Num (suc m)} (⊢s ⊢a) (NatTy ,p fst ,p snd) (~ᵣs ~) γ≅ (evalS a↓) (evalS b↓) = 
    cong suc (proof ⊢a (NatTy ,p fst ,p snd) ~ γ≅ a↓ b↓)
proof {𝓐 = 𝓐} {a = a} {b = b} (⊢app {a = fₜ} {b = aₜ} ⊢f ⊢a) (A' ,p fst ,p snd) (~ᵣappω {d = gₜ} {c = cₜ} ~ ~₁) γ≅ (evalApp f↓ a↓ appF) (evalApp g↓ c↓ appG) = {!   !} -- extLemma f≅g a≅c appF appG
    where 
        -- Cant specify the derivation proof for the types 
        f≅g = proof ⊢f ({!   !} ,p evalFunTy {!   !} ,p {!   !} ,p {!   !})  ~ γ≅ f↓ g↓
        a≅c = proof ⊢a ({!   !} ,p ({!    !} ,p {!   !})) ~₁ γ≅ a↓ c↓
proof ⊢a 𝓐↓ (~ᵣapp𝟘 ~) γ≅ a↓ b↓ = {!   !}
proof (⊢appᵣ ⊢a ⊢a₁) (fst ,p fst₁ ,p snd) (~ᵣappr ~) γ≅ (evalAppR a↓ a↓₁ x) b↓ = {!   !}
-- proof {a = a} {b} {𝓐} ~ᵣrefl γ≅ a↓ b↓ = {!   !}
-- proof {a = a} {b} {𝓐} (~ᵣsym ~) γ≅ a↓ b↓ = ≅sym (proof ~ (≅Csym γ≅) b↓ a↓)
-- -- Missing intermediate value derivation
-- proof (~ᵣtrans {B = cₜ} ~ ~₁) γ≅ a↓ b↓ = ≅trans (proof ~ γ≅ a↓ {!   !}) (proof ~₁ γ≅ {!   !} b↓)
-- -- How contradiction here? Only problem is with type, need some (semantic) typing judgement
-- proof {a = FunTy A F} {b = FunTy B G} {𝓐 = SemNat} {d} (~ᵣpiω ~ ~₁) γ≅ a↓ b↓ = {!   !}
-- proof {a = FunTy A F} {FunTy B G} {SemFun 𝓐 𝓕} (~ᵣpiω ~ ~₁) γ≅ a↓ b↓ a≅ ()
-- proof {a = FunTy A (FunClos B₁ γ)} {FunTy B (FunClos D γ')} {SemSet x} (~ᵣpiω ~ ~₁) γ≅ (evalFunTy a↓) (evalFunTy b↓) = 
--     (proof ~ γ≅ a↓ b↓) ,p 
--         lemma ~₁ γ≅ a↓
-- proof {a = FunClos fₜ γᵢ} {FunClos gₜ γᵢ'} {SemFun 𝓐 x} (~ᵣlamω ~) γ≅ evalLam evalLam a≅ (appFun x₁) (appFun x₂) = 
--     -- How to prove that type annotation matches semantic type?
--     proof ~ (present γ≅ {!   !} a≅) x₁ x₂
-- proof {a = FunClos x x₁} {FunClos x₂ x₃} {SemNat} (~ᵣlamω ~) γ≅ a↓ b↓ = {!   !}
-- proof {a = FunClos x₁ x₂} {b} {SemSet x} (~ᵣlamω ~) γ≅ a↓ b↓ = {!   !}
-- proof {a = a} {b} {𝓐} (~ᵣlam𝟘 ~) γ≅ a↓ b↓ = {!   !}
-- proof {a = a} {b} {𝓐} ~ᵣlamr γ≅ a↓ b↓ = {!   !}
-- proof {a = a} {b} {𝓐} (~ᵣs ~) γ≅ a↓ b↓ = {!   !}
-- proof {a = a} {b} {𝓐} (~ᵣappω ~ ~₁) γ≅ a↓ b↓ = {!   !}
-- proof {a = a} {b} {𝓐} (~ᵣapp𝟘 ~) γ≅ a↓ b↓ = {!   !}
-- proof {a = a} {b} {𝓐} (~ᵣappr ~) γ≅ a↓ b↓ = {!   !}
-- proof {a = a} {b} {𝓐} ~ᵣelℕᵣ γ≅ a↓ b↓ = {!   !}

