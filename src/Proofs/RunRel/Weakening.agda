module Proofs.RunRel.Weakening where

import RunId as S
import STLC as T
open import RunIdComp
open import Proofs.Relations

open S using (
    𝟘; ω;
    _𝕢_;
    _~ᵣ_;
    _↑_≥_)

open import Data.Bool hiding (_≤_; _≤?_; _<_)

open import Data.Nat
open import Data.Nat.Properties hiding (≤⇒≤ᵇ)
open import Data.Maybe
open import Data.Unit
open import Data.Empty

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

private variable
    A B : Set

    Γₛ : S.PreContext
    cΓₛ : S.Context Γₛ
    Aₛ Bₛ Cₛ : S.Type
    aₛ bₛ cₛ asₛ bsₛ fₛ : S.Term
    σ π ρ : S.Quantity

    i l j k x : ℕ

    rΓ rΓ' : ContextRemap cΓₛ

    Aₜ Bₜ Cₜ : T.Type
    aₜ bₜ cₜ : T.Term

if-injective :
    (cond : Bool) →
    (cons : A → B) →
    (x₁ x₂ : A) →
    (if cond then cons x₁ else cons x₂) 
        ≡ 
    cons (if cond then x₁ else x₂)
if-injective  Bool.false _ _ _ = refl
if-injective  Bool.true _ _ _ = refl

≤b-injective : (suc i ≤ᵇ suc j) ≡ (i ≤ᵇ j)
≤b-injective {zero} {j} = refl
≤b-injective {suc i} {j} = refl

,ᵣskip-injective₁ : ∀ {cΓₛ : S.Context Γₛ} {rΓ rΓ↑ : ContextRemap cΓₛ} →
    just (rΓ ,ᵣ Aₛ skip) ≡ just (rΓ↑ ,ᵣ Aₛ skip) →
    rΓ ≡ rΓ↑
,ᵣskip-injective₁ refl = refl

,ᵣass-injective₁ : ∀ {cΓₛ : S.Context Γₛ} {rΓ rΓ↑ : ContextRemap cΓₛ} →
    just (rΓ ,ᵣ Aₛ ↦ Aₜ) ≡ just (rΓ↑ ,ᵣ Aₛ  ↦ Bₜ) →
    rΓ ≡ rΓ↑
,ᵣass-injective₁ refl = refl

-- ,ᵣass-injective₂ : ∀ {cΓₛ : S.Context Γₛ} {rΓ rΓ↑ : ContextRemap cΓₛ} →
--     just (rΓ ,ᵣ Aₛ ↦ Aₜ) ≡ just (rΓ↑ ,ᵣ Aₛ  ↦ Bₜ) →
--     Aₜ ≡ Bₜ

≤⇒¬> : 
    i ≤ j → 
    ¬ (i > j)
≤⇒¬> (s≤s i≤j) (s≤s i>j) = ≤⇒¬> i≤j i>j

invertRemapSkip : 
    (compileRemap cΓₛ >>= (λ rΓ₁ → just (rΓ₁ ,ᵣ Aₛ skip))) ≡ just (rΓ ,ᵣ Aₛ skip) →
    compileRemap cΓₛ ≡ just rΓ
invertRemapSkip {cΓₛ = S.[]} refl = refl
invertRemapSkip {cΓₛ = cΓₛ S., A 𝕢 𝟘} {rΓ = rΓ ,ᵣ .A skip} bindComps with compileRemap cΓₛ
... | just rΓ' 
        rewrite ,ᵣskip-injective₁ bindComps = refl
invertRemapSkip {cΓₛ = cΓₛ S., A 𝕢 ω} {rΓ = rΓ ,ᵣ .A ↦ Aₜ} bindComps with compileRemap cΓₛ | compileType A
... | just rΓ' | just Aₜ'
        rewrite ,ᵣskip-injective₁ bindComps = refl

invertRemapAss₁ :     
    (compileRemap cΓₛ >>= (λ rΓ₁ → compileType Aₛ >>= (λ Aₜ → just (rΓ₁ ,ᵣ Aₛ ↦ Aₜ)))) 
        ≡ 
    just (rΓ ,ᵣ Aₛ ↦ Aₜ) →
    compileRemap cΓₛ ≡ just rΓ
invertRemapAss₁ {cΓₛ = S.[]} {rΓ = []ᵣ} bindComps = refl
invertRemapAss₁ {cΓₛ = cΓₛ S., A 𝕢 𝟘} {Aₛ} {rΓ = rΓ ,ᵣ .A skip} bindComps with compileRemap cΓₛ | compileType Aₛ
... | just rΓ' | just Aₜ'
        rewrite ,ᵣass-injective₁ bindComps = refl
invertRemapAss₁ {cΓₛ = cΓₛ S., A 𝕢 ω} {Aₛ} {rΓ = rΓ ,ᵣ .A ↦ Aₜ} bindComps with compileRemap cΓₛ | compileType A | compileType Aₛ
... | just rΓ' | just Aₜ' | just _ 
        rewrite ,ᵣass-injective₁ bindComps = refl


-- Could avoid inversion business if I just with abstract the recursive compilation?
lemmaRemap : ∀ {p} {rΓ : ContextRemap cΓₛ} {rΓ↑ : ContextRemap (S.insertType cΓₛ i p Bₛ 𝟘)} →
    (x : ℕ) →
    compileRemap cΓₛ ≡ just rΓ →
    compileRemap (S.insertType cΓₛ i p Bₛ 𝟘) ≡ just rΓ↑ →
    remapIndex x rΓ ≡ remapIndex (if i ≤ᵇ x then (x + 1) else x) rΓ↑
lemmaRemap {cΓₛ = _} {i = zero} {p = z≤n} {rΓ↑ = rΓ↑ ,ᵣ Aₛ skip} x cΓₛComps cΓₛ↑Comps
    rewrite cΓₛComps | ,ᵣskip-injective₁ cΓₛ↑Comps | +-comm x 1 = refl 
lemmaRemap 
    {cΓₛ = cΓₛ S., A 𝕢 𝟘} {i = suc i} {p = s≤s p} {rΓ ,ᵣ .A skip} {rΓ↑ ,ᵣ .(A ↑ 1 ≥ i) skip} 
    zero cΓₛComps cΓₛ↑Comps = refl
lemmaRemap 
    {cΓₛ = cΓₛ S., A 𝕢 ω} {i = suc i} {p = s≤s p} {rΓ ,ᵣ .A ↦ Aₜ} {rΓ↑ ,ᵣ .(A ↑ 1 ≥ i) ↦ Aₜ₁}
    zero cΓₛComps cΓₛ↑Comps = refl
lemmaRemap
    {cΓₛ = cΓₛ S., A 𝕢 𝟘} {i = suc i} {p = s≤s p} {rΓ ,ᵣ .A skip} {rΓ↑ ,ᵣ .(A ↑ 1 ≥ i) skip}
    (suc x) cΓₛComps cΓₛ↑Comps 
    rewrite ≤b-injective {i = i} {j = x} | if-injective (i ≤ᵇ x) suc (x + 1) x = 
        lemmaRemap x (invertRemapSkip cΓₛComps) (invertRemapSkip cΓₛ↑Comps)
lemmaRemap 
    {cΓₛ = cΓₛ S., A 𝕢 ω} {i = suc i} {p = s≤s p} {rΓ ,ᵣ .A ↦ Aₜ} {rΓ↑ ,ᵣ .(A ↑ 1 ≥ i) ↦ Aₜ₁}
    (suc x) cΓₛComps cΓₛ↑Comps
    rewrite ≤b-injective {i = i} {j = x} | if-injective (i ≤ᵇ x) suc (x + 1) x
        rewrite lemmaRemap x (invertRemapAss₁ cΓₛComps) (invertRemapAss₁ cΓₛ↑Comps) = refl

A↑MustCompile : 
    (Aₛ : S.Term) →
    (i : ℕ) → 
    (l : ℕ) →
    -- change this to other formulation?
    compileType Aₛ ≡ just Aₜ →
    ¬ (compileType (Aₛ ↑ i ≥ l) ≡ nothing)
A↑MustCompile S.Nat i l AComps = λ ()
A↑MustCompile (S.List Aₛ) i l ListComps _
    with compileType Aₛ in AComps | compileType (Aₛ ↑ i ≥ l) in A↑Comps
... | just Aₜ | nothing = A↑MustCompile Aₛ i l AComps A↑Comps
A↑MustCompile (S.Vec Aₛ (nₛ 𝕢 𝟘)) i l VecComps _
    with compileType Aₛ in AComps | compileType (Aₛ ↑ i ≥ l) in A↑Comps
... | just Aₜ | nothing = A↑MustCompile Aₛ i l AComps A↑Comps 
A↑MustCompile (S.Vec Aₛ (nₛ 𝕢 ω)) i l VecComps _
    with compileType Aₛ in AComps | compileType (Aₛ ↑ i ≥ l) in A↑Comps
... | just Aₜ | nothing = A↑MustCompile Aₛ i l AComps A↑Comps
A↑MustCompile (S.∶ Aₛ 𝕢 𝟘 ⟶ Bₛ) i l AComps = 
    A↑MustCompile Bₛ i (suc l) AComps
A↑MustCompile (S.∶ Aₛ 𝕢 ω ⟶ Bₛ) i l FunComps _
-- Either A or B fails (which neither of them can)
    with compileType Aₛ in AComps | compileType (Aₛ ↑ i ≥ l) in A↑Comps
... | just _ | nothing = A↑MustCompile Aₛ i l AComps A↑Comps
... | just _ | just _
        with compileType Bₛ in BComps | compileType (Bₛ ↑ i ≥ (suc l)) in B↑Comps
...     | just _ | nothing  = A↑MustCompile Bₛ i (suc l) BComps B↑Comps
A↑MustCompile (S.r∶ Aₛ ⟶ Bₛ) i l FunComps _
-- Either A or B fails (which neither of them can)
    with compileType Aₛ in AComps | compileType (Aₛ ↑ i ≥ l) in A↑Comps
... | just _ | nothing = A↑MustCompile Aₛ i l AComps A↑Comps
... | just _ | just _
        with compileType Bₛ in BComps | compileType (Bₛ ↑ i ≥ (suc l)) in B↑Comps
...     | just _ | nothing  = A↑MustCompile Bₛ i (suc l) BComps B↑Comps

rΓ↑MustCompile : ∀ {cΓₛ : S.Context Γₛ} {rΓ : ContextRemap cΓₛ} →
    (i : ℕ) → 
    (p : i ≤ S.conLen Γₛ) →
    (Bₛ : S.Type) →
    compileRemap cΓₛ ≡ just rΓ →
    ¬ (compileRemap (S.insertType cΓₛ i p Bₛ 𝟘) ≡ nothing)
rΓ↑MustCompile {cΓₛ = cΓₛ} zero z≤n Bₛ cΓComps cΓ↑DoesntComp 
    with compileRemap cΓₛ
rΓ↑MustCompile {cΓₛ = cΓₛ} zero z≤n Bₛ cΓComps () | just rΓ
rΓ↑MustCompile {cΓₛ = cΓₛ S., A 𝕢 𝟘} (suc i) (s≤s p) Bₛ cΓEComps cΓ↑DoesntComp 
    with compileRemap cΓₛ in cΓComps | compileRemap (S.insertType cΓₛ i p Bₛ 𝟘) in cΓ↑Comps
... | just _ | nothing = 
        rΓ↑MustCompile i p Bₛ cΓComps cΓ↑Comps
rΓ↑MustCompile {cΓₛ = cΓₛ S., Aₛ 𝕢 ω} (suc i) (s≤s p) Bₛ cΓEComps cΓ↑DoesntComp
    with compileRemap cΓₛ in cΓComps | compileType Aₛ in AComps
... | just _ | just _  
        with compileRemap (S.insertType cΓₛ i p Bₛ 𝟘) in cΓ↑Comps | compileType (Aₛ ↑ 1 ≥ i) in A↑Comps
...     | nothing | _ = rΓ↑MustCompile i p Bₛ cΓComps cΓ↑Comps
...     | just _ | nothing = A↑MustCompile Aₛ 1 i AComps A↑Comps

suci≤ᵇsucj⇒i≤ᵇj : ∀ {b} →
    (suc i ≤ᵇ suc j) ≡ b → 
    (i ≤ᵇ j) ≡ b
suci≤ᵇsucj⇒i≤ᵇj {zero} {_} suci≤ᵇsucj = suci≤ᵇsucj
suci≤ᵇsucj⇒i≤ᵇj {suc i} {_} suci≤ᵇsucj = suci≤ᵇsucj

i≤ᵇj⇒suci≤ᵇsucj : ∀ {b} → 
    (i ≤ᵇ j) ≡ b →
    (suc i ≤ᵇ suc j) ≡ b 
i≤ᵇj⇒suci≤ᵇsucj {zero} {j} i≤ᵇj = i≤ᵇj
i≤ᵇj⇒suci≤ᵇsucj {suc i} {j} i≤ᵇj = i≤ᵇj

my≤⇒≤ᵇTrue : 
    i ≤ j →
    (i ≤ᵇ j) ≡ true
my≤⇒≤ᵇTrue {zero} {_} i≤j = refl
my≤⇒≤ᵇTrue {suc i} {suc j} (s≤s i≤j) = i≤ᵇj⇒suci≤ᵇsucj {i} {j} (my≤⇒≤ᵇTrue {i} {j} i≤j)

my≤ᵇTrue⇒≤ : 
    (i ≤ᵇ j) ≡ true →
    i ≤ j 
my≤ᵇTrue⇒≤ {zero}  i≤ᵇj = z≤n
my≤ᵇTrue⇒≤ {suc i} {suc j} i≤ᵇj = 
    +-monoʳ-≤ 
        1 
        (my≤ᵇTrue⇒≤ {i} {j} (suci≤ᵇsucj⇒i≤ᵇj {i} {j} i≤ᵇj))

my≤ᵇFalse⇒> : 
    (i ≤ᵇ j) ≡ false →
    (i > j) 
my≤ᵇFalse⇒> {suc i} {zero} i≤ᵇj = s≤s z≤n
my≤ᵇFalse⇒> {suc i} {suc j} i≤ᵇj = 
    +-monoʳ-≤ 1  
        (my≤ᵇFalse⇒> {i = i} sub)
    where
        sub : (i ≤ᵇ j) ≡ false
        sub = suci≤ᵇsucj⇒i≤ᵇj {i = i} {j = j} i≤ᵇj

my>⇒≤ᵇFalse : 
    i > j →
    (i ≤ᵇ j) ≡ false    
my>⇒≤ᵇFalse {suc i} {zero} i>j = refl
my>⇒≤ᵇFalse {suc i} {suc j} (s≤s i>j) = 
        trans 
            (≤b-injective {i = i} {j = j}) 
            (my>⇒≤ᵇFalse i>j)


reduceIfFalse : ∀ {c l} {A : Set l} {a b : A} →
    c ≡ false →
    (if c then a else b) ≡ b
reduceIfFalse refl = refl 

reduceIfTrue : ∀ {c l} {A : Set l} {a b : A} →
    c ≡ true →
    (if c then a else b) ≡ a
reduceIfTrue refl = refl

2+-suc :
    (i : ℕ) →
    (j : ℕ) → 
    i + 2+ j ≡ 2+ (i + j)
2+-suc i j = 
    trans 
        (+-suc i (suc j)) 
        (cong suc (+-suc i j))

-- Maybe i l j k aₛ can be implied?
flipShift : 
    (aₛ : S.Term) →
    (i : ℕ) → (j : ℕ) → 
    (l : ℕ) → (k : ℕ) → 
    (outerLater : k ≥ j) →
    (aₛ ↑ i ≥ j) ↑ l ≥ (i + k)
        ≡ 
    ((aₛ ↑ l ≥ k) ↑ i ≥ j)
flipShift (S.var x) i j l k isOuter 
    with j ≤ᵇ x in j≤b | k ≤ᵇ x in k≤b  
... | false | false = 
        trans 
            (reduceIfFalse i+k≤xFalse)
            (sym (reduceIfFalse j≤b))
    where
        k>x : k > x
        k>x = my≤ᵇFalse⇒> k≤b
        i+k>x : (i + k) > x 
        i+k>x = 
            ≤-trans 
                k>x 
                (m≤n+m k i)
        i+k≤xFalse : (i + k ≤ᵇ x) ≡ false 
        i+k≤xFalse = my>⇒≤ᵇFalse i+k>x
... | false | true = 
        ⊥-elim (≤⇒¬> j≤x j>x)
        where
            j≤x = ≤-trans isOuter (my≤ᵇTrue⇒≤ k≤b)
            j>x = my≤ᵇFalse⇒> j≤b
... | true | false = 
        trans 
            (reduceIfFalse i+k≤x+iFalse) 
            (sym (reduceIfTrue j≤b))
        where
            k>x : k > x
            k>x = my≤ᵇFalse⇒> k≤b
            
            i+k>x+i : i + k > x + i
            i+k>x+i = subst (λ m → m > x + i) (+-comm k i) (+-monoˡ-< i k>x)
            
            i+k≤x+iFalse : (i + k ≤ᵇ x + i) ≡ false
            i+k≤x+iFalse = my>⇒≤ᵇFalse i+k>x+i
... | true | true = 
        trans 
            (reduceIfTrue i+k≤ᵇx+iTrue) 
            (sym (trans 
                (reduceIfTrue j≤ᵇx+lTrue) 
                (cong (λ m → S.var m) x+l+i≡x+i+l)))
        where
            i+k≤ᵇx+iTrue : (i + k ≤ᵇ x + i) ≡ true
            i+k≤ᵇx+iTrue = 
                my≤⇒≤ᵇTrue {i = i + k} {j = x + i} 
                    (subst (λ m → m ≤ x + i) (+-comm k i) (+-monoˡ-≤ i (my≤ᵇTrue⇒≤ k≤b)))
            
            j≤ᵇx+lTrue : (j ≤ᵇ x + l) ≡ true
            j≤ᵇx+lTrue = 
                my≤⇒≤ᵇTrue {i = j} {j = (x + l)}
                    (≤-trans (my≤ᵇTrue⇒≤ j≤b) (m≤m+n x l)) 
            
            x+l+i≡x+i+l : (x + l + i) ≡ (x + i + l) 
            x+l+i≡x+i+l = 
                trans 
                    (+-assoc x l i) 
                    (trans 
                        (cong (λ m → x + m) (+-comm l i)) 
                        (trans (sym (+-assoc x i l)) refl))
flipShift (S.ƛ∶ Aₛ 𝕢 σ ♭ aₛ) i j l k isOuter = 
    trans 
        (cong (λ x → S.ƛ∶ x 𝕢 σ ♭ aₗ) flipA) 
        (trans 
            (cong (λ x → S.ƛ∶ Aᵣ 𝕢 σ ♭ ((aₛ ↑ i ≥ suc j) ↑ l ≥ x)) (sym (+-suc i k))) 
            (cong (λ x → (S.ƛ∶ Aᵣ 𝕢 σ ♭ x)) flipa))
    where
        Aᵣ = ((Aₛ ↑ l ≥ k) ↑ i ≥ j)
        aₗ = (aₛ ↑ i ≥ suc j) ↑ l ≥ suc (i + k)
        flipA = flipShift Aₛ i j l k isOuter
        flipa = flipShift aₛ i (suc j) l (suc k) (s≤s isOuter)
flipShift (S.ƛr∶ Aₛ ♭ aₛ) i j l k isOuter = 
    trans 
        (cong (λ x → S.ƛr∶ x ♭ aₗ) flipA) 
        (trans 
            (cong (λ x → S.ƛr∶ Aᵣ ♭ ((aₛ ↑ i ≥ suc j) ↑ l ≥ x)) (sym (+-suc i k))) 
            (cong (λ x → S.ƛr∶ Aᵣ ♭ x) flipa))
    where
        Aᵣ = ((Aₛ ↑ l ≥ k) ↑ i ≥ j)
        aₗ = (aₛ ↑ i ≥ suc j) ↑ l ≥ suc (i + k)
        flipA = flipShift Aₛ i j l k isOuter
        flipa = flipShift aₛ i (suc j) l (suc k) (s≤s isOuter)
flipShift (fₛ S.· aₛ 𝕢 x) i j l k isOuter
    rewrite flipShift aₛ i j l k isOuter
        | flipShift fₛ i j l k isOuter = refl
flipShift (fₛ S.·ᵣ aₛ) i j l k isOuter
    rewrite flipShift aₛ i j l k isOuter
        | flipShift fₛ i j l k isOuter = refl
flipShift (S.s aₛ) i j l k isOuter 
    rewrite flipShift aₛ i j l k isOuter = refl
flipShift (aₛ S.∷l asₛ) i j l k isOuter 
    rewrite flipShift aₛ i j l k isOuter
        | flipShift asₛ i j l k isOuter = refl
flipShift (aₛ S.∷v asₛ 𝕟 nₛ 𝕢 x) i j l k isOuter
    rewrite flipShift aₛ i j l k isOuter
        | flipShift asₛ i j l k isOuter
        | flipShift nₛ i j l k isOuter = refl
flipShift (S.elimnat aₛ P∶ Pₛ zb∶ zₛ sb∶ sₛ) i j l k isOuter
    rewrite flipShift aₛ i j l k isOuter
        | sym (+-suc i k) | flipShift Pₛ i (suc j) l (suc k) (s≤s isOuter)
        | flipShift zₛ i j l k isOuter 
        | sym (+-suc i (suc k)) | flipShift sₛ i (2+ j) l (2+ k) (s≤s (s≤s isOuter)) = refl
flipShift (S.eliml aₛ ty∶ Aₛ P∶ Pₛ nb∶ []ₛ cb∶ ∷ₛ) i j l k isOuter
    rewrite flipShift aₛ i j l k isOuter 
        | flipShift Aₛ i j l k isOuter 
        | sym (+-suc i k) | flipShift Pₛ i (suc j) l (suc k) (s≤s isOuter)
        | flipShift []ₛ i j l k isOuter
        | sym (2+-suc i (suc k)) | flipShift ∷ₛ i (3 + j) l (3 + k) (s≤s (s≤s (s≤s isOuter))) = refl
flipShift (S.elimv aₛ 𝕢 σ ty∶ Aₛ P∶ Pₛ nb∶ []ₛ cb∶ ∷ₛ) i j l k isOuter
    rewrite flipShift aₛ i j l k isOuter 
        | flipShift Aₛ i j l k isOuter
        | sym (2+-suc i k) | flipShift Pₛ i (2+ j) l (2+ k) (s≤s (s≤s isOuter))
        | flipShift []ₛ i j l k isOuter
        | sym (2+-suc i (2+ k)) | flipShift ∷ₛ i (4 + j) l (4 + k) (s≤s (s≤s (s≤s (s≤s isOuter)))) = refl
flipShift (S.List Aₛ) i j l k isOuter = cong S.List (flipShift Aₛ i j l k isOuter)
flipShift (S.Vec Aₛ (nₛ 𝕢 σ)) i j l k isOuter
    rewrite flipShift Aₛ i j l k isOuter
        | flipShift nₛ i j l k isOuter = refl
flipShift (S.∶ Aₛ 𝕢 σ ⟶ Bₛ) i j l k isOuter
    rewrite flipShift Aₛ i j l k isOuter
        | sym (+-suc i k) | flipShift Bₛ i (suc j) l (suc k) (s≤s isOuter) = refl
flipShift (S.r∶ Aₛ ⟶ Bₛ) i j l k isOuter
    rewrite flipShift Aₛ i j l k isOuter
        | sym (+-suc i k) | flipShift Bₛ i (suc j) l (suc k) (s≤s isOuter) = refl
---- Base cases
flipShift S.nill i j l k isOuter = refl
flipShift (S.nilv𝕢 x) i j l k isOuter = refl
flipShift S.z i j l k isOuter = refl
flipShift S.Nat i j l k isOuter = refl
flipShift (S.Sett x) i j l k isOuter = refl


lemmaWeakenTerm : 
    (aₛ : S.Term) → 
    (cΓₛ : S.Context Γₛ) →
    (i : ℕ) → 
    (p : i ≤ S.conLen Γₛ) →
    (Bₛ : S.Type) →
    cΓₛ ⊢ aₛ ⇒ aₜ →
    (S.insertType cΓₛ i p Bₛ 𝟘)  ⊢ (aₛ ↑ 1 ≥ i) ⇒ aₜ
---- Var
lemmaWeakenTerm (S.var x) cΓₛ i p Bₛ lComps 
    rewrite if-injective (i ≤ᵇ x) S.var (x + 1) x with compileRemap cΓₛ in rΓComps | compileRemap (S.insertType cΓₛ i p Bₛ 𝟘) in rΓ↑Comps
... | just rΓ | just rΓ↑
    rewrite lemmaRemap x rΓComps rΓ↑Comps = lComps
-- prove absurd somehow
... | just rΓ | nothing = contradiction rΓ↑Comps (rΓ↑MustCompile i p Bₛ rΓComps)
-- Inductive cases
lemmaWeakenTerm {aₜ = aₜ} (S.ƛ∶ Aₛ 𝕢 𝟘 ♭ aₛ) cΓₛ i p Bₛ lComps with compileTerm (cΓₛ S., Aₛ 𝕢 𝟘) aₛ in aComps
lemmaWeakenTerm {aₜ = aₜ} (S.ƛ∶ Aₛ 𝕢 𝟘 ♭ aₛ) cΓₛ i p Bₛ refl | just .aₜ = 
    lemmaWeakenTerm aₛ (cΓₛ S., Aₛ 𝕢 𝟘) (suc i) (s≤s p) Bₛ aComps
lemmaWeakenTerm (S.ƛ∶ Aₛ 𝕢 ω ♭ aₛ) cΓₛ i p Bₛ lComps with compileTerm (cΓₛ S., Aₛ 𝕢 ω) aₛ in aComps
lemmaWeakenTerm (S.ƛ∶ Aₛ 𝕢 ω ♭ aₛ) cΓₛ i p Bₛ refl | just aₜ 
    rewrite lemmaWeakenTerm aₛ (cΓₛ S., Aₛ 𝕢 ω) (suc i) (s≤s p) Bₛ aComps = refl
lemmaWeakenTerm (S.ƛr∶ Aₛ ♭ aₛ) cΓₛ i p Bₛ lComps with compileTerm (cΓₛ S., Aₛ 𝕢 𝟘) aₛ
... | _ = lComps
lemmaWeakenTerm (fₛ S.· aₛ 𝕢 𝟘) cΓₛ i p Bₛ lComps = 
    lemmaWeakenTerm fₛ cΓₛ i p Bₛ lComps
lemmaWeakenTerm (fₛ S.· aₛ 𝕢 ω) cΓₛ i p Bₛ lComps with compileTerm cΓₛ fₛ in fComps |  compileTerm cΓₛ aₛ in aComps 
... | just fₜ | just aₜ
    rewrite lemmaWeakenTerm fₛ cΓₛ i p Bₛ fComps 
        |  lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps = lComps 
lemmaWeakenTerm (fₛ S.·ᵣ aₛ) cΓₛ i p Bₛ lComps = 
    lemmaWeakenTerm aₛ cΓₛ i p Bₛ lComps
lemmaWeakenTerm (S.s aₛ) cΓₛ i p Bₛ lComps with compileTerm cΓₛ aₛ in aComps
... | just aₜ 
        rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps = 
            lComps
lemmaWeakenTerm (aₛ S.∷l asₛ) cΓₛ i p Bₛ lComps 
    with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ asₛ in asComps
... | just aₜ | just asₜ
        rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps | lemmaWeakenTerm asₛ cΓₛ i p Bₛ asComps = 
            lComps
lemmaWeakenTerm (aₛ S.∷v asₛ 𝕟 nₛ 𝕢 𝟘) cΓₛ i p Bₛ lComps 
    with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ asₛ in asComps
... | just aₜ | just asₜ
        rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps | lemmaWeakenTerm asₛ cΓₛ i p Bₛ asComps = 
            lComps
lemmaWeakenTerm (aₛ S.∷v asₛ 𝕟 nₛ 𝕢 ω) cΓₛ i p Bₛ lComps
    with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ asₛ in asComps | compileTerm cΓₛ nₛ in nComps
... | just aₜ | just asₜ | just nₜ 
        rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps 
            | lemmaWeakenTerm asₛ cΓₛ i p Bₛ asComps
            | lemmaWeakenTerm nₛ cΓₛ i p Bₛ nComps  = 
                lComps
lemmaWeakenTerm (S.elimnat aₛ P∶ Pₛ zb∶ zₛ sb∶ sₛ) cΓₛ i p Bₛ lComps
    with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ zₛ in zComps | compileTerm (((cΓₛ S., S.Nat 𝕢 ω) S., Pₛ 𝕢 ω)) sₛ in sComps
... | just aₜ | just zₜ | just sₜ 
        rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps 
            | lemmaWeakenTerm zₛ cΓₛ i p Bₛ zComps
            | lemmaWeakenTerm sₛ (((cΓₛ S., S.Nat 𝕢 ω) S., Pₛ 𝕢 ω)) (2+ i) (s≤s (s≤s p)) Bₛ sComps = 
               lComps
lemmaWeakenTerm (S.eliml aₛ ty∶ Aₛ P∶ Pₛ nb∶ []bₛ cb∶ ∷bₛ) cΓₛ i p Bₛ lComps -- = {!   !}
    with 
        compileTerm cΓₛ aₛ in aComps 
        | compileTerm cΓₛ []bₛ in []bComps 
        | compileTerm (cΓₛ S., Aₛ 𝕢 ω S., S.List (Aₛ ↑ 1 ≥ 0) 𝕢 ω S., (Pₛ ↑ 1 ≥ 1) 𝕢 ω) ∷bₛ in ∷bComps
... | just aₜ | just []bₜ | just ∷bₜ
        rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps
            | lemmaWeakenTerm []bₛ cΓₛ i p Bₛ []bComps
            ---- Rewriting double shifts
                -- Rewrite double shift in As, maybe there could be some way to do all these rewrites in one go
                | sym (flipShift Aₛ 1 0 1 i z≤n)
                | sym (flipShift Pₛ 1 1 1 (suc i) (s≤s z≤n))
            | lemmaWeakenTerm ∷bₛ (((cΓₛ S., Aₛ 𝕢 ω) S., S.List (Aₛ ↑ 1 ≥ 0) 𝕢 ω) S., (Pₛ ↑ 1 ≥ 1) 𝕢 ω) (3 + i) (s≤s (s≤s (s≤s p))) Bₛ ∷bComps 
            = 
                lComps
-- Could unify these if it were unified in compiler
lemmaWeakenTerm (S.elimv aₛ 𝕢 𝟘 ty∶ Aₛ P∶ Pₛ nb∶ []bₛ cb∶ ∷bₛ) cΓₛ i p Bₛ lComps
    with compileTerm cΓₛ aₛ in aComps 
        | compileTerm cΓₛ []bₛ in []bComps 
        | compileTerm 
            (cΓₛ S., 
                S.Nat 𝕢 𝟘 S., 
                (Aₛ ↑ 1 ≥ 0) 𝕢 ω S.,
                S.Vec (Aₛ ↑ 2 ≥ 0) (S.var 1 𝕢 𝟘) 𝕢 ω S.,
                (Pₛ ↑ 1 ≥ 1) 𝕢 ω) 
            ∷bₛ 
            in ∷bComps
... | just aₜ | just []bₜ | just ∷bₜ
        rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps
            | lemmaWeakenTerm []bₛ cΓₛ i p Bₛ []bComps
            ---- Rewriting double shifts 
                | sym (flipShift Aₛ 1 0 1 i z≤n) 
                | sym (flipShift Aₛ 2 0 1 i z≤n) 
                | sym (flipShift Pₛ 1 1 1 (2+ i) (s≤s z≤n))
            | lemmaWeakenTerm 
                ∷bₛ 
                (cΓₛ S., 
                    S.Nat 𝕢 𝟘 S., 
                    (Aₛ ↑ 1 ≥ 0) 𝕢 ω S.,
                    S.Vec (Aₛ ↑ 2 ≥ 0) (S.var 1 𝕢 𝟘) 𝕢 ω S.,
                    (Pₛ ↑ 1 ≥ 1) 𝕢 ω) 
                (4 + i) 
                (s≤s (s≤s (s≤s (s≤s p)))) 
                Bₛ 
                ∷bComps = lComps
lemmaWeakenTerm (S.elimv aₛ 𝕢 ω ty∶ Aₛ P∶ Pₛ nb∶ []bₛ cb∶ ∷bₛ) cΓₛ i p Bₛ lComps
    with compileTerm cΓₛ aₛ in aComps 
        | compileTerm cΓₛ []bₛ in []bComps 
        | compileTerm 
            (cΓₛ S., 
                S.Nat 𝕢 ω S., 
                (Aₛ ↑ 1 ≥ 0) 𝕢 ω S., 
                S.Vec (Aₛ ↑ 2 ≥ 0) (S.var 1 𝕢 ω) 𝕢 ω S., 
                (Pₛ ↑ 1 ≥ 1) 𝕢 ω) 
            ∷bₛ in ∷bComps
... | just aₜ | just []bₜ |  just ∷bₜ
        rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps
            | lemmaWeakenTerm []bₛ cΓₛ i p Bₛ []bComps
            ---- Rewrite double shifts 
                | sym (flipShift Aₛ 1 0 1 i z≤n)
                | sym (flipShift Aₛ 2 0 1 i z≤n)
                | sym (flipShift Pₛ 1 1 1 (2+ i) (s≤s z≤n))
            | lemmaWeakenTerm 
                ∷bₛ 
                (cΓₛ S., 
                    S.Nat 𝕢 ω S., 
                    (Aₛ ↑ 1 ≥ 0) 𝕢 ω S., 
                    S.Vec (Aₛ ↑ 2 ≥ 0) (S.var 1 𝕢 ω) 𝕢 ω S., 
                    (Pₛ ↑ 1 ≥ 1) 𝕢 ω) 
                (4 + i) 
                (s≤s (s≤s (s≤s (s≤s p)))) 
                Bₛ 
                ∷bComps  
            = lComps   
---- Base cases
lemmaWeakenTerm S.nill cΓₛ i p Bₛ lComps = lComps
lemmaWeakenTerm (S.nilv𝕢 𝟘) cΓₛ i p Bₛ lComps = lComps
lemmaWeakenTerm (S.nilv𝕢 ω) cΓₛ i p Bₛ lComps = lComps
lemmaWeakenTerm S.z cΓₛ i p Bₛ lComps = lComps


lemmaWeakenType :
    (Cₛ : S.Type) →
    (i : ℕ) →
    (l : ℕ) →
    Cₛ ⇒ Cₜ →
    (Cₛ ↑ i ≥ l) ⇒ Cₜ
lemmaWeakenType S.Nat i l Comps = Comps
lemmaWeakenType (S.List Aₛ) i l Comps 
    with compileType Aₛ in AComps
... | just Aₜ 
        rewrite lemmaWeakenType Aₛ i l AComps = 
            Comps
lemmaWeakenType (S.Vec Aₛ (nₛ 𝕢 𝟘)) i l Comps 
    with compileType Aₛ in AComps
... | just Aₜ 
        rewrite lemmaWeakenType Aₛ i l AComps = 
            Comps  
lemmaWeakenType (S.Vec Aₛ (nₛ 𝕢 ω)) i l Comps 
    with compileType Aₛ in AComps
... | just Aₜ 
        rewrite lemmaWeakenType Aₛ i l AComps = 
            Comps
lemmaWeakenType (S.∶ Aₛ 𝕢 𝟘 ⟶ Bₛ) i l Comps = 
    lemmaWeakenType Bₛ i (suc l) Comps
lemmaWeakenType (S.∶ Aₛ 𝕢 ω ⟶ Bₛ) i l Comps 
    with compileType Aₛ in AComps
... | just Aₜ rewrite lemmaWeakenType Aₛ i l AComps 
        with compileType Bₛ in AComps
...     | just Bₜ rewrite lemmaWeakenType Bₛ i (suc l) AComps = 
            Comps
lemmaWeakenType (S.r∶ Aₛ ⟶ Bₛ) i l Comps 
    with compileType Aₛ in AComps
... | just Aₜ rewrite lemmaWeakenType Aₛ i l AComps 
        with compileType Bₛ in AComps
...     | just Bₜ rewrite lemmaWeakenType Bₛ i (suc l) AComps = 
            Comps             