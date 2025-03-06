module Proofs where

import RunId as S 
import STLC as T
open import RunIdComp

-- I think this fucks up pattern match, make issue
open S using (_~ᵣ_)

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans)

private variable
    sA sB : S.Type
    sa sb sas sbs sf sg : S.Term
    σ π ρ : S.Quantity

    tA tB : T.Type
    ta tb : T.Term

-- Maybe a lemma or relation to from a derivation get its subterm proof
-- mark as inline
lemmabind : ∀ {a b body} → a ≡ b → (a >>= body) ≡ (b >>= body) 
lemmabind {body = body} eq = cong (λ x → x >>= body) eq
{-# INLINE lemmabind #-}

proofsimpler : 
    sa ~ᵣ sb → 
    compileTerm S.[] sa ≡ compileTerm S.[] sb × compileType sa ≡ compileType sb
proofsimpler {sa} {sb} S.~ᵣrefl = refl , refl
proofsimpler {sa} {sb} (S.~ᵣsym a~b) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣtrans a~b a~b₁) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣnatelz a~b) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣnatels a~b a~b₁) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣlisteln a~b) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣlistelc a~b a~b₁) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣveceln a~b) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣvecelc a~b a~b₁) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣs {n} {m} a~b) = 
    let pt , _ = proofsimpler a~b in
    lemmabind pt , refl
proofsimpler {sa} {sb} (S.~ᵣlist a~b) = refl , let _ , pt = proofsimpler a~b in {!   !} -- cong (λ x → x >>= λ v → just (T.List v)) pt
proofsimpler {sa} {sb} (S.~ᵣ∷l a~b a~b₁) = (let pt , _ = proofsimpler a~b in lemmabind {! pt  !}) , refl 
proofsimpler {sa} {sb} (S.~ᵣpiω a~b a~b₁) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣpi𝟘 a~b) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣlamω a~b) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣlam𝟘 a~b) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣappω a~b a~b₁) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣapp𝟘 a~b) = {!   !}
proofsimpler {sa} {sb} S.~ᵣbetaω = {!   !}
proofsimpler {sa} {sb} (S.~ᵣvecω a~b a~b₁) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣvec𝟘 a~b) = {!   !} , {!   !} 
proofsimpler {sa} {sb} S.~ᵣnilvω = refl , refl 
proofsimpler {sa} {sb} S.~ᵣnilv𝟘 = refl , refl 
proofsimpler {sa} {sb} (S.~ᵣ∷vω a~b a~b₁ a~b₂) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣ∷v𝟘 a~b a~b₁) = {!   !} , {!   !} 
proofsimpler {sa} {sb} (S.~ᵣηlist a~b a~b₁) = {!   !}
proofsimpler {sa} {sb} (S.~ᵣηvec a~b a~b₁) = {!   !}

proof2 : 
    S.[] S.⊢ sa S.𝕢 σ ∶ sA → 
    S.[] S.⊢ sb S.𝕢 σ ∶ sB → 
    sa ~ᵣ sb → 
    compileTerm S.[] sa ≡ compileTerm S.[] sb × compileType sa ≡ compileType sb 
proof2 {S.var x} da db a~b = {!   !}
proof2 {S.ƛ∶ x ♭ sa} da db a~b = {!   !}
proof2 {S.ƛr∶ x ♭ sa} da db a~b = {!   !}
proof2 {sa S.· sa₁ 𝕢 x} da db a~b = {!   !}
proof2 {sa S.·ᵣ sa₁} da db a~b = {!   !}
proof2 {S.z} da db a~b = {!   !}
proof2 {S.s sa} da db a~b = {!   !}
proof2 {S.nill} da db a~b = {!   !}
proof2 {sa S.∷l sa₁} da db a~b = {!   !}
proof2 {S.nilv𝕢 x} da db a~b = {!   !}
proof2 {sa S.∷v sa₁ 𝕟 sa₂ 𝕢 x} da db a~b = {!   !}
proof2 {S.elimnat sa P∶ sa₁ zb∶ sa₂ sb∶ sa₃} da db a~b = {!   !}
proof2 {S.eliml sa P∶ sa₁ nb∶ sa₂ cb∶ sa₃} da db a~b = {!   !}
proof2 {S.elimv x P∶ sa nb∶ sa₁ cb∶ sa₂} da db a~b = {!   !}
proof2 {S.Nat} da db S.~ᵣrefl = refl , refl 
proof2 {S.Nat} {sb = sb} da db (S.~ᵣsym a~b) = {!   !}
proof2 {S.Nat} S.⊢Nat db (S.~ᵣtrans a~b a~b₁) = {!   !}
proof2 {S.Nat} (S.⊢conv da x) db (S.~ᵣtrans a~b a~b₁) = {!   !}
proof2 {S.Nat} (S.⊢TM-𝟘 da) db (S.~ᵣtrans a~b a~b₁) = {!   !} 
proof2 {S.List x} da db S.~ᵣrefl = refl , refl 
proof2 {S.List x} da db (S.~ᵣsym a~b) = {!   !}
proof2 {S.List x} da db (S.~ᵣtrans a~b a~b₁) = {!   !}
proof2 {S.List sA} (S.⊢List da) (S.⊢List {A = sB} db) (S.~ᵣlist a~b) = refl , {!   !}
-- write some lemma to extract inner type derivation from conv?
proof2 {S.List sA} (S.⊢List da) (S.⊢conv db x) (S.~ᵣlist {B = sB} a~b) = refl , {!   !}
proof2 {S.List sA} (S.⊢List da) (S.⊢TM-𝟘 db) (S.~ᵣlist a~b) = refl , {!   !} 
proof2 {S.List sA} (S.⊢conv da x) (S.⊢List db) (S.~ᵣlist a~b) = {!   !}
proof2 {S.List sA} (S.⊢conv da x) (S.⊢conv db x₁) (S.~ᵣlist a~b) = {!   !}
proof2 {S.List sA} (S.⊢conv da x) (S.⊢TM-𝟘 db) (S.~ᵣlist a~b) = {!   !}
proof2 {S.List sA} (S.⊢TM-𝟘 da) (S.⊢List db) (S.~ᵣlist a~b) = {!   !}
proof2 {S.List sA} (S.⊢TM-𝟘 da) (S.⊢conv db x) (S.~ᵣlist a~b) = {!   !}
proof2 {S.List sA} (S.⊢TM-𝟘 da) (S.⊢TM-𝟘 db) (S.~ᵣlist a~b) = {!   !}
proof2 {S.Vec sa x} da db a~b = {!  da db  !}
proof2 {S.∶ x ⟶ x₁} da db a~b = {!   !}
proof2 {S.r∶ x ⟶ x₁} da db a~b = {!   !}
proof2 {S.Sett x} da db a~b = {!   !}

-- Find a way to exclude : Set from input?
-- Define normal form of STLC for comparison?
~ᵣ⇒comp≡ : 
    S.[] S.⊢ sa S.𝕢 σ ∶ sA → 
    S.[] S.⊢ sb S.𝕢 σ ∶ sB → 
    sa ~ᵣ sb → 
    sA ~ᵣ sB → 
    compile sa sA ≡  compile sb sB
~ᵣ⇒comp≡ {S.var x} {sb = sb} (S.⊢conv da x₁) db S.~ᵣrefl A~B = {!   !}
~ᵣ⇒comp≡ {S.var x} {sb = sb} (S.⊢conv da x₁) db (S.~ᵣsym a~ᵣb) A~B = {!   !}
~ᵣ⇒comp≡ {S.var x} {sb = sb} (S.⊢conv da x₁) db (S.~ᵣtrans a~ᵣb a~ᵣb₁) A~B = {!   !}
~ᵣ⇒comp≡ {S.var x} (S.⊢TM-𝟘 da) db S.~ᵣrefl A~B = {!   !}
~ᵣ⇒comp≡ {S.var x} (S.⊢TM-𝟘 da) db (S.~ᵣsym a~ᵣb) A~B = {!   !}
~ᵣ⇒comp≡ {S.var x} (S.⊢TM-𝟘 da) db (S.~ᵣtrans a~ᵣb a~ᵣb₁) A~B = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl S.~ᵣrefl = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣsym A~B) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣtrans A~B A~B₁) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣnatelz A~B) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣnatels A~B A~B₁) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣlisteln A~B) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣlistelc A~B A~B₁) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣveceln A~B) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣvecelc A~B A~B₁) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣs A~B) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣlist A~B) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣ∷l A~B A~B₁) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣpiω A~B A~B₁) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣpi𝟘 A~B) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣlamω A~B) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣlam𝟘 A~B) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣappω A~B A~B₁) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣapp𝟘 A~B) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl S.~ᵣbetaω = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣvecω A~B A~B₁) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣvec𝟘 A~B) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl S.~ᵣnilvω = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl S.~ᵣnilv𝟘 = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣ∷vω A~B A~B₁ A~B₂) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣ∷v𝟘 A~B A~B₁) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣηlist A~B A~B₁) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db S.~ᵣrefl (S.~ᵣηvec A~B A~B₁) = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db (S.~ᵣsym a~ᵣb) A~B = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db (S.~ᵣtrans a~ᵣb a~ᵣb₁) A~B = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db (S.~ᵣlamω a~ᵣb) A~B = {!   !}
~ᵣ⇒comp≡ {S.ƛ∶ x ♭ sa} da db (S.~ᵣlam𝟘 a~ᵣb) A~B = {!   !}
~ᵣ⇒comp≡ {S.ƛr∶ x ♭ sa} da db S.~ᵣrefl A~B = {!   !}
~ᵣ⇒comp≡ {S.ƛr∶ x ♭ sa} da db (S.~ᵣsym a~ᵣb) A~B = {!   !}
~ᵣ⇒comp≡ {S.ƛr∶ x ♭ sa} da db (S.~ᵣtrans a~ᵣb a~ᵣb₁) A~B = {!   !}
~ᵣ⇒comp≡ {sa S.· sa₁ 𝕢 x} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {sa S.·ᵣ sa₁} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {S.z} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {S.s sa} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {S.nill} {sA = sA} {sB = sB} S.⊢nill S.⊢nill S.~ᵣrefl A~B = {!   !}
~ᵣ⇒comp≡ {S.nill} {sA = sA} {sB = sB} S.⊢nill (S.⊢conv db x) S.~ᵣrefl A~B = {!   !}
~ᵣ⇒comp≡ {S.nill} {sA = sA} {sB = sB} S.⊢nill (S.⊢TM-𝟘 db) S.~ᵣrefl A~B = {!   !}
~ᵣ⇒comp≡ {S.nill} {sA = sA} (S.⊢conv da x) db S.~ᵣrefl A~B = {!   !}
~ᵣ⇒comp≡ {S.nill} {sA = sA} (S.⊢TM-𝟘 da) db S.~ᵣrefl A~B = {!   !}
~ᵣ⇒comp≡ {S.nill} {sA = sA} da db (S.~ᵣsym a~ᵣb) A~B = {!   !}
~ᵣ⇒comp≡ {S.nill} {sA = sA} da db (S.~ᵣtrans a~ᵣb a~ᵣb₁) A~B = {!   !}
~ᵣ⇒comp≡ {sa S.∷l sa₁} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {S.nilv𝕢 x} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {sa S.∷v sa₁ 𝕟 sa₂ 𝕢 x} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {S.elimnat sa P∶ sa₁ zb∶ sa₂ sb∶ sa₃} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {S.eliml sa P∶ sa₁ nb∶ sa₂ cb∶ sa₃} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {S.elimv x P∶ sa nb∶ sa₁ cb∶ sa₂} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {S.Nat} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {S.List x} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {S.Vec sa x} da db S.~ᵣrefl A~B = {!   !}
~ᵣ⇒comp≡ {S.Vec sa x} da db (S.~ᵣsym a~ᵣb) A~B = {!   !}
~ᵣ⇒comp≡ {S.Vec sa x} da db (S.~ᵣtrans a~ᵣb a~ᵣb₁) A~B = {!   !}
~ᵣ⇒comp≡ {S.Vec sa x} da db (S.~ᵣvecω a~ᵣb a~ᵣb₁) A~B = {!   !}
~ᵣ⇒comp≡ {S.Vec sa x} {sA = sA} da db (S.~ᵣvec𝟘 a~ᵣb) A~B = {!   !}
~ᵣ⇒comp≡ {S.∶ x ⟶ x₁} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {S.r∶ x ⟶ x₁} da db a~ᵣb A~B = {!   !}
~ᵣ⇒comp≡ {S.Sett x} da db a~ᵣb A~B = {!   !}

-- Might need to shift in sB here
runid⇒id :  
    S.[] S.⊢ sf S.𝕢 σ ∶ (S.r∶ sA ⟶ sB) → 
    (compileTerm S.[] sf ≡ just (T.ƛ (T.var 0))) × compileType sA ≡ compileType sB
runid⇒id {sf} df = {!   !}     