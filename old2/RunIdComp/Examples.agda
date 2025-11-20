module RunIdComp.Examples where 

import RunId as S
import STLC as T
open import RunIdComp
open import Proofs.Relations

open import Data.Nat
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open S using (
    𝟘; ω;
    _𝕢_;
    _~ᵣ_;
    _↑_≥_)

elimnatExTe : S.Term
elimnatExTe = (S.elimnat S.z P∶ S.Nat 
            zb∶ S.z 
            sb∶ S.s (S.var 0))


testElimNat : 
    compileTerm S.[] elimnatExTe ≡ 
    just 
        (T.elimnat T.z 
            zb∶ T.z 
            sb∶ T.s (T.var 0))
testElimNat = refl

testElimNat↑ :  
    compileTerm (S.insertType S.[] zero z≤n S.Nat 𝟘)
        (_↑_≥_ 
            elimnatExTe 
            1 
            zero) ≡
    just
        (T.elimnat T.z 
            zb∶ T.z 
            sb∶ T.s (T.var 0))
testElimNat↑ = refl