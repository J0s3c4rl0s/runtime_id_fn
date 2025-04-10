module AgdaRunIdExamples where


module ListExamples where
    open import Data.Nat
    -- open import Data.Nat.Properties
    open import Data.List as List
    open import Data.Vec as Vec

    private variable 
        A B C D : Set 
        n m : ℕ

    listElim : 
        (xs : List A) →
        (P : List A → Set) →
        P [] →
        ((x : A) → (xs : List A) → P xs → P (x ∷ xs)) → 
        P xs
    listElim [] P base step = base
    listElim (x ∷ xs) P base step = step x xs (listElim xs P base step)



    open import Data.Product
    open import Relation.Binary.PropositionalEquality

    -- vecToListProd :
    --     (v : Vec A n) →
    --     Σ[ xs ∈ List A ] (List.length xs ≡ n)
    -- vecToListProd [] = [] , refl
    -- vecToListProd (x ∷ xs) = (x ∷ proj₁ (vecToListProd xs)) , cong (λ m → suc m) (proj₂ (vecToListProd xs))

    listToVec : 
        (xs : List A) →
        Vec A (List.length xs)
    listToVec xs = listElim xs (λ x → Vec _ (List.length x)) [] (λ x xs acc → x ∷ acc)

    vecToList :
        Vec A n →
        List A  
    vecToList [] = []
    vecToList (_∷_ {n} x xs) = x ∷ (vecToList xs)

    listToVec≅vecToListTo : ∀ {vs : Vec A n} →
        -- Need Vec A (List.length (vecToList vs)) ≡ Vec A n on RHS
        -- I dont think this can be known definitionally (specially in an intensional language)
        listToVec (vecToList vs) ≡ {!  !} 
    listToVec≅vecToListFrom : ∀ {ls : List A} → vecToList (listToVec ls) ≡ ls
    listToVec≅vecToListFrom {ls = []} = refl
    listToVec≅vecToListFrom {ls = x ∷ ls} = cong (λ x₁ → x ∷ x₁) (listToVec≅vecToListFrom {ls = ls}) 

    module iso where
        listToVecI : 
            (xs : List A) →
            Vec A (List.length xs)
        listToVecI xs = {!   !} -- listElim xs (λ x → Vec _ (List.length x)) [] (λ x xs acc → x ∷ acc)

        vecToListI :
            Vec A n →
            List A  
        vecToListI [] = []
        vecToListI (_∷_ {n} x xs) = x ∷ (vecToListI xs)

        infix 0 _≃_
        record _≃_ (A B : Set) : Set where
            field
                to   : A → B
                from : B → A
                from∘to : ∀ (x : A) → from (to x) ≡ x
                to∘from : ∀ (y : B) → to (from y) ≡ y
        open _≃_
        isoListVec : List A ≃ Vec A n
        isoListVec = record { to = {!  listToVec  !} ; from = {!   !} ; from∘to = {!   !} ; to∘from = {!   !} }


    vecToList' :
        Vec A n →
        List A
    vecToList' = Vec.foldr (λ x → List _) (λ a acc → a ∷ acc) []

    vecToList'' :
        Vec A n →
        List A
    vecToList'' = foldr′ (λ x xs → x ∷ xs) []
    
    open import Relation.Binary.PropositionalEquality

    pat≡foldr : (vecToList {A = A} {n = n}) ≗ vecToList'
    pat≡foldr [] = refl
    pat≡foldr (x ∷ xs) = cong (λ x₁ → x ∷ x₁) (pat≡foldr xs)

    foldr≡foldr′ : (vecToList' {A = A} {n = n}) ≗ vecToList''
    foldr≡foldr′ = λ x → refl

    -- Write map example, e.g. mapping list of lists to list of vecs or sth similar

    module mapExamples where
        mapListToVec : 
            -- assume f is runid
            -- Should f be erased?
            (A → B) →
            (xs : List A)  → 
            Vec B (List.length xs)
        mapListToVec f [] = []
        mapListToVec f (x ∷ xs) = f x ∷ mapListToVec f xs 

        mapRList : 
            -- imagine f is runid
            (A → B) →
            (xs : List A)  →
            List B
        -- But use regular map function?
        mapRList f xs = List.map f xs

        open import Data.Fin
        mapFin :
            List (Fin n) → 
            List ℕ 
        -- toℕ is runid so assume its annotated
        mapFin = List.map toℕ

        listFinToVecℕ : 
            (xs : List (Fin n)) →
            Vec ℕ (List.length xs)
        -- toℕ is runid so assume its annotated
        listFinToVecℕ = mapListToVec toℕ

    -- Reverse list/vector? 

    data Even : ℕ → Set where
        even-zero  : Even zero
        even-plus2 : {n : ℕ} → Even n → Even (suc (suc n))

    open import Data.Product

    ListProd : (A : Set) → (P : A → Set) → Set
    ListProd A P = List (Σ[ a ∈ A ] P a)

    EvenListToList : 
        List (Σ[ x ∈ ℕ ] Even x) →
        List ℕ
    EvenListToList = List.foldr (λ prod xs → (proj₁ prod) ∷ xs) []


    module ListWith where
        data ListWith (A : Set) (P : A → Set) : Set where
            [] : ListWith A P
            _p_∷_ : (a : A) → P a  → ListWith A P → ListWith A P
        
        listWithLength : ∀ {P} → ListWith A P → ℕ
        listWithLength [] = zero
        listWithLength (a p x ∷ xs) = suc (listWithLength xs)

        evenListToVec : 
            (xs : ListWith ℕ Even) → 
            Vec ℕ (listWithLength xs)
        evenListToVec [] = []
        evenListToVec (a p x ∷ xs) = a ∷ (evenListToVec xs)

    scrutineeIrred : 
        List A →
        List A
    scrutineeIrred = List.map λ x → x

    -- Why would you ever need to match on a neutral nonvar
    -- Could be that neutral contains some var which influences outcome and that is what we want to subst for?
    -- Ig if we can invert when the expression reduces to [] or _∷_ that can be applied to the subst in the branches?
    tmp : (A → B) → List A → {!   !} 
    tmp f xs = 
        listElim (List.map f xs) (λ x → {!   !}) {!   !} {!   !}

    elimScrutineHeadExample : {!   !}
    elimScrutineHeadExample = {! Vec.foldr  !}

module PropertyExamples where
    private variable
        A B C D : Set

    open import Function

    flipRunId :
        -- A ->r B 
        (A → B) →
        -- B ->r A
        (B → A)
    flipRunId f = {!   !}

    transRunId : 
        -- assume all arrows are runid
        (A → B) → 
        (B → C) → 
        (A → C)
    transRunId f g = g ∘ f

    transRunId' : 
        -- assume all arrows are runid
        (A → B) → 
        (B → C) → 
        (A → C)
    transRunId' f g a = g (f a)

    convertRunidL : 
        -- assume all arrows are runid
        (A → B) →
        (B → D) →
        (C → D) →
        A → C
    -- This one might not be trivial
    convertRunidL f g h = (flipRunId h ∘ g) ∘ f

    
    convertRunidR : 
        -- assume all arrows are runid
        (A → B) →
        (A → C) →
        (C → D) → 
        B → D
    convertRunidR f g h  = (h ∘ g) ∘ (flipRunId f)

    open import Relation.Binary.PropositionalEquality

    comm : 
        -- A ->r B
        (f : A → B) →
        -- C ->r D
        (g : C → D) →
        -- A ->r C
        (h : A → C) → 
        -- B ->r D
        (i : B → D) →
        (i ∘ f) ≗ (g ∘ h)
    comm f g h i = {!   !}
          

        

module SigmaExamples where
    record ∃ (A : Set) (@0 P : A → Set) : Set where
        constructor _⟨_⟩
        field
            value    : A
            @0 proof : P value
    open ∃ public

    private variable 
        A B : Set

    record PredsRunEq (P : A → Set) (Q : B → Set) :  Set where
        constructor mkP~Q
        field 
            -- A ->r B
            A~B : A → B 
            P~QthruA~B : (@0 a : A) → P a → Q (A~B a)

    module LHS where
        record Σ₁ (@0 A : Set) (P : A → Set) : Set where
            constructor _⟨_⟩
            field
                @0 value    : A
                proof : P value
        open Σ₁ public

        mapΣ₁RunId : ∀ {P Q} →
            PredsRunEq P Q →
            -- Σ₂ A P ->r Σ₂ B Q
            Σ₁ A  P → Σ₁ B Q
        -- This can only hold if P~QthruA~B : (a : A) → P a →r P (A~B a)
        mapΣ₁RunId (mkP~Q A~B P~QthruA~B) (a ⟨ p ⟩) = (A~B a) ⟨ P~QthruA~B a p ⟩ 


    module RHS where
        record Σ₂ (A : Set) (@0 P : A → Set) : Set where
            constructor _⟨_⟩
            field
                value    : A
                @0 proof : P value
        open Σ₂ public

        mapΣ₂RunId : ∀ {P Q} →
            PredsRunEq P Q →
            -- Σ₂ A P ->r Σ₂ B Q
            Σ₂ A  P → Σ₂ B Q
        mapΣ₂RunId (mkP~Q A~B P~QthruA~B) (a ⟨ p ⟩) = (A~B a) ⟨ P~QthruA~B a p ⟩


    -- Have to consider erased args, var 0 or var first unerased var
    mapRefine : {@0 P Q : A → Set} (@0 f : ∀ {x} → P x → Q x) → ∃ A P → ∃ A Q
    mapRefine f (x ⟨ p ⟩) = x ⟨ f p ⟩

    

    open import Data.Bool
    open import Data.Empty

    @0 Reflects : Set → Bool → Set
    Reflects P true  = P
    Reflects P false = P → ⊥

    Dec : @0 Set → Set
    Dec P = ∃ Bool (Reflects P)
    
    infixr 9 _∘_
    _∘_ : ∀ {a b c : Set} → (b → c) → (a → b) → a → c
    (f ∘ g) x = f (g x)

    mapDec : {@0 a b : Set}
        → @0 (a → b)
        → @0 (b → a)
        → Dec a → Dec b
    mapDec f g (true  ⟨ x ⟩) = true  ⟨ f x   ⟩
    mapDec f g (false ⟨ h ⟩) = false ⟨ h ∘ g ⟩

    -- Write example with no erasure?

module PropEqualExamples where
    private variable
        A B : Set
    
    open import Relation.Binary.PropositionalEquality
    subst0 : {@0 a : Set} 
        (@0 p : @0 a → Set) {@0 x y : a} → @0 x ≡ y → 
        p x → 
        p y
    subst0 p refl z = z

    substrunid : ∀ {@0 P : {T : Set} → T → Set} →
        -- f : A ->r B
        (f : A → B) →
        (a : A) → (b : B) →
        -- P a ->r P b
        P a → P b
    substrunid f a b Pa = {!  P  !}

    open import Data.Nat
    open import Data.List as List 
    open import Data.Vec as Vec

    data ListAll {A : Set} (P : A → Set) : List A → Set where
        []  : ListAll P []
        _∷_ : ∀ {x xs} (px : P x) (pxs : ListAll P xs) → ListAll P (x ∷ xs)

    data VecAll {A : Set} (P : A → Set) : {@0 n : ℕ} → Vec A n → Set where
        []  : VecAll P  []
        _∷_ : ∀ {x n xs} (px : P x) (pxs : VecAll P {n} xs) → VecAll P (x ∷ xs)


    substList : ∀ {P xs} →
        (f : (zs : List A) → Vec A (List.length zs)) →
        ListAll P xs →
        VecAll P (f xs) 
    substList f [] = {! VecAll.[]  !}
    substList f (px ∷ ys) = {! ? ∷ ?  !}

    tmp : A → B
    tmp = subst {!   !} {!   !}

    transport : ∀ {A B : Set} → A ≡ B → A → B
    transport refl a = a

    f : A → B
    f x = {!   !} -- transport refl x