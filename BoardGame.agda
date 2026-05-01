module BoardGame where

-- TODO
--
-- Prove:
--  1.  (a ; (b ; c) ) == ((a ; b) ; c )
--  2.  Two lists cannot contain the same reference

open import Data.Integer using (ℤ) renaming (+_ to +ℤ_; _+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _<_ to _<ℤ_)
open import Data.String using () renaming (String to Var)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using (Pred; Decidable)
open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
open import BigAndSmallStepSemantics using (⌈>; BigStepSemantics)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤) renaming (tt to ttt)
open import Relation.Nullary.Negation using (¬_)
open import Data.Maybe using (Maybe; _>>=_; map; just; nothing)
open import Data.Sum using (_⊎_) renaming (inj₁ to inj₁_; inj₂ to inj₂_)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
open import Data.List using (_∷_; []; length) renaming (List to ListAny)
open import Data.Float using (Float) renaming (_≡ᵇ_ to _==ᶠ_)
open import Data.Bool using (Bool; _∧_) renaming (true to tt; false to ff)

data 𝕍 : Set
data Stmt : Set
data PosArgDecl : Set
data OptionalArg : Set
data Expr : Set
data ExprList : Set
data Member : Set

String = Var
Loc = ℕ

open import Data.Nat using (_^_) renaming (suc to nxt; _<_ to _<ₙ_; _<?_ to _<?ₙ_; _≡ᵇ_ to _==ₙ_)
open import State 𝕍 Loc _<ₙ_ _<?ₙ_ _==ₙ_ using (_⊢_==ₛ_) renaming
    (_[_↦_]     to _[_↦ₛ_]
    ;lookup     to lookupₛ
    ;State      to Store
    ;emptyState to emptyStore
    ;sortedNil  to sortedNilₛ
    ;sortedCons to sortedConsₛ
    ;sortedOne  to sortedOneₛ
    )


open import Data.String using () renaming (_<_ to _<ₛ_; _<?_ to _<?ₛ_; _==_ to _==ₛ_)
open import State Loc Var _<ₛ_ _<?ₛ_ _==ₛ_ using () renaming
    (_[_↦_]     to _[_↦ₑ_]
    ;lookup     to lookupₑ
    ;State      to Envᵥ
    ;emptyState to emptyEnv
    ;sortedNil  to sortedNilₑ
    ;sortedCons to sortedConsₑ
    ;sortedOne  to sortedOneₑ
    ;_⊢_==ₛ_    to _⊢_==ₑ_
    )

open import State Expr Var _<ₛ_ _<?ₛ_ _==ₛ_ using () renaming
    (State   to Var⇀Expr
    ;_⊢_==ₛ_ to _⊢_==ₑₓ_
    )


open import Data.Float using (Float)
open import Data.Fin using (Fin; toℕ)

data Int : Set where
    nonNeg_ : Fin (2 ^ 63) → Int
    -⟨_+1⟩  : Fin (2 ^ 63) → Int

open import Data.Vec using (Vec)

data 𝕍 where
    ref_      : (l : Loc     ) → 𝕍
    bool_     : (b : Bool    ) → 𝕍
    int_      : (i : Int     ) → 𝕍
    float_    : (f : Float   ) → 𝕍
    str_      : (s : String  ) → 𝕍
    object_   : (ℰ : Envᵥ    ) → 𝕍
    list_     : {n : ℕ       } → (σ : Vec Loc n) → 𝕍
    primFunc_ : (implDefinedFnRef : Loc) → 𝕍

    -- args include both positional arguments and optional arguments, due to it being used to infer evaluation order of the exprssions.
    userFunc : (ℰ : Envᵥ) → (args : ListAny Var) → (optArgs : Var⇀Expr) → (body : Stmt) → 𝕍


data Object (σ  : Store) : Set where
    obj : (l : Loc) → (o : Envᵥ) → {just (object o) ≡ lookupₛ σ l} → Object σ

data Stmt where
    _⍮_           : (S1 : Stmt) → (S2 : Stmt) → Stmt
    skip          : Stmt
    if_then_else_ : (e : Expr ⊎ 𝕍 ) → (S1 : Stmt) → (S2 : Stmt) → Stmt
    while_dø_     : (e : Expr ⊎ 𝕍 ) → (S : Stmt) → Stmt
    fn_⟨_,_⟩_     : (x : Var      ) → (P : PosArgDecl ) → (O : OptionalArg) → (S : Stmt) → Stmt
    return_       : (e : Expr     ) → Stmt
    apply_dø_     : (e : Expr ⊎ 𝕍 ) → (S : Stmt) → Stmt
    ⟨_⟩           : (S : Stmt     ) → Stmt
    _←_           : (x : Member ⊎ Loc) → (e : Expr ⊎ 𝕍) → Stmt
    expr          : (e : Expr ⊎ 𝕍 ) → Stmt

data PosArgDecl where
    arg : Var → PosArgDecl
    _,arg_ : Var → PosArgDecl → PosArgDecl

data OptionalArg where
    _oarg_ : Var → Expr → OptionalArg
    _,,_←_ : Var → Expr → OptionalArg → OptionalArg

data Expr where
    _==_   : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _!=_   : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _<=_   : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _>=_   : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _<_    : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _>_    : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _··=_  : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _··_   : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _+_    : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _-_    : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _*_    : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _/_    : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _│_    : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _&_    : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _%_    : (e₁ : Expr ⊎ 𝕍) → (e₂ : Expr ⊎ 𝕍) → Expr
    _[_,_] : (e  : Expr ⊎ 𝕍) → (E  : ExprList) → (O : OptionalArg) → (S : Stmt) → Expr -- Index
    [_]    : (E  : ExprList     ) → Expr
    fₗ_    : (fₗ : Float        ) → Expr
    iₗ_    : (iₗ : Int          ) → Expr
    bₗ_    : (bₗ : Bool         ) → Expr
    sₗ_    : (sₗ : String       ) → Expr
    Xₗ_    : (m  : Member ⊎ Loc ) → Expr

data ExprList where
    eL_ : (e : Expr) → ExprList
    _,expr_ : (e : Expr) → (E : ExprList) → ExprList

data Member where
    last_ : Var → Member
    _deref_ : Expr → Var → Member
    _[_]ₘ : (Expr ⊎ 𝕍) → (Expr ⊎ 𝕍) → Member

σ∘ℰ_ : {ℰ : Envᵥ} → {σ : Store} → Var → Maybe 𝕍
σ∘ℰ_ {ℰ} {σ} x = lookupₑ ℰ x >>= lookupₛ σ

infixr 5 _⍮_
infixr 6 while_dø_
infixr 6 if_then_else_

--State = (Envᵥ × Store) × ListAny (Envᵥ × Store)

ET = (Expr ⊎ 𝕍) × Store × Loc × ListAny Envᵥ
data ⟨_⟩⇒E⟨_⟩ : ET → ET → Set

ST₁ = Stmt × Store × Loc × ListAny Envᵥ
ST₂ = Store × Loc × ListAny Envᵥ
ST = ST₁ ⊎ ST₂
data ⟨_⟩⇒Sₐ⟨_⟩ : (IN : ST) → (OUT : ST) → Set
⟨⟩⇒S⟨⟩1 : (IN : ST₁) → (OUT : ST₁) → Set
⟨⟩⇒S⟨⟩1 x y = ⟨ inj₁ x ⟩⇒Sₐ⟨ inj₁ y ⟩
syntax ⟨⟩⇒S⟨⟩1 IN OUT = ⟨ IN ⟩⇒S⟨ OUT ⟩

MT = (Member ⊎ Loc) × Store × Loc × ListAny Envᵥ
data ⟨_⟩⇒M⟨_⟩ : MT → MT → Set

data OpType : Set where
    ⊕+ ⊕- ⊕* ⊕/ ⊕% ⊕··= ⊕·· ⊕== ⊕!= ⊕> ⊕< ⊕>= ⊕<= : OpType

getOp : OpType → Expr ⊎ 𝕍 → Expr ⊎ 𝕍 → Expr
getOp ⊕==  = _==_
getOp ⊕!=  = _!=_
getOp ⊕>   = _>_
getOp ⊕<   = _<_
getOp ⊕>=  = _>=_
getOp ⊕<=  = _<=_
getOp ⊕+   = _+_
getOp ⊕-   = _-_
getOp ⊕*   = _*_
getOp ⊕/   = _/_
getOp ⊕%   = _%_
getOp ⊕··= = _··=_
getOp ⊕··  = _··_

_==ᵢ_ : Int → Int → Bool
(nonNeg x₁) ==ᵢ (nonNeg x₂) = toℕ x₁ ==ₙ toℕ x₂
-⟨ x₁ +1⟩ ==ᵢ -⟨ x₂ +1⟩ = toℕ x₁ ==ₙ toℕ x₂
(nonNeg _) ==ᵢ -⟨ _ +1⟩ = ff
-⟨ _ +1⟩ ==ᵢ (nonNeg _) = ff

open import Data.Bool using (_∨_)
_==ᵥ_ : ∀{n m} → Vec Loc n → Vec Loc m → Bool
Vec.[]       ==ᵥ Vec.[]        = tt
(x₁ Vec.∷ σ₁) ==ᵥ (x₂ Vec.∷ σ₂) = (x₁ ==ₙ x₂) ∨ σ₁ ==ᵥ σ₂
_ ==ᵥ _ = ff

_𝕍==_ : 𝕍 → 𝕍 → 𝕍
(object ℰ₁     ) 𝕍== (object ℰ₂     ) = bool (_==ₙ_ ⊢ ℰ₁ ==ₑ ℰ₂)
(float f₁      ) 𝕍== (float f₂      ) = bool (f₁ ==ᶠ f₂)
(int i₁        ) 𝕍== (int i₂        ) = bool (i₁ ==ᵢ i₂)
(str s₁        ) 𝕍== (str s₂        ) = bool (s₁ ==ₛ s₂)
(list σ₁       ) 𝕍== (list σ₂       ) = bool (σ₁ ==ᵥ σ₂)
(bool ff       ) 𝕍== (bool ff       ) = bool tt
(bool tt       ) 𝕍== (bool tt       ) = bool tt
(ref l₁        ) 𝕍== (ref l₂        ) = bool (l₁ ==ₙ l₂)
(primFunc implDefinedFnRef₁) 𝕍== (primFunc implDefinedFnRef₂) = bool (implDefinedFnRef₁ ==ₙ implDefinedFnRef₂)
(userFunc ℰ₁ args₁ optArgs₁ body₁) 𝕍== (userFunc ℰ₂ args₂ optArgs₂ body₂ ) = bool ({!   !} ∧ {!   !} ∧ {!   !})
(object ℰ      ) 𝕍== _ = bool ff
(float f       ) 𝕍== _ = bool ff
(int i         ) 𝕍== _ = bool ff
(str s         ) 𝕍== _ = bool ff
(list σ        ) 𝕍== _ = bool ff
(bool b        ) 𝕍== _ = bool ff
(ref b         ) 𝕍== _ = bool ff
(primFunc implDefinedFnRef) 𝕍== _ = bool ff
(userFunc ℰ args optArgs body) 𝕍== _ = bool ff

-- TODO
_[_]ₐ_ : 𝕍 → OpType → 𝕍 → 𝕍
x₁ [ ⊕==  ]ₐ x₂ = x₁ 𝕍== x₂
x₁ [ ⊕!=  ]ₐ x₂ = x₁
x₁ [ ⊕>   ]ₐ x₂ = x₁
x₁ [ ⊕<   ]ₐ x₂ = x₁
x₁ [ ⊕>=  ]ₐ x₂ = x₁
x₁ [ ⊕<=  ]ₐ x₂ = x₁
x₁ [ ⊕+   ]ₐ x₂ = x₁
x₁ [ ⊕-   ]ₐ x₂ = x₁
x₁ [ ⊕*   ]ₐ x₂ = x₁
x₁ [ ⊕/   ]ₐ x₂ = x₁
x₁ [ ⊕%   ]ₐ x₂ = x₁
x₁ [ ⊕··= ]ₐ x₂ = x₁
x₁ [ ⊕··  ]ₐ x₂ = x₁

data ⟨_⟩⇒E⟨_⟩ where
    OP :    ∀ {v₁ v₂ σ l 𝒮}
            → (⊕ : OpType)
            → ⟨(inj₁ ((getOp ⊕) (inj₂ v₁) (inj₂ v₂))) , σ , l , 𝒮 ⟩⇒E⟨ (inj₂ (v₁ [ ⊕ ]ₐ v₂)) , σ , l , 𝒮 ⟩

data ⟨_⟩⇒Sₐ⟨_⟩ where

    IF-E :  ∀ {S₁ S₂ e e' σ σ' l l' 𝒮 }
            → ⟨    e                 , σ , l , 𝒮 ⟩⇒E⟨    e'                 , σ' , l' , 𝒮 ⟩
            → ⟨ if e then S₁ else S₂ , σ , l , 𝒮 ⟩⇒S⟨ if e' then S₁ else S₂ , σ' , l' , 𝒮 ⟩

    IF-T :  ∀ {S₁ S₂ σ l 𝒮}
            → ⟨ if (inj₂ (bool tt)) then S₁ else S₂ , σ , l , 𝒮 ⟩⇒S⟨ ⟨ S₁ ⟩ , σ , l , 𝒮 ⟩

    IF-F :  ∀ {S₁ S₂ σ l 𝒮}
            → ⟨ if (inj₂ (bool ff)) then S₁ else S₂ , σ , l , 𝒮 ⟩⇒S⟨ ⟨ S₂ ⟩ , σ , l , 𝒮 ⟩

    BLOCK-S :   ∀ {S S' σ σ' l l' 𝒮 𝒮' }
                → ⟨ S , σ , l , 𝒮 ⟩⇒S⟨ S' , σ' , l' , 𝒮' ⟩
                → ⟨ ⟨ S ⟩ , σ , l , 𝒮 ⟩⇒S⟨ ⟨ S' ⟩ , σ' , l' , 𝒮' ⟩

    BLOCK : ∀ {S σ σ' l l' 𝒮 𝒮' ℰ }
            → ⟨ inj₁ (S , σ , l , (ℰ ∷ 𝒮)) ⟩⇒Sₐ⟨ inj₂(σ' , l' , 𝒮') ⟩
            → ⟨ inj₁ ( ⟨ S ⟩ , σ , l , (ℰ ∷ 𝒮) ) ⟩⇒Sₐ⟨ inj₂ (σ' , l' , 𝒮) ⟩

    SKIP :  ∀ {σ l ℰ}
            → ⟨ inj₁ (skip , σ , l , ℰ) ⟩⇒Sₐ⟨ inj₂ (σ , l , ℰ) ⟩

    ASS-E : ∀ {m e e' σ σ' l l' 𝒮 𝒮' }
            → ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ e' , σ' , l' , 𝒮' ⟩
            → ⟨ m ← e , σ , l , 𝒮 ⟩⇒S⟨ m ← e' , σ' , l' , 𝒮' ⟩

    ASS-M : ∀ {m m' v σ σ' l l' 𝒮 𝒮' ℰ}
            → ⟨ m , σ , l , 𝒮 ⟩⇒M⟨ m' , σ' , l' , 𝒮' ⟩
            → ⟨ m ← (inj₂ v) , σ , l , (ℰ ∷ 𝒮) ⟩⇒S⟨ m' ← (inj₂ v) , σ' , l' , 𝒮' ⟩

    -- TODO
    ASS   : ∀ {m v σ σ' l 𝒮 ℰ ℰ' }
            → σ' ≡ σ [ m ↦ₛ v ]
            → ⟨ inj₁( (inj₂ m) ← (inj₂ v) , σ , l , (ℰ ∷ 𝒮)) ⟩⇒Sₐ⟨ inj₂(σ' , nxt l , (ℰ' ∷ 𝒮))⟩

    WHILE : ∀ {e S σ l 𝒮}
            → ⟨ while e dø S , σ , l , 𝒮 ⟩⇒S⟨ if e then while e dø S else skip , σ , l , 𝒮 ⟩

    COMP-S1 :   ∀ {S₁ S₁´ S₂ σ σ' l l' 𝒮 𝒮'}
                → ⟨ S₁      , σ , l , 𝒮 ⟩⇒S⟨ S₁´      , σ' , l' , 𝒮' ⟩
                → ⟨ S₁ ⍮ S₂ , σ , l , 𝒮 ⟩⇒S⟨ S₁´ ⍮ S₂ , σ' , l' , 𝒮' ⟩

    COMP :  ∀ {S₁ S₂ σ σ' l l' 𝒮 𝒮'}
            → ⟨ inj₁ (S₁ , σ , l , 𝒮) ⟩⇒Sₐ⟨ inj₂(σ' , l' , 𝒮') ⟩
            → ⟨ S₁ ⍮ S₂ , σ , l , 𝒮 ⟩⇒S⟨ S₂ , σ' , l' , 𝒮' ⟩

--    ASS-E1 :    ∀ { e₁ e₁' e₂ l l' ℰ ℰₗ σ σ'}
--                → ℰ ⊢⟨ e₁ , σ , l ⟩⇒E⟨ e₁' , σ' , l' ⟩
--                → ⟨ inj₁ (e₂ ← e₁) , σ , l , ℰ ∷ ℰₗ ⟩⇒S⟨ inj₁ (e₂ ← e₁') , σ' , l' , ℰ ∷ ℰₗ ⟩ -- (ℰ´ , (σ´ [ l ↦ₛ v ]))
--
--    ASS-E2 :    ∀ { v e₂ e₂' l l' ℰ ℰₗ σ σ'}
--                → ℰ ⊢⟨ e₂ , σ , l ⟩⇒E⟨ e₂' , σ' , l' ⟩
--                → ⟨ inj₁ (e₂ ← (inj₂ v)) , σ , l , ℰ ∷ ℰₗ ⟩⇒S⟨ inj₁ (e₂' ← (inj₂ v)) , σ' , l' , ℰ ∷ ℰₗ ⟩ -- (ℰ´ , (σ´ [ l ↦ₛ v ]))
--
--    ASS-DEREF-E :   ∀ {n e v l l' ℰ ℰₗ ℰ' σ σ'}
--                    → ℰ ⊢⟨ inj₁ e , {! ℰ  !} , {!   !} ⟩⇒E⟨ {!   !} , {!   !} ⟩
--                    → ⟨ inj₁ ((inj₁ deref e n) ← (inj₂ v)) , σ , l , ℰ ∷ ℰₗ ⟩⇒S⟨ inj₂ emptyObj , σ' , l' , ℰ ∷ ℰₗ ⟩ -- (ℰ´ , (σ´ [ l ↦ₛ v ]))
--
--    ASS-DEREF : ∀ {n e v l l' ℰ ℰₗ ℰ' σ σ'}
--                → ℰ ⊢⟨ {!   !} , {!   !} ⟩⇒E⟨ {!   !} , {!   !} ⟩
--                → lookupₑ ℰ n ≡ just l
--                → σ' ≡ (σ' [ {!   !} ↦ₛ {!   !} ])
--                → ⟨ inj₁ ((inj₁ deref {!   !} n) ← (inj₂ v)) , σ , l , ℰ ∷ ℰₗ ⟩⇒S⟨ inj₂ emptyObj , σ' , l' , ℰ ∷ ℰₗ ⟩ -- (ℰ´ , (σ´ [ l ↦ₛ v ]))
--
--    ASS-NAME :  ∀ {n v l ℰ ℰₗ σ any}
--                → lookupₑ ℰ n ≡ just any
--                → ⟨ inj₁ ((inj₁ (X n)) ← (inj₂ v)) , σ , l , ℰ ∷ ℰₗ ⟩⇒S⟨ inj₂ emptyObj , σ [ l ↦ₛ v ] , suc l , (ℰ [ n ↦ₑ l ]) ∷ ℰₗ ⟩ -- (ℰ´ , (σ´ [ l ↦ₛ v ]))
--
--
--    ASS-LIST-E1 :  ∀ {x e v l l' ℰ ℰₗ ℰ' σ σ'}
--                → ℰ ⊢⟨ {! inj₁_  !} , {!   !} ⟩⇒E⟨ {!   !} , {!   !} ⟩
--                → lookupₑ ℰ' x ≡ just l
--                → σ' ≡ (σ' [ {!   !} ↦ₛ {!   !} ])
--                → ⟨ inj₁ ((inj₁ ({! e  !} [ {!   !} ])) ← (inj₂ v)) , σ , l , ℰ ∷ ℰₗ ⟩⇒S⟨ inj₂ emptyObj , σ' , l' , ℰ ∷ ℰₗ ⟩ -- (ℰ´ , (σ´ [ l ↦ₛ v ]))
--
--    ASS-LIST-E2 :  ∀ {x e v l l' ℰ ℰₗ ℰ' σ σ'}
--                → ℰ ⊢⟨ {! inj₁_  !} , {!   !} ⟩⇒E⟨ {!   !} , {!   !} ⟩
--                → ⟨ inj₁ ((inj₁ ({! e  !} [ {!   !} ])) ← (inj₂ v)) , σ , l , ℰ ∷ ℰₗ ⟩⇒S⟨ inj₂ emptyObj , σ' , l' , ℰ ∷ ℰₗ ⟩ -- (ℰ´ , (σ´ [ l ↦ₛ v ]))
--
--    ASS-LIST :  ∀ {x e v l l' ℰ ℰₗ ℰ' σ σ'}
--                → ℰ ⊢⟨ {! inj₁_  !} , {!   !} ⟩⇒E⟨ {!   !} , {!   !} ⟩
--                → lookupₑ ℰ' x ≡ just l
--                → σ' ≡ (σ' [ {!   !} ↦ₛ {!   !} ])
--                → ⟨ inj₁ ((inj₁ ({! e  !} [ {!   !} ])) ← (inj₂ v)) , σ , l , ℰ ∷ ℰₗ ⟩⇒S⟨ inj₂ emptyObj , σ' , l' , ℰ ∷ ℰₗ ⟩ -- (ℰ´ , (σ´ [ l ↦ₛ v ]))
--
--    DEF-E : ∀ {x e e' l l' ℰ ℰₗ σ σ'}
--            → ℰ ⊢⟨ e , σ , l ⟩⇒E⟨ e' , σ' , l' ⟩
--            → ⟨ inj₁ (x ← e) , σ , l , ℰ ∷ ℰₗ ⟩⇒S⟨ inj₁ (x ← e') , σ' , l' , ℰ ∷ ℰₗ ⟩ -- (ℰ´ , (σ´ [ l ↦ₛ v ]))
--
--    DEF :   ∀ {x v l l' ℰ ℰₗ σ σ'}
--            → ⟨ inj₁ (x ← (inj₂ v)) , σ , l , ℰ ∷ ℰₗ ⟩⇒S⟨ inj₂ (emptyObj [ x ↦ v ]) , σ' , l' , ℰ ∷ ℰₗ ⟩ -- (ℰ´ , (σ´ [ l ↦ₛ v ]))
--
--    WHILE : ∀ {e S σ l ℰ}
--            → ⟨ inj₁ while e dø S , σ , l , ℰ  ⟩⇒S⟨ inj₁ if inj₁ e then while e dø S else skip , σ , l , ℰ ⟩
--
--    APPLY-E : ∀ {e e' n σ σ' l l' ℰ ℰₗ}
--            → ℰ ⊢⟨ inj₁ e , σ , l ⟩⇒E⟨ e' , σ' , l' ⟩
--            → ⟨ inj₁ apply (inj₁ e) (inj₂ n) , σ , l , ℰ ∷ ℰₗ ⟩⇒S⟨ inj₁ apply e' (inj₂ n) , σ' , l ,  ℰ ∷ ℰₗ ⟩
--
--    APPLY-S :   ∀ {S S' Lₒ σ σ' l l' ℰ ℰ'}
--                → ⟨ S , σ , l , ℰ ⟩⇒S⟨ S' , σ' , l' , ℰ' ⟩
--                → ⟨ inj₁ apply (inj₂ Lₒ) S , σ , l , ℰ ⟩⇒S⟨ inj₁ apply (inj₂ Lₒ) S' , σ' , l' , ℰ' ⟩
--
--    APPLY : ∀ {Lₒ o n σ σ' l ℰ}
--            → just (object o) ≡ lookupₛ σ Lₒ
--            → σ' ≡ σ [ Lₒ ↦ₛ object (joinOverwrite o n) ]
--            → ⟨ inj₁ apply (inj₂ ref Lₒ) (inj₂ n) , σ , l , ℰ ⟩⇒S⟨ inj₂ emptyObj , σ' , l , ℰ ⟩
--
--    IF-T-S :    ∀ {S₁' S₁ S₂ σ σ' l l' ℰ ℰ'}
--                → ⟨                       inj₁ S₁          , σ , l , ℰ ⟩⇒S⟨ inj₁ S₁' , σ' , l' , ℰ' ⟩
--                → ⟨ inj₁ (if inj₂ bool tt then S₁ else S₂) , σ , l , ℰ ⟩⇒S⟨ inj₁ S₁  , σ' , l' , ℰ  ⟩

--    IF-F :  ∀ {s s´ e S₁ S₂ l}
--            → (isExpFalse : l ⟨ inj₁ (e , s) ⟩⇒E⟨ inj₂ (bool ff , s´) ⟩)
--            → ⟨ inj₁ ((if e then S₁ else S₂) , s)
--                ⟩⇒S⟨ inj₁ (S₂ , s´) ⟩

--    DEC :   ∀ {x e v L L´ ℰ ℰ´ σ σ´ l}
--            → l ⟨ inj₁ (e , ((ℰ , σ) , L)) ⟩⇒E⟨ inj₂ (v , ((ℰ´ , σ´) , L´)) ⟩
--            → ⟨ inj₁ ((x ← e) , ((ℰ , σ) , ((ℰ , σ) ∷ L))) ⟩⇒S⟨ inj₂ ((ℰ´ , (σ´ [ nxt l ↦ₛ v ])) , L´) ⟩ -- Needs to update in a specific scope
--
--
--    -- Cannot be done till functions are defined
--    -- RET : ∀ {s e} → ⟨ inj₁ ((return e) , s) ⟩⇒S⟨ inj₂ {! evaluated e !} ⟩
--
--    APP :   ∀ {l σ σ´ σ˝ ℰ v v´- e S L L´ L˝} -- the - means it's ignored, like what _ is usually for
--            → l ⟨ inj₁ (e , (ℰ , σ) , L) ⟩⇒E⟨ inj₂ (component v , (ℰ , σ´) , L´) ⟩ -- TODO state in s´ should be able to be acessed from S, unless it's context overwrites it ofc. It's basically dynamic scope inside a static scope :p -- Should the env be the same here in result and input?
--            → ⟨ inj₁ (S , (v , σ´) , L´) ⟩⇒S⟨ inj₂ ((v´- , σ˝) , L˝) ⟩ -- Execute S with the v environment
--            → ⟨ inj₁ ((apply e S) , (ℰ , σ) , L) ⟩⇒S⟨ inj₂ ((ℰ , σ˝) , L˝) ⟩
--
--    CALL :  ∀{f argsExpr varList S s s´ argsListAsStmts} -- f needs to be read from env to get loc, then get val from loc, then see if that val is a function with correct argument count, and make sure it can return something
--            → argsToVars argsExpr varList ≡ just argsListAsStmts
--            → ⟨ inj₁ (argsListAsStmts ⍮ S , s) ⟩⇒S⟨ inj₂ s´ ⟩
--            → ⟨ inj₁ ((f ⟨ argsExpr ⟩ S) , s) ⟩⇒S⟨ inj₂ s´ ⟩
---- TODO assign v´ to be inside env

data ⟨_⟩⇒M⟨_⟩ where

    VAR :   ∀ {x σ l L ℰ 𝒮}
            → just L ≡ lookupₑ ℰ x
            → ⟨ inj₁ last x , σ , l , ℰ ∷ 𝒮 ⟩⇒M⟨ inj₂ L , σ , l , 𝒮 ⟩

    INDEX-E1 :  ∀ {e₁ e₁' e₂ σ l 𝒮 σ' l' 𝒮'}
                → ⟨ e₁ , σ , l , 𝒮 ⟩⇒E⟨ e₁' , σ' , l' , 𝒮' ⟩
                → ⟨ inj₁ (e₁ [ e₂ ]ₘ) , σ , l , 𝒮 ⟩⇒M⟨ inj₁ (e₁' [ e₂ ]ₘ) , σ' , l' , 𝒮' ⟩

    INDEX-E2 :  ∀ {v e e' σ l 𝒮 σ' l' 𝒮'}
                → ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ e' , σ' , l' , 𝒮' ⟩
                → ⟨ inj₁ (v [ e ]ₘ) , σ , l , 𝒮 ⟩⇒M⟨ inj₁ (v [ e' ]ₘ) , σ' , l' , 𝒮' ⟩

--    INDEX : ∀ {v i L σ l 𝒮 σ' l' 𝒮'}
--            → ⟨ inj₁ ((inj₂ {!   !}) [ inj₂ (int i) ]) , σ , l , 𝒮 ⟩⇒M⟨ inj₂ L , σ' , l' , 𝒮' ⟩


-- Examples

module example-1 where

    one two three : ST₁
    one = while inj₁ ((inj₂(bool ff)) == (inj₂(bool ff))) dø ⟨ (inj₁ (last "x")) ← (inj₂ (bool tt)) ⟩ ⍮ skip , emptyStore , 0 , emptyEnv ∷ []
    two = if inj₁ ((inj₂(bool ff)) == (inj₂(bool ff))) then (while inj₁ ((inj₂(bool ff)) == (inj₂(bool ff))) dø ⟨ ((inj₁ (last "x")) ← (inj₂ (bool tt))) ⟩) else skip ⍮ skip , emptyStore , 0 , emptyEnv ∷ []
    three = if inj₂ (bool tt) then (while inj₁ ((inj₂(bool ff)) == (inj₂(bool ff))) dø ⟨ ((inj₁ (last "x")) ← (inj₂ (bool tt))) ⟩) else skip ⍮ skip , emptyStore , 0 , emptyEnv ∷ []
    step0 : ⟨ one ⟩⇒S⟨ two  ⟩
    step0 = COMP-S1 WHILE

    step1 : ⟨ two ⟩⇒S⟨ three ⟩
    step1 = COMP-S1 (IF-E (OP ⊕==))

--    step1 : ⟨ p1 , emptyStore , 0 , [] ⟩⇒S⟨ if inj₁ ((b ff) == (b ff)) then (while inj₁ ((b ff) == (b ff)) dø ⟨ ((inj₁ (last "x")) ← (inj₂ (bool tt))) ⟩) else skip ⍮ skip , emptyStore , 0 , [] ⟩
--    step0 = COMP-S1 WHILE


    --case-study : (Stmt × State) ⊎ State
    --case-study = inj₁ ((
    --        "x" ← (i (+ℤ 1)) ⍮
    --        "y" ← (i (+ℤ 2)) ⍮
    --        fn "f" ⟨ [] ⟩ (
    --            "x" ← (i (+ℤ 5)) ⍮
    --            "y" ↩ (X ("x" , []))
    --        ) ⍮
    --        (("f" ∷ []) ⟨ [] ⟩ skip) ⍮
    --        ("x" ↩ ((X ("x" , [])) + (X ("y" , [])))) ⍮
    --        skip
    --    ) , ((([] , sortedNilₑ) , ([] , sortedNilₛ)) , []))

    --case-study-result : (Stmt × State) ⊎ State
    --case-study-result =
    --    inj₂ ((
    --        ((("x" , 0) ∷ ("y" , 1) ∷ ("f" , 2) ∷ []) , {!   !}) ,
    --        ((0 , int (+ℤ 6)) ∷ {!   !} ∷ {!   !}) , {!   !}
    --    ), [])
    --    6

    --ℰ : Envᵥ
    --ℰ "x" = just (loc 0)
    --ℰ "y" = just (loc 1)
    --ℰ "z" = just (loc 1)
    --ℰ x = nothing

    --σ : Sto
    --σ (loc 0) = just (int (+ℤ 5))
    --σ (loc 1) = just (int (+ℤ 2))
    --σ x = nothing
