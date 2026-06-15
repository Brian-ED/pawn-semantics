open import Data.Bool using (Bool; _∧_) renaming (true to tt; false to ff)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.Core using (Rel)
open import Level using (0ℓ)

module BoardGame
    (Var : Set) -- Var is an implementation defined set
    (_<ₛ_ : Rel Var 0ℓ)
    (_<?ₛ_ : Decidable _<ₛ_)
    (_==ₛ_ : Var → Var → Bool)
    where

-- TODO
--
-- Prove:
--  1.  (a ; (b ; c) ) == ((a ; b) ; c )
--  2.  Two lists cannot contain the same reference

open import Data.Integer using (ℤ) renaming (+_ to +ℤ_; _+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _<_ to _<ℤ_)
open import Data.String using (String) renaming (length to strLen; _==_ to _==ₛₜᵣ_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
open import Relation.Unary using (Pred; Decidable)
open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
open import BigAndSmallStepSemantics using (⌈>; BigStepSemantics)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤) renaming (tt to ttt)
open import Relation.Nullary.Negation using (¬_)
open import Data.Maybe using (Maybe; _>>=_; map; just; nothing)
open import Data.Sum using (_⊎_) renaming (inj₁ to inj₁_; inj₂ to inj₂_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
open import Data.List using (_∷_; []; length; lookup; updateAt) renaming (List to ListAny)
open import Data.Float using (Float) renaming (_≡ᵇ_ to _==ᶠ_)
open import Data.Fin using (Fin; toℕ)
open import Data.Vec using (Vec; toList; fromList)
import State as Dict
open import Data.Nat using (suc; _^_) renaming (_<_ to _<ₙ_; _<?_ to _<?ₙ_; _≡ᵇ_ to _==ₙ_)
open import Data.Bool using (_∨_)

data 𝕍 : Set
data Stmt : Set
data PosArgDecl : Set
data NamedArg : Set
data Expr : Set
data Member : Set

infixr 5 _⍮_
infixr 6 while_dø_
infixr 6 if_then_else_
infixr 6 apply_dø_
infixr 6 fn_⟨_,_⟩_
infixr 6 return_
infixr 6 _←_
infixr 6 expr_

infixr 4 _==ᵥ_
infixr 4 _𝕍==_
infixr 4 _==ᵢ_

syntax ⟨⟩⇒S⟨⟩1 IN OUT = ⟨ IN ⟩⇒S⟨ OUT ⟩
syntax ⟨⟩⇒E⟨⟩1 IN OUT = ⟨ IN ⟩⇒E⟨ OUT ⟩


data Loc : Set where
    NULL : Loc
    nxt_ : (L : Loc) → Loc

module locNatEquivalence where

    locToNat : Loc → ℕ
    locToNat NULL = 0
    locToNat (nxt x) = suc (locToNat x)

    locFromNat : ℕ → Loc
    locFromNat ℕ.zero = NULL
    locFromNat (suc x) = nxt locFromNat x

    leftInv : ∀ {x} → locFromNat (locToNat x) ≡ x
    leftInv {NULL} = refl
    leftInv {nxt x} = cong nxt_ leftInv

    rightInv : ∀ {x} → locToNat (locFromNat x) ≡ x
    rightInv {ℕ.zero} = refl
    rightInv {suc x} = cong suc rightInv

open locNatEquivalence using (locToNat; locFromNat)

open Dict 𝕍 ℕ _<ₙ_ _<?ₙ_ _==ₙ_ using (_⊢_==ₛ_) renaming
    (_[_↦_]     to _[_↦ₛ_]
    ;lookup     to lookupₛ
    ;State      to Store
    ;emptyState to emptyStore
    ;sortedNil  to sortedNilₛ
    ;sortedCons to sortedConsₛ
    ;sortedOne  to sortedOneₛ
    )

open Dict Loc Var _<ₛ_ _<?ₛ_ _==ₛ_ using () renaming
    (_[_↦_]     to _[_↦ₑ_]
    ;lookup     to lookupₑ
    ;State      to Var⇀Loc
    ;emptyState to Æ
    ;sortedNil  to sortedNilₑ
    ;sortedCons to sortedConsₑ
    ;sortedOne  to sortedOneₑ
    ;_⊢_==ₛ_    to _⊢_==ₑ_
    )

open Dict Expr Var _<ₛ_ _<?ₛ_ _==ₛ_ using () renaming
    (State   to Var⇀Expr
    ;_⊢_==ₛ_ to _⊢_==ₑₓ_
    )

ExprList = ListAny Expr

data Int : Set where
    nonNeg_ : Fin (2 ^ 63) → Int
    -⟨_+1⟩  : Fin (2 ^ 63) → Int

data Sorted : ListAny Var → Set where
    sortedNil  : Sorted []
    sortedOne  : ∀ {x} → Sorted (x ∷ [])
    sortedCons : ∀ {s1 s2 xs}
               → s1 <ₛ s2
               → Sorted (s2 ∷ xs)
               → Sorted (s1 ∷ s2 ∷ xs)

Stack = ListAny Var⇀Loc

module StackEquivalence where
    data LocalStack : Set where
        ⍴ : LocalStack
        _,Stack_ : (𝒮 : LocalStack) → (ℰ : Var⇀Loc) → LocalStack

    mapTo : Stack → LocalStack
    mapTo [] = ⍴
    mapTo (x ∷ x₁) = (mapTo x₁) ,Stack x

    mapFrom : LocalStack → Stack
    mapFrom ⍴ = []
    mapFrom (x ,Stack ℰ) = ℰ ∷ mapFrom x

    leftInv : ∀ {x} → mapFrom (mapTo x) ≡ x
    leftInv {[]} = refl
    leftInv {x ∷ x₁} = cong (x ∷_) (leftInv {x₁})

    rightInv : ∀ {x} → mapTo (mapFrom x) ≡ x
    rightInv {⍴} = refl
    rightInv {x ,Stack ℰ} = cong (_,Stack ℰ) (rightInv {x})

ψ : Var → Stack → Maybe Loc
ψ x [] = nothing
ψ x (ℰ ∷ 𝒮) with lookupₑ ℰ x
... | just ℰ⟨x⟩ = just ℰ⟨x⟩
... | nothing = ψ x 𝒮

PrimFunction = Loc × ℕ × Σ (ListAny Var) Sorted
UserFunction = Stack × ListAny Var × Σ ℕ (λ m → Vec Var m × Vec Expr m) × Stmt

data Function : Set where
    primFunction : (fₚ : PrimFunction) → Function
    userFunction : (fᵤ : UserFunction) → Function

data 𝕍 where
    ref_   : (l : Loc     ) → 𝕍
    bool_  : (b : Bool    ) → 𝕍
    int_   : (i : Int     ) → 𝕍
    float_ : (F : Float   ) → 𝕍
    str_   : (s : String  ) → 𝕍
    obj_   : (ℰ : Var⇀Loc ) → 𝕍
    list_  : {n : Fin (2 ^ 63)} → (σ : Vec Loc (toℕ n)) → 𝕍
    func_  : (f : Function) → 𝕍

data 𝕍C : Set where
    refC_   : (l : Loc    ) → 𝕍C
    boolC_  : (b : Bool   ) → 𝕍C
    intC_   : (i : Int    ) → 𝕍C
    floatC_ : (F : Float  ) → 𝕍C
    strC_   : (s : String ) → 𝕍C

data Stmt where
    _⍮_           : (S1 : Stmt) → (S2 : Stmt) → Stmt
    skip          : Stmt
    if_then_else_ : (e : Expr) → (S1 : Stmt) → (S2 : Stmt) → Stmt
    while_dø_     : (e : Expr) → (S : Stmt) → Stmt
    fn_⟨_,_⟩_     : (x : Var) → (P : PosArgDecl) → (O : NamedArg) → (S : Stmt) → Stmt
    return_       : (e : Expr) → Stmt
    return·       : Stmt
    apply_dø_     : (e : Expr) → (S : Stmt) → Stmt
    ⟨_⟩           : (S : Stmt) → Stmt
    _←_           : (m : Member) → (e : Expr) → Stmt
    expr_         : (e : Expr) → Stmt

data Expr where
    _==_       : (e₁ : Expr) → (e₂ : Expr) → Expr
    _!=_       : (e₁ : Expr) → (e₂ : Expr) → Expr
    _<=_       : (e₁ : Expr) → (e₂ : Expr) → Expr
    _>=_       : (e₁ : Expr) → (e₂ : Expr) → Expr
    _<_        : (e₁ : Expr) → (e₂ : Expr) → Expr
    _>_        : (e₁ : Expr) → (e₂ : Expr) → Expr
    _··=_      : (e₁ : Expr) → (e₂ : Expr) → Expr
    _··_       : (e₁ : Expr) → (e₂ : Expr) → Expr
    _+_        : (e₁ : Expr) → (e₂ : Expr) → Expr
    _-_        : (e₁ : Expr) → (e₂ : Expr) → Expr
    _*_        : (e₁ : Expr) → (e₂ : Expr) → Expr
    _/_        : (e₁ : Expr) → (e₂ : Expr) → Expr
    _│_        : (e₁ : Expr) → (e₂ : Expr) → Expr
    _&_        : (e₁ : Expr) → (e₂ : Expr) → Expr
    _%_        : (e₁ : Expr) → (e₂ : Expr) → Expr
    _[_,_]f_   : (e  : Expr) → (E  : ExprList) → (O : NamedArg) → (S : Stmt) → Expr -- Call
    [_]        : (E  : ExprList) → Expr
    stackframe : (𝒮  : Stack) → (S : Stmt) → Expr
    value_     : (v  : 𝕍) → Expr

data PosArgDecl where
    arg_ : (x : Var) → PosArgDecl
    _,arg_ : (x : Var) → (P : PosArgDecl) → PosArgDecl

data NamedArg where
    ε : NamedArg
    _←_,O_ : (x : Var) → (e : Expr) → (O : NamedArg) → NamedArg

data Member where
    name_ : (x : Var) → Member
    _deref_ : (e : Expr) → (x : Var) → Member
    _[_,_]ᵢ : (e₁ : Expr) → (e₂ : Expr) → (E : ExprList) → Member
    locM_ : (L : Loc) → Member

σ∘ℰ_ : {ℰ : Var⇀Loc} → {σ : Store} → Var → Maybe 𝕍
σ∘ℰ_ {ℰ} {σ} x = lookupₑ ℰ x >>= λ x → lookupₛ σ (locToNat x)

module _
    (Call : (Loc × ListAny 𝕍 × Σ ℕ (λ m → Vec Var m × Vec 𝕍 m) × Stack × Var⇀Loc) → Maybe (Stack × 𝕍C))
    where
    -- TODO


Γₑ₁ = Expr × Store × Loc × Stack
Γₑ₂ = Expr × ListAny Expr × Stack × Store × Loc × Stack

data Γₑ : Set where
    ₑ₁ : Γₑ₁ → Γₑ
    funcTransitions : Γₑ₂ → Γₑ

data ⟨_⟩⇒Eₐ⟨_⟩ : Γₑ → Γₑ → Set

⟨⟩⇒E⟨⟩1 : (IN : Γₑ₁) → (OUT : Γₑ₁) → Set
⟨⟩⇒E⟨⟩1 x y = ⟨ ₑ₁ x ⟩⇒Eₐ⟨ ₑ₁ y ⟩


Γₛ₁ = Stmt × Store × Loc × ListAny Var⇀Loc
Γₛ₂ = Store × Loc × ListAny Var⇀Loc

data Γₛ : Set where
    ₛ₁ : Γₛ₁ → Γₛ
    final : Γₛ₂ → Γₛ


data ⟨_⟩⇒Sₐ⟨_⟩ : (IN : Γₛ) → (OUT : Γₛ) → Set

⟨⟩⇒S⟨⟩1 : (IN : Γₛ₁) → (OUT : Γₛ₁) → Set
⟨⟩⇒S⟨⟩1 x y = ⟨ ₛ₁ x ⟩⇒Sₐ⟨ ₛ₁ y ⟩


Γₘ = Member × Store × Loc × Stack

data ⟨_⟩⇒M⟨_⟩ : Γₘ → Γₘ → Set

data OpType : Set where
    ⊕+ ⊕- ⊕* ⊕/ ⊕% ⊕··= ⊕·· ⊕== ⊕!= ⊕> ⊕< ⊕>= ⊕<= : OpType

getOp : OpType → Expr → Expr → Expr
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
nonNeg x₁ ==ᵢ nonNeg x₂ = toℕ x₁ ==ₙ toℕ x₂
-⟨ x₁ +1⟩ ==ᵢ -⟨ x₂ +1⟩ = toℕ x₁ ==ₙ toℕ x₂
nonNeg _ ==ᵢ -⟨ _ +1⟩ = ff
-⟨ _ +1⟩ ==ᵢ nonNeg _ = ff

_==ᵥ_ : ListAny Loc → ListAny Loc → Bool
[]        ==ᵥ []        = tt
(x₁ ∷ σ₁) ==ᵥ (x₂ ∷ σ₂) = (locToNat x₁ ==ₙ locToNat x₂) ∨ (σ₁ ==ᵥ σ₂)
_ ==ᵥ _ = ff

_𝕍==_ : 𝕍 → 𝕍 → 𝕍
obj ℰ₁    𝕍== obj ℰ₂ = bool ((λ l₁ l₂ → locToNat l₁ ==ₙ locToNat l₂) ⊢ ℰ₁ ==ₑ ℰ₂)
float f₁  𝕍== float f₂  = bool (f₁ ==ᶠ f₂)
int i₁    𝕍== int i₂    = bool (i₁ ==ᵢ i₂)
str s₁    𝕍== str s₂    = bool (s₁ ==ₛₜᵣ s₂)
list σ₁   𝕍== list σ₂   = bool (toList σ₁ ==ᵥ toList σ₂)
bool ff   𝕍== bool ff   = bool tt
bool tt   𝕍== bool tt   = bool tt
ref l₁    𝕍== ref l₂    = bool (locToNat l₁ ==ₙ locToNat l₂)
obj _    𝕍== _ = bool ff
float _  𝕍== _ = bool ff
int _    𝕍== _ = bool ff
str _    𝕍== _ = bool ff
list _   𝕍== _ = bool ff
bool _   𝕍== _ = bool ff
ref _    𝕍== _ = bool ff
func userFunction _ 𝕍== _ = bool ff
func primFunction _ 𝕍== _ = bool ff

-- TODO
--_[_]ₐ_ : 𝕍 → OpType → 𝕍 → 𝕍
--x₁ [ ⊕==  ]ₐ x₂ = x₁ 𝕍== x₂
--x₁ [ ⊕!=  ]ₐ x₂ = x₁
--x₁ [ ⊕>   ]ₐ x₂ = x₁
--x₁ [ ⊕<   ]ₐ x₂ = x₁
--x₁ [ ⊕>=  ]ₐ x₂ = x₁
--x₁ [ ⊕<=  ]ₐ x₂ = x₁
--x₁ [ ⊕+   ]ₐ x₂ = x₁
--x₁ [ ⊕-   ]ₐ x₂ = x₁
--x₁ [ ⊕*   ]ₐ x₂ = x₁
--x₁ [ ⊕/   ]ₐ x₂ = x₁
--x₁ [ ⊕%   ]ₐ x₂ = x₁
--x₁ [ ⊕··= ]ₐ x₂ = x₁
--x₁ [ ⊕··  ]ₐ x₂ = x₁

data ⟨_⟩⇒Eₐ⟨_⟩ where
--    OP :    ∀ {v₁ v₂ σ l 𝒮}
--            → (⊕ : OpType)
--            → ⟨(inj₁ ((getOp ⊕) (inj₂ v₁) (inj₂ v₂))) , σ , l , 𝒮 ⟩⇒E⟨ (inj₂ (v₁ [ ⊕ ]ₐ v₂)) , σ , l , 𝒮 ⟩

data ⟨_⟩⇒Sₐ⟨_⟩ where

--    IF-E :  ∀ {S₁ S₂ e e' σ σ' l l' 𝒮 }
--            → ⟨    e                 , σ , l , 𝒮 ⟩⇒E⟨    e'                 , σ' , l' , 𝒮 ⟩
--            → ⟨ if e then S₁ else S₂ , σ , l , 𝒮 ⟩⇒S⟨ if e' then S₁ else S₂ , σ' , l' , 𝒮 ⟩

--    IF-T :  ∀ {S₁ S₂ σ l 𝒮}
--            → ⟨ if (inj₂ (bool tt)) then S₁ else S₂ , σ , l , 𝒮 ⟩⇒S⟨ ⟨ S₁ ⟩ , σ , l , 𝒮 ⟩
--
--    IF-F :  ∀ {S₁ S₂ σ l 𝒮}
--            → ⟨ if (inj₂ (bool ff)) then S₁ else S₂ , σ , l , 𝒮 ⟩⇒S⟨ ⟨ S₂ ⟩ , σ , l , 𝒮 ⟩
--
--    BLOCK-S :   ∀ {S S' σ σ' l l' 𝒮 𝒮' }
--                → ⟨ S , σ , l , 𝒮 ⟩⇒S⟨ S' , σ' , l' , 𝒮' ⟩
--                → ⟨ ⟨ S ⟩ , σ , l , 𝒮 ⟩⇒S⟨ ⟨ S' ⟩ , σ' , l' , 𝒮' ⟩
--
--    BLOCK : ∀ {S σ σ' l l' 𝒮 𝒮' ℰ }
--            → ⟨ inj₁ (S , σ , l , (ℰ ∷ 𝒮)) ⟩⇒Sₐ⟨ inj₂(σ' , l' , 𝒮') ⟩
--            → ⟨ inj₁ ( ⟨ S ⟩ , σ , l , (ℰ ∷ 𝒮) ) ⟩⇒Sₐ⟨ inj₂ (σ' , l' , 𝒮) ⟩
--
--    SKIP :  ∀ {σ l ℰ}
--            → ⟨ inj₁ (skip , σ , l , ℰ) ⟩⇒Sₐ⟨ inj₂ (σ , l , ℰ) ⟩
--
--    ASS-E : ∀ {m e e' σ σ' l l' 𝒮 𝒮' }
--            → ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ e' , σ' , l' , 𝒮' ⟩
--            → ⟨ m ← e , σ , l , 𝒮 ⟩⇒S⟨ m ← e' , σ' , l' , 𝒮' ⟩
--
--    ASS-M : ∀ {m m' v σ σ' l l' 𝒮 𝒮' ℰ}
--            → ⟨ m , σ , l , 𝒮 ⟩⇒M⟨ m' , σ' , l' , 𝒮' ⟩
--            → ⟨ m ← (inj₂ v) , σ , l , (ℰ ∷ 𝒮) ⟩⇒S⟨ m' ← (inj₂ v) , σ' , l' , 𝒮' ⟩
--
--    -- TODO
--    ASS   : ∀ {m v σ σ' l 𝒮 ℰ ℰ' }
--            → σ' ≡ σ [ m ↦ₛ v ]
--            → ⟨ inj₁( (inj₂ m) ← (inj₂ v) , σ , l , (ℰ ∷ 𝒮)) ⟩⇒Sₐ⟨ inj₂(σ' , nxt l , (ℰ' ∷ 𝒮))⟩
--
--    WHILE : ∀ {e S σ l 𝒮}
--            → ⟨ while e dø S , σ , l , 𝒮 ⟩⇒S⟨ if e then while e dø S else skip , σ , l , 𝒮 ⟩
--
--    COMP-S1 :   ∀ {S₁ S₁´ S₂ σ σ' l l' 𝒮 𝒮'}
--                → ⟨ S₁      , σ , l , 𝒮 ⟩⇒S⟨ S₁´      , σ' , l' , 𝒮' ⟩
--                → ⟨ S₁ ⍮ S₂ , σ , l , 𝒮 ⟩⇒S⟨ S₁´ ⍮ S₂ , σ' , l' , 𝒮' ⟩
--
--    COMP :  ∀ {S₁ S₂ σ σ' l l' 𝒮 𝒮'}
--            → ⟨ inj₁ (S₁ , σ , l , 𝒮) ⟩⇒Sₐ⟨ inj₂(σ' , l' , 𝒮') ⟩
--            → ⟨ S₁ ⍮ S₂ , σ , l , 𝒮 ⟩⇒S⟨ S₂ , σ' , l' , 𝒮' ⟩

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

-- minimum index that is not a number
minIndexNonInt : ∀ {n} → Vec Expr (suc n) → Maybe (Fin (suc n))
minIndexNonInt {ℕ.zero} ((value (int x)) Vec.∷ Vec.[]) = nothing
minIndexNonInt {suc n} ((value (int x)) Vec.∷ x₁) = map Fin.suc (minIndexNonInt x₁)
minIndexNonInt (x Vec.∷ y) = just Fin.zero

exprsAsIndecies : ListAny Expr → Maybe (ListAny (Fin (2 ^ 63)))
exprsAsIndecies [] = just []
exprsAsIndecies (value int nonNeg n ∷ xs) = map (n ∷_) (exprsAsIndecies xs)
exprsAsIndecies (x ∷ x₁) = nothing

massIndex : ListAny (Fin (2 ^ 63)) → (σ : ListAny Loc) → Maybe (ListAny Loc)
massIndex [] xs = just []
massIndex (x ∷ i) xs = {! lookup xs !}

data ⟨_⟩⇒M⟨_⟩ where

--name_ :
--_deref_
--_[_,_]ₘ
--locM_ :

    INDEX-1 :   ∀ {e₁ e₂ E e₁´ σ σ′ l l′ 𝒮 𝒮′}
                → ⟨ e₁ , σ , l , 𝒮 ⟩⇒E⟨ e₁´ , σ′ , l′ , 𝒮′ ⟩
                → ⟨ e₁ [ e₂ , E ]ᵢ , σ , l , 𝒮 ⟩⇒M⟨ e₁´ [ e₂ , E ]ᵢ , σ′ , l′ , 𝒮′ ⟩

    INDEX-2 :   ∀ {E E´ e₁ e₁´ eᵢ´ indexOfExpr L₁ σ σ′ l l′ 𝒮 𝒮′}
                → minIndexNonInt (fromList (e₁ ∷ E)) ≡ just indexOfExpr
                → ⟨ lookup (e₁ ∷ E) indexOfExpr , σ , l , 𝒮 ⟩⇒E⟨ eᵢ´ , σ′ , l′ , 𝒮′ ⟩
                → {updateAt (e₁ ∷ E) indexOfExpr (λ _ → eᵢ´) ≡ e₁´ ∷ E´}
                → ⟨ (value ref L₁) [ e₁ , E ]ᵢ , σ , l , 𝒮 ⟩⇒M⟨ (value ref L₁) [ e₁´ , E´ ]ᵢ , σ′ , l′ , 𝒮′ ⟩

    INDEX-3 :   ∀ {A i j L σ l 𝒮}
                → lookupₛ σ (locToNat L) ≡ just (list A)
                → toℕ i ≡ toℕ j
                → ⟨ (value ref L) [ value int nonNeg i , [] ]ᵢ , σ , l , 𝒮 ⟩⇒M⟨ locM Data.Vec.lookup A j , σ , l , 𝒮 ⟩

    INDEX-4 :   ∀ {e₁ v locs E L σ l 𝒮}
                → lookupₛ σ (locToNat L) ≡ just (list locs)
                → exprsAsIndecies (e₁ ∷ E) ≡ just v
                → ⟨ (value ref L) [ e₁ , E ]ᵢ , σ , l , 𝒮 ⟩⇒M⟨ locM l , σ [ locToNat L ↦ₛ list {!  v !} ] , nxt l , 𝒮 ⟩

    MEMBER-1 :  ∀ {e e´ x σ σ′ l l′ 𝒮 𝒮′}
                → ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ e´ , σ′ , l′ , 𝒮′ ⟩
                → ⟨ e deref x , σ , l , 𝒮 ⟩⇒M⟨ e´ deref x , σ′ , l′ , 𝒮′ ⟩

    MEMBER-2 :  ∀ {O x σ l L 𝒮}
                → lookupₛ σ (locToNat L) ≡ just (obj O)
                → lookupₑ O x ≡ just L
                → ⟨ (value (ref L)) deref x , σ , l , 𝒮 ⟩⇒M⟨ locM L , σ , l , 𝒮 ⟩

    VAR :   ∀ {x σ l L 𝒮}
            → ψ x 𝒮 ≡ just L
            → ⟨ name x , σ , l , 𝒮 ⟩⇒M⟨ locM L , σ , l , 𝒮 ⟩

--    INDEX-E1 :  ∀ {e₁ e₁' e₂ σ l 𝒮 σ' l' 𝒮'}
--                → ⟨ e₁ , σ , l , 𝒮 ⟩⇒E⟨ e₁' , σ' , l' , 𝒮' ⟩
--                → ⟨ inj₁ (e₁ [ e₂ ]ₘ) , σ , l , 𝒮 ⟩⇒M⟨ inj₁ (e₁' [ e₂ ]ₘ) , σ' , l' , 𝒮' ⟩
--
--    INDEX-E2 :  ∀ {v e e' σ l 𝒮 σ' l' 𝒮'}
--                → ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ e' , σ' , l' , 𝒮' ⟩
--                → ⟨ inj₁ (v [ e ]ₘ) , σ , l , 𝒮 ⟩⇒M⟨ inj₁ (v [ e' ]ₘ) , σ' , l' , 𝒮' ⟩

--    INDEX : ∀ {v i L σ l 𝒮 σ' l' 𝒮'}
--            → ⟨ inj₁ ((inj₂ {!   !}) [ inj₂ (int i) ]) , σ , l , 𝒮 ⟩⇒M⟨ inj₂ L , σ' , l' , 𝒮' ⟩


-- Examples

module example-1 where

--    one two three : ST₁
--    one = while inj₁ ((inj₂(bool ff)) == (inj₂(bool ff))) dø ⟨ (inj₁ (name "x")) ← (inj₂ (bool tt)) ⟩ ⍮ skip , emptyStore , 0 , emptyEnv ∷ []
--    two = if inj₁ ((inj₂(bool ff)) == (inj₂(bool ff))) then (while inj₁ ((inj₂(bool ff)) == (inj₂(bool ff))) dø ⟨ ((inj₁ (name "x")) ← (inj₂ (bool tt))) ⟩) else skip ⍮ skip , emptyStore , 0 , emptyEnv ∷ []
--    three = if inj₂ (bool tt) then (while inj₁ ((inj₂(bool ff)) == (inj₂(bool ff))) dø ⟨ ((inj₁ (name "x")) ← (inj₂ (bool tt))) ⟩) else skip ⍮ skip , emptyStore , 0 , emptyEnv ∷ []
--    step0 : ⟨ one ⟩⇒S⟨ two  ⟩
--    step0 = COMP-S1 WHILE

--    step1 : ⟨ two ⟩⇒S⟨ three ⟩
--    step1 = COMP-S1 (IF-E (OP ⊕==))

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

    --ℰ : Var⇀Loc
    --ℰ "x" = just (loc 0)
    --ℰ "y" = just (loc 1)
    --ℰ "z" = just (loc 1)
    --ℰ x = nothing

    --σ : Sto
    --σ (loc 0) = just (int (+ℤ 5))
    --σ (loc 1) = just (int (+ℤ 2))
    --σ x = nothing
