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

open import Data.Integer using (ℤ; _≤ᵇ_) renaming (+_ to +ℤ_; _+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _<_ to _<ℤ_)
open import Data.String using (String) renaming (length to strLen; _==_ to _==ₛₜᵣ_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans; refl)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (yes; no)
open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
open import BigAndSmallStepSemantics using (⌈>; BigStepSemantics)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤) renaming (tt to ttt)
open import Relation.Nullary.Negation using (¬_)
open import Data.Maybe using (Maybe; _>>=_; map; nothing) renaming (just to just_)
open import Data.Sum using (_⊎_) renaming (inj₁ to inj₁_; inj₂ to inj₂_)
open import Data.Product using (_×_; _,_; Σ; ∃; proj₁; proj₂; uncurry)
open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
open import Data.List using (_∷_; []; length; lookup; updateAt) renaming (List to ListAny; map to mapL)
open import Data.Float using (Float) renaming (_≡ᵇ_ to _==ᶠ_)
open import Data.Fin using (Fin; toℕ; fromℕ; fromℕ<; inject; inject≤)
open import Data.Vec using (Vec; unzipWith; unzip; toList; fromList)
open import Function as Func using (_∘_)
import State as Dict
open import Data.Nat using (suc; _^_; s<s; z≤n; s≤s; z<s) renaming (_<_ to _<ₙ_; _≤_ to _≤ₙ_; _<?_ to _<?ₙ_; _≡ᵇ_ to _==ₙ_)
open import Data.Bool using (_∨_) renaming (if_then_else_ to ifB_then_else_)

data 𝕍 : Set
data Stmt : Set
data Expr : Set
data Member : Set

infixr 5 _⍮_
infixr 6 while_dø_
infixr 6 if_then_else_
infixr 6 apply_dø_
infixr 6 fn_⟨_,_⟩_
infixr 6 return_
infixr 6 _←_
infixr 5 _==_

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

open locNatEquivalence using (locToNat; locFromNat) public

PosArgDecl = ListAny Var

open Dict 𝕍 ℕ _<ₙ_ _<?ₙ_ _==ₙ_ using (_⊢_==ₛ_) renaming
    (_[_↦_]     to _[_↦ₛ_]
    ;lookup     to lookupₛ
    ;State      to Store
    ;emptyState to emptyStore
    ;sortedNil  to sortedNilₛ
    ;sortedCons to sortedConsₛ
    ;sortedOne  to sortedOneₛ
    ;joinOverwrite to joinObjOverwrite
    ) public

open Dict Loc Var _<ₛ_ _<?ₛ_ _==ₛ_ using () renaming
    (_[_↦_]     to _[_↦ₑ_]
    ;lookup     to lookupₑ
    ;State      to Var⇀Loc
    ;emptyState to Æ
    ;sortedNil  to sortedNilₑ
    ;sortedCons to sortedConsₑ
    ;sortedOne  to sortedOneₑ
    ;_⊢_==ₛ_    to _⊢_==ₑ_
    ) public

open Dict Expr Var _<ₛ_ _<?ₛ_ _==ₛ_ using () renaming
    (State   to Var⇀Expr
    ;_⊢_==ₛ_ to _⊢_==ₑₓ_
    ) public

ExprList = ListAny Expr

NamedArg = ListAny (Var × Expr)

module namedArgEquivalence where
    data NamedArgOriginal : Set where
        ε : NamedArgOriginal
        _←O_,O_ : (x : Var) → (e : Expr) → (O : NamedArgOriginal) → NamedArgOriginal

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
UserFunction = Stack × ListAny Var × ListAny (Var × Expr) × Stmt

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
    member_     : (m  : Member) → Expr
    value_     : (v  : 𝕍) → Expr


data Member where
    name_ : (x : Var) → Member
    _deref_ : (e : Expr) → (x : Var) → Member
    _[_,_]ᵢ : (e₁ : Expr) → (e₂ : Expr) → (E : ExprList) → Member
    locM_ : (L : Loc) → Member

σ∘ℰ_ : {ℰ : Var⇀Loc} → {σ : Store} → Var → Maybe 𝕍
σ∘ℰ_ {ℰ} {σ} x = lookupₑ ℰ x >>= λ x → lookupₛ σ (locToNat x)

Γₑ₁ = Expr × Store × Loc × Stack
Γₑ₂ = Expr × NamedArg × Stack × Store × Loc × Stack

data Γₑ : Set where
    ₑ₁_ : Γₑ₁ → Γₑ
    funcTransitions_ : Γₑ₂ → Γₑ

data ⟨_⟩⇒Eₐ⟨_⟩ : Γₑ → Γₑ → Set

⟨⟩⇒E⟨⟩1 : (IN : Γₑ₁) → (OUT : Γₑ₁) → Set
⟨⟩⇒E⟨⟩1 x y = ⟨ ₑ₁ x ⟩⇒Eₐ⟨ ₑ₁ y ⟩


Γₛ₁ = Stmt × Store × Loc × ListAny Var⇀Loc
Γₛ₂ = Store × Loc × ListAny Var⇀Loc

data Γₛ : Set where
    ₛ₁_ : Γₛ₁ → Γₛ
    final_ : Γₛ₂ → Γₛ

infix 1 ₛ₁_ ₑ₁_ funcTransitions_
infix 1 final_

data ⟨_⟩⇒Sₐ⟨_⟩ : (IN : Γₛ) → (OUT : Γₛ) → Set

⟨⟩⇒S⟨⟩1 : (IN : Γₛ₁) → (OUT : Γₛ₁) → Set
⟨⟩⇒S⟨⟩1 x y = ⟨ ₛ₁ x ⟩⇒Sₐ⟨ ₛ₁ y ⟩


Γₘ = Member × Store × Loc × Stack

data ⟨_⟩⇒M⟨_⟩ : Γₘ → Γₘ → Set

data SimpleOpType : Set where
    ⊕+ ⊕- ⊕* ⊕/ ⊕% ⊕< ⊕> ⊕<= ⊕>= : SimpleOpType

data OpType : Set where
    ⊙⊕ : SimpleOpType → OpType
    ⊙·· ⊙··= ⊙== ⊙!= ⊙│ ⊙& : OpType

getSimpleOp : SimpleOpType → Expr → Expr → Expr
getSimpleOp ⊕>   = _>_
getSimpleOp ⊕<   = _<_
getSimpleOp ⊕>=  = _>=_
getSimpleOp ⊕<=  = _<=_
getSimpleOp ⊕+   = _+_
getSimpleOp ⊕-   = _-_
getSimpleOp ⊕*   = _*_
getSimpleOp ⊕/   = _/_
getSimpleOp ⊕%   = _%_

getOp : OpType → Expr → Expr → Expr
getOp (⊙⊕ x) = getSimpleOp x
getOp ⊙·· = _··_
getOp ⊙··= = _··=_
getOp ⊙== = _==_
getOp ⊙!= = _!=_
getOp ⊙│ = _│_
getOp ⊙& = _&_

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

IntToℤ_ : Int → ℤ
IntToℤ (nonNeg x) = +ℤ toℕ x
IntToℤ -⟨ x +1⟩ = ℤ.negsuc (toℕ x)

ℤToMaybeInt_ : ℤ → Maybe Int
ℤToMaybeInt +ℤ_ n with n Data.Nat.<? (2 ^ 63)
... | yes p = just nonNeg fromℕ< p
... | no p = nothing
ℤToMaybeInt ℤ.negsuc n with n Data.Nat.<? (2 ^ 63)
... | yes p = just -⟨ fromℕ< p +1⟩
... | no p = nothing

-- TODO
_ₐ : SimpleOpType → 𝕍 → 𝕍 → Maybe 𝕍
--_ₐ op  (float x) (int y) = _ₐ op (float x) (float (Data.Float.fromℤ (IntToℤ y)))
--_ₐ op  (int x) (float y) = _ₐ op (float (Data.Float.fromℤ (IntToℤ x))) (float y)
_ₐ ⊕>  (int x) (int y) = just bool (((+ℤ 1) +ℤ IntToℤ y) ≤ᵇ IntToℤ x)
_ₐ ⊕<  (int x) (int y) = just bool ((((+ℤ 1) +ℤ IntToℤ x) ≤ᵇ IntToℤ y))
_ₐ ⊕>= (int x) (int y) = just bool (IntToℤ y ≤ᵇ IntToℤ x)
_ₐ ⊕<= (int x) (int y) = just bool (IntToℤ x ≤ᵇ IntToℤ y)
_ₐ ⊕+  (int x) (int y) = ℤToMaybeInt (IntToℤ x +ℤ IntToℤ y) >>= just_ ∘ int_
_ₐ ⊕-  (int x) (int y) = ℤToMaybeInt (IntToℤ x -ℤ IntToℤ y) >>= just_ ∘ int_
_ₐ ⊕*  (int x) (int y) = ℤToMaybeInt (IntToℤ x *ℤ IntToℤ y) >>= just_ ∘ int_
_ₐ ⊕/  (int x) (int y) with IntToℤ y Data.Integer.≟ +ℤ 0
... | yes _ = nothing
... | no p = ℤToMaybeInt (Data.Integer._/_ (IntToℤ x) (IntToℤ y) {{Data.Integer.≢-nonZero p}}) >>= just_ ∘ int_
_ₐ ⊕%  (int x) (int y) with IntToℤ y Data.Integer.≟ +ℤ 0
... | yes _ = nothing
... | no p = ℤToMaybeInt (+ℤ (Data.Integer._%_ (IntToℤ x) (IntToℤ y) {{Data.Integer.≢-nonZero p}})) >>= just_ ∘ int_
_ₐ ⊕>  (float x) (float y) = just bool (y Data.Float.<ᵇ x)
_ₐ ⊕<  (float x) (float y) = just bool (x Data.Float.<ᵇ y)
_ₐ ⊕>= (float x) (float y) = just bool (y Data.Float.≤ᵇ x)
_ₐ ⊕<= (float x) (float y) = just bool (x Data.Float.≤ᵇ y)
_ₐ ⊕+  (float x) (float y) = just float (x Data.Float.+ y)
_ₐ ⊕-  (float x) (float y) = just float (x Data.Float.- y)
_ₐ ⊕*  (float x) (float y) = just float (x Data.Float.* y)
_ₐ ⊕/  (float x) (float y) = just float (x Data.Float.÷ y)
_ₐ ⊕%  (float x) (float y) = (Data.Float.⌊ x Data.Float.÷ y ⌋) >>= λ z → just float (x Data.Float.- (Data.Float.fromℤ z) Data.Float.* y)
_ₐ _ _ _ = nothing

variable
    e e´ e˝ e₁ e₁´ e₂ e₂´ eᵢ eᵢ´ eᵢ˝ : Expr
    S S´ S₁ S₁´ S₂ S₂´ : Stmt
    m m´ : Member
    σ σ´ σ˝ : Store
    l l´ l˝ L Lᶠ : Loc
    ℰ ℰ´ : Var⇀Loc
    𝒮 𝒮´ 𝒮˝ 𝒮ₛ : Stack
    x N : Var
    xₙ : PosArgDecl
    v v₁ v₂ : 𝕍
    xₒ=eₒ O : NamedArg
    E E´ : ExprList
    B : Bool
    f f₁ f₂ : Float
    fₚ :  PrimFunction
    fᵤ : UserFunction

_<ᵇI_ : Int → Int → Bool
(nonNeg i₁) <ᵇI (nonNeg i₂) = (toℕ i₁) Data.Nat.<ᵇ (toℕ i₂)
(nonNeg i₁) <ᵇI -⟨ i₂ +1⟩ = Bool.false
-⟨ i₁ +1⟩ <ᵇI (nonNeg i₂) = Bool.true
-⟨ i₁ +1⟩ <ᵇI -⟨ i₂ +1⟩ = (toℕ i₂) Data.Nat.<ᵇ (toℕ i₁)

minIndexNonValue : ∀ {n} → Vec Expr (suc n) → Maybe (Fin (suc n))
minIndexNonValue {ℕ.zero} ((value x) Vec.∷ Vec.[]) = nothing
minIndexNonValue {suc n} ((value x) Vec.∷ x₁) = map Fin.suc (minIndexNonValue x₁)
minIndexNonValue (x Vec.∷ y) = just Fin.zero

exprToLoc : Expr → Maybe Loc
exprToLoc (value ref v) = just v
exprToLoc x = nothing

transfer : {n m : ℕ} → n ≡ m → Vec Loc n → Vec Loc m
transfer refl x = x

cap0 : ℤ → ℕ
cap0 (+ℤ_ n) = n
cap0 (ℤ.negsuc n) = 0

append : {A : Set} → ListAny A → A → ListAny A
append [] a = a ∷ []
append (aᵢ ∷ as) a = aᵢ ∷ (append as a)

𝕍CTo𝕍 : 𝕍C → 𝕍
𝕍CTo𝕍 (refC l) = ref l
𝕍CTo𝕍 (boolC b) = bool b
𝕍CTo𝕍 (intC i) = int i
𝕍CTo𝕍 (floatC F) = float F
𝕍CTo𝕍 (strC s) = str s

data ⟨_⟩⇒Eₐ⟨_⟩ where
    -- TODO OP
    OP-1 :  (⊙ : OpType) →
            ⟨ e₁ , σ , l , 𝒮 ⟩⇒E⟨ e₁´ , σ´ , l´ , 𝒮´ ⟩ →
            ⟨ getOp ⊙ e₁ e₂ , σ , l , 𝒮 ⟩⇒E⟨ getOp ⊙ e₁´ e₂ , σ´ , l´ , 𝒮´ ⟩

    OP-2 :  (⊙ : OpType) →
            ⟨ e₂ , σ , l , 𝒮 ⟩⇒E⟨ e₂´ , σ´ , l´ , 𝒮´ ⟩ →
            ⟨ getOp ⊙ (value v₁) e₂ , σ , l , 𝒮 ⟩⇒E⟨ getOp ⊙ (value v₁) e₂´ , σ´ , l´ , 𝒮´ ⟩

    SIMPLE-OP : (⊕ : SimpleOpType) →
                _ₐ ⊕ v₁ v₂ ≡ just v →
                ⟨ getSimpleOp ⊕ (value v₁) (value v₂) , σ , l , 𝒮 ⟩⇒E⟨ (value v) , σ´ , l´ , 𝒮´ ⟩

    RANGE : ∀ {i₁ i₂}
            → (p : (cap0 ((IntToℤ i₂) -ℤ (IntToℤ i₁))) ≤ₙ 2 ^ 63)
            → ⟨ (value int i₁) ·· (value int i₂) , σ , l , 𝒮 ⟩⇒E⟨ [ Data.List.tabulate {A = Expr} {n = cap0 ((IntToℤ i₂) -ℤ (IntToℤ i₁))} (λ x → (value int i₁) + (value (int (nonNeg (inject≤ x p))))) ] , σ , l , 𝒮 ⟩

    RANGE-INCL : ∀ {i₁ i₂}
            → (p : (cap0 ((+ℤ 1) +ℤ ((IntToℤ i₂) -ℤ (IntToℤ i₁)))) ≤ₙ 2 ^ 63)
            → ⟨ (value int i₁) ··= (value int i₂) , σ , l , 𝒮 ⟩⇒E⟨ [ Data.List.tabulate {A = Expr} {n = (cap0 ((+ℤ 1) +ℤ ((IntToℤ i₂) -ℤ (IntToℤ i₁))))} (λ x → (value int i₁) + (value (int (nonNeg (inject≤ x p))))) ] , σ , l , 𝒮 ⟩


    EQ-BOOL-TRUE :         ⟨ (value bool B) == (value bool B) , σ , l , 𝒮 ⟩⇒E⟨ value bool tt , σ , l , 𝒮 ⟩
    EQ-REF-TRUE  :         ⟨ (value ref  L) == (value ref  L) , σ , l , 𝒮 ⟩⇒E⟨ value bool tt , σ , l , 𝒮 ⟩
    EQ-INT-TRUE  : ∀ {i} → ⟨ (value int  i) == (value int  i) , σ , l , 𝒮 ⟩⇒E⟨ value bool tt , σ , l , 𝒮 ⟩
    EQ-STR-TRUE  : ∀ {s} → ⟨ (value str  s) == (value str  s) , σ , l , 𝒮 ⟩⇒E⟨ value bool tt , σ , l , 𝒮 ⟩

    EQ-FLOAT-1 : ⟨ (value float f₁) == (value float f₂) , σ , l , 𝒮 ⟩⇒E⟨ value bool (f₁ ==ᶠ f₂) , σ , l , 𝒮 ⟩

    EQ-BOOL-FALSE :          (¬ bool  B ≡ v) → ⟨ (value bool  B) == (value v) , σ , l , 𝒮 ⟩⇒E⟨ value bool ff , σ , l , 𝒮 ⟩
    EQ-REF-FALSE  :          (¬ ref   L ≡ v) → ⟨ (value ref   L) == (value v) , σ , l , 𝒮 ⟩⇒E⟨ value bool ff , σ , l , 𝒮 ⟩
    EQ-INT-FALSE  : ∀ {i} →  (¬ int   i ≡ v) → ⟨ (value int   i) == (value v) , σ , l , 𝒮 ⟩⇒E⟨ value bool ff , σ , l , 𝒮 ⟩
    EQ-STR-FALSE  : ∀ {s} →  (¬ str   s ≡ v) → ⟨ (value str   s) == (value v) , σ , l , 𝒮 ⟩⇒E⟨ value bool ff , σ , l , 𝒮 ⟩
    EQ-FLOAT-2    :          (¬ ∃ λ f₂ → float f₂ ≡ v) → ⟨ (value float f) == (value v) , σ , l , 𝒮 ⟩⇒E⟨ value bool ff , σ , l , 𝒮 ⟩

    NOT-EQ : ⟨ (value v₁) != (value v₂) , σ , l , 𝒮 ⟩⇒E⟨ (((value v₁) == (value v₂)) == (value bool ff)) , σ , l , 𝒮 ⟩

    CALL :  ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ e´ , σ´ , l´ , 𝒮´ ⟩ →
            ⟨ e´ , σ´ , l´ , 𝒮´ ⟩⇒E⟨ e˝ , σ˝ , l˝ , 𝒮˝ ⟩ →
            ⟨ e [ E , O ]f S , σ , l , 𝒮 ⟩⇒E⟨ e´ [ E , O ]f S , σ´ , l´ , 𝒮´ ⟩

    CALL-PRIM-1 :   ∀ {n Lf args}
                    → length E ≡ n
                    → lookupₛ σ (locToNat L) ≡ just func primFunction (Lf , n , args)
                    → ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ value ref L , σ´ , l´ , 𝒮´ ⟩
                    → ⟨ e [ E , O ]f S , σ , l , 𝒮 ⟩⇒E⟨ (value ref L) [ E , O ]f S , σ´ , l´ , Æ ∷ 𝒮´ ⟩

    CALL-PRIM-2 :   ∀ {n args index}
                    → (∀ i → ∃ λ v → lookup (Data.List.take (toℕ index) E) i ≡ value v)
                    → lookupₛ σ (locToNat L) ≡ just func primFunction (Lᶠ , n , args)
                    → (∀ i → ∃ λ j → lookup O i .proj₁ ≡ lookup (proj₁ args) j)
                    → ⟨ lookup E index , σ , l , 𝒮 ⟩⇒E⟨ eᵢ´ , σ´ , l´ , 𝒮´ ⟩
                    → ⟨ (value ref L) [ E , O ]f S , σ , l , 𝒮 ⟩⇒E⟨ (value ref L) [ updateAt E index (λ _ → eᵢ´) , O ]f S , σ´ , l´ , 𝒮´ ⟩

    CALL-PRIM-3 :   ∀ {n args index}
                    → (∀ i → ∃ λ v → lookup E i ≡ value v)
                    → (∀ i → ∃ λ v → lookup (Data.List.take (toℕ index) O) i .proj₂ ≡ value v)
                    → lookupₛ σ (locToNat L) ≡ just func primFunction (Lᶠ , n , args)
                    → (∀ i → ∃ λ j → lookup O i .proj₁ ≡ lookup (proj₁ args) j)
                    → ⟨ (lookup O index) .proj₂ , σ , l , 𝒮 ⟩⇒E⟨ eᵢ´ , σ´ , l´ , 𝒮´ ⟩
                    → ⟨ (value ref L) [ E , O ]f S , σ , l , 𝒮 ⟩⇒E⟨ (value ref L) [ E , updateAt O index ((_, eᵢ´) ∘ proj₁) ]f S , σ´ , l´ , 𝒮´ ⟩

    CALL-PRIM-4 :   ∀ {n args}
                    → lookupₛ σ (locToNat L) ≡ just func primFunction (Lᶠ , n , args)
                    → (∀ i → ∃ λ v → lookup E i ≡ value v)
                    → (∀ i → ∃ λ v → lookup O i .proj₂ ≡ value v)
                    → (∀ i → ∃ λ j → lookup O i .proj₁ ≡ lookup (proj₁ args) j)
                    → ⟨ S , σ , l , 𝒮 ⟩⇒S⟨ S´ , σ´ , l´ , 𝒮´ ⟩
                    → ⟨ (value ref L) [ E , O ]f S , σ , l , 𝒮 ⟩⇒E⟨ (value ref L) [ E , O ]f S´ , σ , l , 𝒮 ⟩

    CALL-PRIM-5 :   ∀ {n args vC}
                    → lookupₛ σ (locToNat L) ≡ just func primFunction (Lᶠ , n , args)
                    → (argsAreValues : ∀ i → ∃ λ v → lookup E i ≡ value v)
                    → (namedArgsAreValues : ∀ i → ∃ λ v → lookup O i .proj₂ ≡ value v)
                    → (∀ i → ∃ λ j → lookup O i .proj₁ ≡ lookup (proj₁ args) j)
                    → ⟨ ₛ₁ S , σ , l , 𝒮 ⟩⇒Sₐ⟨ final σ´ , l´ , ℰ´ ∷ 𝒮´ ⟩
                    → (Call : Loc → ListAny 𝕍 → ListAny (Var × 𝕍) → Store → Var⇀Loc → Maybe (Store × 𝕍C))
                    → Call Lᶠ (Data.List.tabulate (proj₁ ∘ argsAreValues)) (Data.List.tabulate (λ i → lookup O i .proj₁ , namedArgsAreValues i .proj₁)) σ´ ℰ´ ≡ (just (σ˝ , vC))
                    → ⟨ (value ref L) [ E , O ]f S , σ , l , 𝒮 ⟩⇒E⟨ value 𝕍CTo𝕍 vC , σ˝ , l , 𝒮 ⟩

    CALL-USER-1 :   ∀ {args namedArgs}
                    → length E ≡ length args
                    → lookupₛ σ (locToNat L) ≡ just func userFunction (𝒮ₛ , args , namedArgs , S )
                    → (∀ i → ∃ λ j → lookup O i .proj₁ ≡ lookup namedArgs j .proj₁)
                    → ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ value ref L , σ´ , l´ , 𝒮´ ⟩
                    → ⟨ e [ E , O ]f skip , σ , l , 𝒮 ⟩⇒E⟨ (value ref L) [ E , O ]f skip , σ´ , l´ , 𝒮´ ⟩

    CALL-USER-2 :   ∀ {args index namedArgs}
                    → length E ≡ length args
                    → (∀ i → ∃ λ v → lookup (Data.List.take (toℕ index) E) i ≡ value v)
                    → lookupₛ σ (locToNat L) ≡ just func userFunction (𝒮ₛ , args , namedArgs , S )
                    → (∀ i → ∃ λ j → lookup O i .proj₁ ≡ lookup namedArgs j .proj₁)
                    → ⟨ lookup E index , σ , l , 𝒮 ⟩⇒E⟨ eᵢ´ , σ´ , l´ , 𝒮´ ⟩
                    → ⟨ (value ref L) [ E , O ]f skip , σ , l , 𝒮 ⟩⇒E⟨ (value ref L) [ updateAt E index (λ _ → eᵢ´) , O ]f skip , σ´ , l´ , 𝒮´ ⟩

    CALL-USER-3 :   ∀ {args index namedArgs}
                    → length E ≡ length args
                    → (∀ i → ∃ λ v → lookup E i ≡ value v)
                    → (∀ i → ∃ λ v → lookup (Data.List.take (toℕ index) O) i .proj₂ ≡ value v)
                    → lookupₛ σ (locToNat L) ≡ just func userFunction (𝒮ₛ , args , namedArgs , S)
                    → (∀ i → ∃ λ j → lookup O i .proj₁ ≡ lookup namedArgs j .proj₁)
                    → ⟨ lookup O index .proj₂ , σ , l , 𝒮 ⟩⇒E⟨ eᵢ´ , σ´ , l´ , 𝒮´ ⟩
                    → ⟨ (value ref L) [ E , O ]f skip , σ , l , 𝒮 ⟩⇒E⟨ (value ref L) [ E , updateAt O index ((_, eᵢ´) ∘ proj₁) ]f skip , σ´ , l´ , 𝒮´ ⟩

    CALL-USER-4 :   ∀ {args namedArgs}
                    → length E ≡ length args
                    → lookupₛ σ (locToNat L) ≡ just func userFunction (𝒮ₛ , args , namedArgs , S )
                    → (∀ i → ∃ λ v → lookup E i ≡ value v)
                    → (∀ i → ∃ λ v → lookup O i .proj₂ ≡ value v)
                    → (∀ i → ∃ λ j → lookup O i .proj₁ ≡ lookup namedArgs j .proj₁)
                    → ⟨ ₑ₁ (value ref L) [ E , O ]f skip , σ , l , 𝒮 ⟩⇒Eₐ⟨ funcTransitions (value ref L) [ E , O ]f skip , namedArgs , 𝒮ₛ , σ , l , 𝒮 ⟩

    CALL-USER-5 :   ∀ {args index namedArgs}
                    → length E ≡ length args
                    → lookupₛ σ (locToNat L) ≡ just func userFunction (𝒮ₛ , args , namedArgs , S )
                    → (∀ i → ∃ λ v → lookup E i ≡ value v)
                    → (∀ i → ∃ λ v → lookup O i .proj₂ ≡ value v)
                    → (∀ i → ∃ λ j → lookup O i .proj₁ ≡ lookup namedArgs j .proj₁)
                    → (¬ ∃ λ i → lookup O i .proj₁ ≡ x)
                    → ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ e´ , σ´ , l´ , 𝒮´ ⟩
                    → ⟨ funcTransitions (value ref L) [ E , O ]f skip , (x , e) ∷ Data.List.drop index namedArgs , 𝒮ₛ , σ , l , 𝒮 ⟩⇒Eₐ⟨ funcTransitions (value ref L) [ E , O ]f skip , (x , e´) ∷ Data.List.drop index namedArgs , 𝒮ₛ , σ , l , 𝒮 ⟩

    CALL-USER-6 :   ∀ {args namedArgs index}
                    → length E ≡ length args
                    → lookupₛ σ (locToNat L) ≡ just func userFunction (𝒮ₛ , args , namedArgs , S )
                    → (∀ i → ∃ λ v → lookup E i ≡ value v)
                    → (∀ i → ∃ λ v → lookup O i .proj₂ ≡ value v)
                    → (∀ i → ∃ λ j → lookup O i .proj₁ ≡ lookup namedArgs j .proj₁)
                    → (¬ ∃ λ i → lookup O i .proj₁ ≡ x)
                    → ⟨       funcTransitions (value ref L) [ E ,        O               ]f skip , (x , value v) ∷ Data.List.drop index namedArgs , 𝒮ₛ , σ , l , 𝒮
                        ⟩⇒Eₐ⟨ funcTransitions (value ref L) [ E , append O (x , value v) ]f skip ,                 Data.List.drop index namedArgs , 𝒮ₛ , σ , l , 𝒮 ⟩

    CALL-USER-7 :   ∀ {args namedArgs index}
                    → length E ≡ length args
                    → lookupₛ σ (locToNat L) ≡ just func userFunction (𝒮ₛ , args , namedArgs , S )
                    → (∀ i → ∃ λ v → lookup E i ≡ value v)
                    → (∀ i → ∃ λ v → lookup O i .proj₂ ≡ value v)
                    → (∀ i → ∃ λ j → lookup O i .proj₁ ≡ lookup namedArgs j .proj₁)
                    → (∃ λ i → lookup O i .proj₁ ≡ x)
                    → ⟨       funcTransitions (value ref L) [ E , O ]f skip , (x , value v) ∷ Data.List.drop index namedArgs , 𝒮ₛ , σ , l , 𝒮
                        ⟩⇒Eₐ⟨ funcTransitions (value ref L) [ E , O ]f skip ,                 Data.List.drop index namedArgs , 𝒮ₛ , σ , l , 𝒮 ⟩

    CALL-USER-8 :   ∀ {args namedArgs}
                    → length E ≡ length args
                    → lookupₛ σ (locToNat L) ≡ just func userFunction (𝒮ₛ , args , namedArgs , S )
                    → (∀ i → ∃ λ v → lookup E i ≡ value v)
                    → (valuesOfObjs : ∀ i → ∃ λ v → lookup O i .proj₂ ≡ value v)
                    → (∀ (i : Fin (length O)) → ∃ λ j → lookup O i .proj₁ ≡ lookup namedArgs j .proj₁)
                    → ⟨ funcTransitions (value ref L) [ E , O ]f skip , [] , 𝒮ₛ , σ , l , 𝒮
                        ⟩⇒Eₐ⟨ ₑ₁ stackframe 𝒮 S ,
                            Data.List.foldl (uncurry ∘ _[_↦ₛ_]) σ
                                (Data.List.zip (
                                    Data.List.applyUpTo
                                        (_+ℕ locToNat l)
                                        (length O)
                                ) (Data.List.tabulate
                                    (proj₁ ∘ valuesOfObjs)
                                )) ,
                            locFromNat (length O +ℕ locToNat l) ,
                            Data.List.foldl (uncurry ∘ _[_↦ₑ_]) Æ
                                (Data.List.zip (mapL proj₁ O) (
                                    Data.List.applyUpTo
                                        (locFromNat ∘ (_+ℕ locToNat l))
                                        (length O)
                                ))
                            ∷ 𝒮ₛ ⟩

    STACKFRAME-1 :  ⟨ S , σ , l , 𝒮 ⟩⇒S⟨ S´ , σ´ , l´ , 𝒮´ ⟩ →
                    ⟨ stackframe 𝒮ₛ S , σ , l , 𝒮 ⟩⇒E⟨ stackframe 𝒮ₛ S´ , σ´ , l´ , 𝒮´ ⟩

    STACKFRAME-2 :  ⟨ ₛ₁ S , σ , l , 𝒮 ⟩⇒Sₐ⟨ final σ´ , l´ , 𝒮´ ⟩ →
                    ⟨ stackframe 𝒮ₛ S , σ , l , 𝒮 ⟩⇒E⟨ stackframe 𝒮ₛ return· , σ´ , l´ , 𝒮´ ⟩

    STACKFRAME-3 : ⟨ stackframe 𝒮ₛ (return value v) , σ , l , 𝒮 ⟩⇒E⟨ value v , σ , l , 𝒮ₛ ⟩

    List-1 :    ∀ {indexOfExpr}
                → minIndexNonValue (fromList (e ∷ E)) ≡ just indexOfExpr
                → ⟨ lookup (e ∷ E) indexOfExpr , σ  , l  , 𝒮  ⟩⇒E⟨ eᵢ´ , σ´ , l´ , 𝒮´ ⟩
                → ⟨ eᵢ´ , σ´ , l´ , 𝒮´ ⟩⇒E⟨ eᵢ˝ , σ˝ , l˝ , 𝒮˝ ⟩
                → ⟨ [ e ∷ E ] , σ , l , 𝒮 ⟩⇒E⟨ [ updateAt (e ∷ E) indexOfExpr (λ _ → eᵢ´) ] , σ´ , l´ , 𝒮´ ⟩

    List-2 :    ∀ {indexOfExpr}
                → minIndexNonValue (fromList (e ∷ E)) ≡ just indexOfExpr
                → ⟨ lookup (e ∷ E) indexOfExpr , σ  , l  , 𝒮  ⟩⇒E⟨ value v , σ´ , l´ , 𝒮´ ⟩
                → ⟨ [ e ∷ E ] , σ , l , 𝒮 ⟩⇒E⟨ [ updateAt (e ∷ E) indexOfExpr (λ _ → value ref l´) ] , σ´ [ locToNat l´ ↦ₛ v ] , nxt l´ , 𝒮´ ⟩

    List-3 :    ∀ {n locs} --hasLocOnly E
                → (length E) <ₙ (2 ^ 63)
                → length E ≡ toℕ n
                → (p : length locs ≡ toℕ n) -- TODO you could infer this instead of taking it as an assumption
                → (Data.List.foldl (λ x → _>>= (λ y → map (y ∷_) x)) (just []) (mapL exprToLoc E)) ≡ just locs
                → ⟨ [ E ] , σ , l , 𝒮 ⟩⇒E⟨ value ref l , σ [ locToNat l ↦ₛ list_ {n} (transfer p (fromList locs)) ] , nxt l , 𝒮 ⟩

    MEMBER-EXPR-1 : ⟨ m , σ , l , 𝒮 ⟩⇒M⟨ m´ , σ´ , l´ , 𝒮´ ⟩ →
                    ⟨ member m , σ , l , 𝒮 ⟩⇒E⟨ member m´ , σ´ , l´ , 𝒮´ ⟩

    MEMBER-EXPR-2 : lookupₛ σ (locToNat L) ≡ just v →
                    ⟨ member locM L , σ , l , 𝒮 ⟩⇒E⟨ value v , σ , l , 𝒮 ⟩

breakEnv : Var⇀Loc → Σ ℕ (λ n → Vec Var n × Vec Loc n)
breakEnv (fst , _) = length fst , unzip (fromList fst)

APPLY-4-algo : Store → ListAny Loc → Σ ℕ (λ n → Vec Var n × Vec Loc n) → Maybe Store
APPLY-4-algo σ [] _ = just σ
APPLY-4-algo σ (L₁ ∷ Lₘ) (n , Nₙ , vₑₙ) with lookupₛ σ (locToNat L₁)
... | nothing = nothing
... | just obj o = APPLY-4-algo (σ [ locToNat L₁ ↦ₛ obj Data.Vec.foldl′ (uncurry ∘ _[_↦ₑ_]) o (Data.Vec.zip Nₙ vₑₙ) ]) Lₘ (n , Nₙ , vₑₙ)
... | just v = nothing

data ⟨_⟩⇒Sₐ⟨_⟩ where

    FN-DECL :   ⟨ ₛ₁ fn x ⟨ xₙ , xₒ=eₒ ⟩ S , σ , l , ℰ ∷ 𝒮 ⟩⇒Sₐ⟨
                    final σ [ locToNat l ↦ₛ ref nxt l ] [
                        locToNat (nxt l) ↦ₛ func (userFunction (ℰ [ x ↦ₑ l ] ∷ 𝒮 , xₙ , xₒ=eₒ , S))
                    ] , nxt nxt l , ℰ [ x ↦ₑ l ] ∷ 𝒮
                ⟩

    RETURN :    ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ e´ , σ´ , l´ , 𝒮´ ⟩ →
                ⟨ return e , σ , l , 𝒮 ⟩⇒S⟨ return e´ , σ´ , l´ , 𝒮´ ⟩

    COMP-1 :    ⟨ S₁      , σ , l , 𝒮 ⟩⇒S⟨ S₁´      , σ´ , l´ , 𝒮´ ⟩ →
                ⟨ S₁ ⍮ S₂ , σ , l , 𝒮 ⟩⇒S⟨ S₁´ ⍮ S₂ , σ´ , l´ , 𝒮´ ⟩

    COMP-2 :    ⟨ ₛ₁ S₁ , σ , l , 𝒮 ⟩⇒Sₐ⟨ final σ´ , l´ , 𝒮´ ⟩ →
                ⟨ S₁ ⍮ S₂ , σ , l , 𝒮 ⟩⇒S⟨ S₂ , σ´ , l´ , 𝒮´ ⟩

    COMP-3 : ⟨ return value v ⍮ S₂ , σ , l , 𝒮 ⟩⇒S⟨ return value v , σ´ , l´ , 𝒮´ ⟩

    COMP-4 : ⟨ return· ⍮ S₂ , σ , l , 𝒮 ⟩⇒S⟨ return· , σ , l , 𝒮 ⟩

    SKIP : ⟨ ₛ₁ skip , σ , l , 𝒮 ⟩⇒Sₐ⟨ final σ , l , 𝒮 ⟩

    BLOCK-1 :   ⟨   S   , σ , l , 𝒮 ⟩⇒S⟨   S´   , σ´ , l´ , 𝒮´ ⟩ →
                ⟨ ⟨ S ⟩ , σ , l , 𝒮 ⟩⇒S⟨ ⟨ S´ ⟩ , σ´ , l´ , 𝒮´ ⟩

    BLOCK-2 :   ⟨ ₛ₁   S   , σ , l , 𝒮 ⟩⇒Sₐ⟨ final σ´ , l´ , ℰ´ ∷ 𝒮´ ⟩ →
                ⟨ ₛ₁ ⟨ S ⟩ , σ , l , 𝒮 ⟩⇒Sₐ⟨ final σ´ , l´ ,      𝒮´ ⟩

    BLOCK-3 : ⟨ ⟨ return value v ⟩ , σ , l , ℰ ∷ 𝒮 ⟩⇒S⟨ return value v , σ , l , 𝒮 ⟩

    BLOCK-4 : ⟨ ⟨ return· ⟩ , σ , l , ℰ ∷ 𝒮 ⟩⇒S⟨ return· , σ , l , 𝒮 ⟩

    IF-COND :   ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ e´ , σ´ , l´ , 𝒮´ ⟩ →
                ⟨ if e then S₁ else S₂ , σ , l , 𝒮 ⟩⇒S⟨ if e´ then S₁ else S₂ , σ´ , l´ , 𝒮´ ⟩

    IF-TRUE : ⟨ if value bool tt then S₁ else S₂ , σ , l , 𝒮 ⟩⇒S⟨ ⟨ S₁ ⟩ , σ , l , Æ ∷ 𝒮 ⟩

    IF-FALSE : ⟨ if value bool ff then S₁ else S₂ , σ , l , 𝒮 ⟩⇒S⟨ ⟨ S₂ ⟩ , σ , l , Æ ∷ 𝒮 ⟩

    WHILE : ⟨ while e dø S , σ , l , 𝒮 ⟩⇒S⟨
                if e then
                    if value bool tt then S else skip ⍮
                    while e dø S
                else skip , σ , l , 𝒮
            ⟩

    ASSIGN-1 :  ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ e´ , σ´ , l´ , 𝒮´ ⟩ →
                ⟨ m ← e , σ , l , 𝒮 ⟩⇒S⟨ m ← e´ , σ´ , l´ , 𝒮´ ⟩

    ASSIGN-2 :  ⟨ m , σ , l , 𝒮 ⟩⇒M⟨ m´ , σ´ , l´ , 𝒮´ ⟩ →
                ⟨ m ← value v , σ , l , 𝒮 ⟩⇒S⟨ m´ ← value v , σ´ , l´ , 𝒮´ ⟩

    ASSIGN-3 : ⟨ ₛ₁ locM L ← value v , σ , l , 𝒮 ⟩⇒Sₐ⟨ final (σ [ locToNat L ↦ₛ v ]) , l , 𝒮 ⟩

    ASSIGN-4 :  ψ x (ℰ ∷ 𝒮) ≡ nothing →
                ⟨ ₛ₁ name x ← value v , σ , l , ℰ ∷ 𝒮 ⟩⇒Sₐ⟨ final σ [ locToNat l ↦ₛ v ] , nxt l , ℰ [ x ↦ₑ l ] ∷ 𝒮 ⟩

    EXPR-STMT-1 :   ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ e´ , σ´ , l´ , 𝒮´ ⟩ →
                    ⟨ expr e , σ , l , 𝒮 ⟩⇒S⟨ expr e´ , σ´ , l´ , 𝒮´ ⟩

    EXPR-STMT-2 : ⟨ ₛ₁ expr value v , σ , l , 𝒮 ⟩⇒Sₐ⟨ final σ , l , 𝒮 ⟩

    EXPR-STMT-3 : ⟨ ₛ₁ expr stackframe 𝒮ₛ return· , σ , l , 𝒮 ⟩⇒Sₐ⟨ final σ , l , 𝒮ₛ ⟩

    APPLY-1 :   ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ e´ , σ´ , l´ , 𝒮´ ⟩ →
                ⟨ e´ , σ´ , l´ , 𝒮´ ⟩⇒E⟨ e˝ , σ˝ , l˝ , 𝒮˝ ⟩ →
                ⟨ apply e dø S , σ , l , 𝒮 ⟩⇒S⟨ apply e´ dø S , σ´ , l´ , 𝒮´ ⟩

    APPLY-2 :   ∀ {n locs}
                → ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ value ref L , σ´ , l´ , 𝒮´ ⟩
                → lookupₛ σ´ (locToNat L) ≡ just list_ {n} locs
                → ((i : Fin (toℕ n)) → ∃ λ (o : Var⇀Loc) → lookupₛ σ´ (locToNat (Data.Vec.lookup locs i)) ≡ just obj o)
                → ⟨ apply e dø S , σ , l , 𝒮 ⟩⇒S⟨ apply value list_ {n} locs dø S , σ´ , l´ , Æ ∷ 𝒮´ ⟩

    APPLY-3 :   ∀ {n locs}
                → ⟨ S , σ , l , 𝒮 ⟩⇒S⟨ S´ , σ´ , l´ , 𝒮´ ⟩
                → ((i : Fin (toℕ n)) → ∃ λ (o : Var⇀Loc) → lookupₛ σ´ (locToNat (Data.Vec.lookup locs i)) ≡ just obj o)
                → ⟨ apply value list_ {n} locs dø S , σ , l , 𝒮 ⟩⇒S⟨ apply value list_ {n} locs dø S´ , σ´ , l´ , 𝒮´ ⟩

    APPLY-4 :   ∀ {n locs}
                → ⟨ ₛ₁ S , σ , l , 𝒮 ⟩⇒Sₐ⟨ final σ´ , l´ , ℰ´ ∷ 𝒮´ ⟩
                → ((i : Fin (toℕ n)) → ∃ λ (o : Var⇀Loc) → lookupₛ σ´ (locToNat (Data.Vec.lookup locs i)) ≡ just obj o)
                → APPLY-4-algo σ (toList locs) (breakEnv ℰ´) ≡ just σ´
                → ⟨ ₛ₁ apply value list_ {n} locs dø S , σ , l , 𝒮 ⟩⇒Sₐ⟨ final σ´ , l´ , 𝒮´ ⟩

    APPLY-5 :   ∀ {n locs}
                → ⟨ apply value list_ {n} locs dø return value v , σ , l , 𝒮 ⟩⇒S⟨ return value v , σ´ , l´ , 𝒮´ ⟩

    APPLY-6 :   ∀ {n locs}
                → ⟨ apply value list_ {n} locs dø return· , σ , l , 𝒮 ⟩⇒S⟨ return· , σ´ , l´ , 𝒮´ ⟩


-- minimum index that is not a number
minIndexNonInt : ∀ {n} → Vec Expr (suc n) → Maybe (Fin (suc n))
minIndexNonInt {ℕ.zero} ((value (int x)) Vec.∷ Vec.[]) = nothing
minIndexNonInt {suc n} ((value (int x)) Vec.∷ x₁) = map Fin.suc (minIndexNonInt x₁)
minIndexNonInt (x Vec.∷ y) = just Fin.zero

exprsAsIndecies : ListAny Expr → Maybe (ListAny (Fin (2 ^ 63)))
exprsAsIndecies [] = just []
exprsAsIndecies (value int nonNeg n ∷ xs) = map (n ∷_) (exprsAsIndecies xs)
exprsAsIndecies (x ∷ x₁) = nothing

massIndex : (σ : ListAny Loc) → ListAny (Fin (2 ^ 63)) → Maybe (ListAny Loc)
massIndex xs [] = just []
massIndex xs (i ∷ is) with toℕ i <?ₙ length xs
... | yes p = map ((λ l → (lookup xs (fromℕ< p)) ∷ l)) (massIndex xs is)
... | no p = nothing

vecLenReplace : {n m : ℕ} → Vec Loc n → n ≡ m → Vec Loc m
vecLenReplace x refl = x

data ⟨_⟩⇒M⟨_⟩ where

    INDEX-1 :   ⟨ e₁ , σ , l , 𝒮 ⟩⇒E⟨ e₁´ , σ´ , l´ , 𝒮´ ⟩ →
                ⟨ e₁ [ e₂ , E ]ᵢ , σ , l , 𝒮 ⟩⇒M⟨ e₁´ [ e₂ , E ]ᵢ , σ´ , l´ , 𝒮´ ⟩

    INDEX-2 :   ∀ {indexOfExpr}
                → minIndexNonInt (fromList (e₁ ∷ E)) ≡ just indexOfExpr
                → ⟨ lookup (e₁ ∷ E) indexOfExpr , σ , l , 𝒮 ⟩⇒E⟨ eᵢ´ , σ´ , l´ , 𝒮´ ⟩
                → {updateAt (e₁ ∷ E) indexOfExpr (λ _ → eᵢ´) ≡ e₁´ ∷ E´}
                → ⟨ (value ref L) [ e₁ , E ]ᵢ , σ , l , 𝒮 ⟩⇒M⟨ (value ref L) [ e₁´ , E´ ]ᵢ , σ´ , l´ , 𝒮´ ⟩

    INDEX-3 :   ∀ {n locs i j}
                → lookupₛ σ (locToNat L) ≡ just (list_ {n} locs)
                → toℕ i ≡ toℕ j
                → ⟨ (value ref L) [ value int nonNeg i , [] ]ᵢ , σ , l , 𝒮 ⟩⇒M⟨ locM Data.Vec.lookup locs j , σ , l , 𝒮 ⟩

    INDEX-4 :   ∀ {indecies fromIndexing n m locs}
                → lookupₛ σ (locToNat L) ≡ just (list_ {n} locs)
                → exprsAsIndecies (e₁ ∷ e₂ ∷ E) ≡ just indecies
                → massIndex (toList locs) indecies ≡ just fromIndexing
                → (p : length fromIndexing ≡ toℕ m)
                → ⟨ (value ref L) [ e₁ , e₂ ∷ E ]ᵢ , σ , l , 𝒮 ⟩⇒M⟨ locM l , σ [ locToNat L ↦ₛ list (vecLenReplace (fromList {A = Loc} fromIndexing) p) ] , nxt l , 𝒮 ⟩

    MEMBER-1 :  ⟨ e , σ , l , 𝒮 ⟩⇒E⟨ e´ , σ´ , l´ , 𝒮´ ⟩ →
                ⟨ e deref x , σ , l , 𝒮 ⟩⇒M⟨ e´ deref x , σ´ , l´ , 𝒮´ ⟩

    MEMBER-2 :  ∀ {O}
                → lookupₛ σ (locToNat L) ≡ just (obj O)
                → lookupₑ O x ≡ just L
                → ⟨ (value (ref L)) deref x , σ , l , 𝒮 ⟩⇒M⟨ locM L , σ , l , 𝒮 ⟩

    VAR :   ψ x 𝒮 ≡ just L →
            ⟨ name x , σ , l , 𝒮 ⟩⇒M⟨ locM L , σ , l , 𝒮 ⟩
