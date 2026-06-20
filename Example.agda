module Example where

open import Data.String using (String) renaming (_<_ to _<ₛ_; _<?_ to _<?ₛ_; _==_ to _==ₛ_)
open import Data.Bool using (Bool) renaming (false to ff; true to tt)

open import BoardGame String _<ₛ_ _<?ₛ_ _==ₛ_
open import Data.Product using (_,_)
open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong-app)

one two three four five six seven
  eight nine ten eleven tvelve thirteen fourteen
  fifteen : Γₛ₁

sixteen : Γₛ₂

one =
  name "x" ← value bool ff ⍮
  while member name "x" == value bool ff
    dø name "x" ← value bool tt
  , emptyStore , NULL , Æ ∷ []

two =
  while member name "x" == value bool ff
    dø name "x" ← value bool tt
  , emptyStore [ locToNat NULL ↦ₛ bool ff ] , nxt NULL , Æ [ "x" ↦ₑ NULL ] ∷ []

three =
  if member name "x" == value bool ff then
    if value bool tt
      then name "x" ← value bool tt
      else skip ⍮
    while member name "x" == value bool ff
      dø name "x" ← value bool tt
    else skip
  , emptyStore [ locToNat NULL ↦ₛ bool ff ] , nxt NULL , Æ [ "x" ↦ₑ NULL ] ∷ []

four =
  if member locM NULL == value bool ff then
    if value bool tt
      then name "x" ← value bool tt
      else skip ⍮
    while member name "x" == value bool ff
      dø name "x" ← value bool tt
    else skip
  , emptyStore [ locToNat NULL ↦ₛ bool ff ] , nxt NULL , Æ [ "x" ↦ₑ NULL ] ∷ []

five =
  if value bool ff == value bool ff then
    if value bool tt
      then name "x" ← value bool tt
      else skip ⍮
    while member name "x" == value bool ff
      dø name "x" ← value bool tt
    else skip
  , emptyStore [ locToNat NULL ↦ₛ bool ff ] , nxt NULL , Æ [ "x" ↦ₑ NULL ] ∷ []

six =
  if value bool tt then
    if value bool tt
      then name "x" ← value bool tt
      else skip ⍮
    while member name "x" == value bool ff
      dø name "x" ← value bool tt
    else skip
  , emptyStore [ locToNat NULL ↦ₛ bool ff ] , nxt NULL , Æ [ "x" ↦ₑ NULL ] ∷ []

seven =
  ⟨
    if value bool tt
      then name "x" ← value bool tt
      else skip ⍮
    while member name "x" == value bool ff
      dø name "x" ← value bool tt
  ⟩
  , emptyStore [ locToNat NULL ↦ₛ bool ff ] , nxt NULL , Æ ∷ Æ [ "x" ↦ₑ NULL ] ∷ []

eight =
  ⟨
    ⟨ name "x" ← value bool tt ⟩ ⍮
    while member name "x" == value bool ff
      dø name "x" ← value bool tt
  ⟩
  , emptyStore [ locToNat NULL ↦ₛ bool ff ] , nxt NULL , Æ ∷ Æ ∷ Æ [ "x" ↦ₑ NULL ] ∷ []

nine =
  ⟨
    ⟨ locM NULL ← value bool tt ⟩ ⍮
    while member name "x" == value bool ff
      dø name "x" ← value bool tt
  ⟩
  , emptyStore [ locToNat NULL ↦ₛ bool ff ] , nxt NULL , Æ ∷ Æ ∷ Æ [ "x" ↦ₑ NULL ] ∷ []

ten =
  ⟨
    while member name "x" == value bool ff
      dø name "x" ← value bool tt
  ⟩
  , emptyStore [ locToNat NULL ↦ₛ bool tt ] , nxt NULL , Æ ∷ Æ [ "x" ↦ₑ NULL ] ∷ []

eleven =
  ⟨
    if member name "x" == value bool ff then
        if value bool tt then name "x" ← value bool tt else skip ⍮
        while member name "x" == value bool ff dø name "x" ← value bool tt
    else skip
  ⟩
  , emptyStore [ locToNat NULL ↦ₛ bool tt ] , nxt NULL , Æ ∷ Æ [ "x" ↦ₑ NULL ] ∷ []

tvelve =
  ⟨
    if member locM NULL == value bool ff then
        if value bool tt then name "x" ← value bool tt else skip ⍮
        while member name "x" == value bool ff dø name "x" ← value bool tt
    else skip
  ⟩
  , emptyStore [ locToNat NULL ↦ₛ bool tt ] , nxt NULL , Æ ∷ Æ [ "x" ↦ₑ NULL ] ∷ []

thirteen =
  ⟨
    if value bool tt == value bool ff then
        if value bool tt then name "x" ← value bool tt else skip ⍮
        while member name "x" == value bool ff dø name "x" ← value bool tt
    else skip
  ⟩
  , emptyStore [ locToNat NULL ↦ₛ bool tt ] , nxt NULL , Æ ∷ Æ [ "x" ↦ₑ NULL ] ∷ []

fourteen =
  ⟨
    if value bool ff then
        if value bool tt then name "x" ← value bool tt else skip ⍮
        while member name "x" == value bool ff dø name "x" ← value bool tt
    else skip
  ⟩
  , emptyStore [ locToNat NULL ↦ₛ bool tt ] , nxt NULL , Æ ∷ Æ [ "x" ↦ₑ NULL ] ∷ []

fifteen =
  ⟨
    ⟨ skip ⟩
  ⟩
  , emptyStore [ locToNat NULL ↦ₛ bool tt ] , nxt NULL , Æ ∷ Æ ∷ Æ [ "x" ↦ₑ NULL ] ∷ []

sixteen = emptyStore [ locToNat NULL ↦ₛ bool tt ] , nxt NULL , Æ [ "x" ↦ₑ NULL ] ∷ []

step1 : ⟨ one ⟩⇒S⟨ two ⟩
step1 = COMP-2 (ASSIGN-4 refl)

step2 : ⟨ two ⟩⇒S⟨ three ⟩
step2 = WHILE

step3 : ⟨ three ⟩⇒S⟨ four ⟩
step3 = IF-COND (OP-1 ⊙== (MEMBER-EXPR-1 (VAR refl)))

step4 : ⟨ four ⟩⇒S⟨ five ⟩
step4 = IF-COND (OP-1 ⊙== (MEMBER-EXPR-2 refl))

step5 : ⟨ five ⟩⇒S⟨ six ⟩
step5 = IF-COND EQ-BOOL-TRUE

step6 : ⟨ six ⟩⇒S⟨ seven ⟩
step6 = IF-TRUE

step7 : ⟨ seven ⟩⇒S⟨ eight ⟩
step7 = BLOCK-1 (COMP-1 IF-TRUE)

step8 : ⟨ eight ⟩⇒S⟨ nine ⟩
step8 = BLOCK-1 (COMP-1 (BLOCK-1 (ASSIGN-2 (VAR refl))))

step9 : ⟨ nine ⟩⇒S⟨ ten ⟩
step9 = BLOCK-1 (COMP-2 (BLOCK-2 ASSIGN-3))

step10 : ⟨ ten ⟩⇒S⟨ eleven ⟩
step10 = BLOCK-1 WHILE

step11 : ⟨ eleven ⟩⇒S⟨ tvelve ⟩
step11 = BLOCK-1 (IF-COND (OP-1 ⊙== (MEMBER-EXPR-1 (VAR refl))))

step12 : ⟨ tvelve ⟩⇒S⟨ thirteen ⟩
step12 = BLOCK-1 (IF-COND (OP-1 ⊙== (MEMBER-EXPR-2 refl)))

step13 : ⟨ thirteen ⟩⇒S⟨ fourteen ⟩
step13 = BLOCK-1 (IF-COND (EQ-BOOL-FALSE λ ()))

step14 : ⟨ fourteen ⟩⇒S⟨ fifteen ⟩
step14 = BLOCK-1 IF-FALSE

step15 : ⟨ ₛ₁ fifteen ⟩⇒Sₐ⟨ final sixteen ⟩
step15 = BLOCK-2 (BLOCK-2 SKIP)
