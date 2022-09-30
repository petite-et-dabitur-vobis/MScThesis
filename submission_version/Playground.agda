{-# OPTIONS --without-K #-}

open import Types
open import Univalence
open import EqReasoning

-- this file was made for tests and getting used to Agda

simple_pair : ℕ × ℕ
simple_pair = (2 , 2)

simple_pair_verbose : Σ x ꞉ ℕ ∙ ℕ
simple_pair_verbose = (2 , 2)

nested_pair : ℕ × (ℕ × ℕ)
nested_pair = (2 , (2 , 2))

nested_pair_verbose1 : Σ x ꞉ ℕ ∙ (ℕ × ℕ)
nested_pair_verbose1 = (2 , (2 , 2))

nested_pair_verbose2 : ( Σ x ꞉ ℕ ∙ ℕ ) × ℕ
nested_pair_verbose2 = ((2 , 2) , 2)

nested_pair_verbose3 : Σ x ꞉ ℕ ∙ (Σ x ꞉ ℕ ∙ ℕ)
nested_pair_verbose3 = (2 , (2 , 2))

pair_no_syntax1 : Σ ℕ (λ _ → ℕ)
pair_no_syntax1 = (2 , 2)

nested_pair_no_syntax1 : Σ ℕ (λ _ → Σ ℕ (λ _ → ℕ))
nested_pair_no_syntax1 = (2 , (2 , 2))

nested_pair_no_syntax2 : Σ (Σ ℕ (λ _ → ℕ)) (λ _ → ℕ)
nested_pair_no_syntax2 = ((2 , 2) , 2)

-- sized lists
private
  variable
    n : ℕ

data Vec (A : Type) : (n : ℕ) → Type where
  []   : Vec A 0
  cons : A → Vec A n → Vec A (succ n)

dep_pair : Σ x ꞉ ℕ ∙ Vec ℕ x
dep_pair = (2 , cons 2 (cons 2 []) )

nested_dep_pair : Σ x ꞉ ℕ ∙ (Vec ℕ x × Vec ℕ x)
nested_dep_pair = (2 , (cons 2 (cons 2 []) , cons 2 (cons 2 [])) )

-- 1st try (without Σ type) for SEQ
-- without map
record SEQ1 (A : Type) (Seq : Type → Type) : Type where
  constructor s
  field
    empty  : Seq A
    single : A → Seq A
    append : Seq A → Seq A → Seq A

-- list implementation for sequences
data List (A : Type) : Type where
  [] : List A
  cons : A → List A → List A

lempty : {A : Type} → List A
lempty = []

lsingle : {A : Type} → (x : A) → List A
lsingle x = cons x []

lappend : {A : Type} → List A → List A → List A
lappend [] l = l
lappend (cons a l1) l2 = cons a (lappend l1 l2)

lmap : {A B : Type} → (f : A → B) → List A → List B
lmap f [] = []
lmap f (cons a l) = cons (f a) (lmap f l)

ListSeq1 : {A : Type} → SEQ1 A List
ListSeq1 = s lempty lsingle lappend

-- 2nd try (without Σ type) for SEQ
record SEQ2 : Set₁ where
  field
    Seq      : Type → Type
    empty    : {A : Type} → Seq A
    single   : {A : Type} → A → Seq A
    append   : {A : Type} → Seq A → Seq A → Seq A
    map      : {A B : Type} → (A → B) → (Seq A → Seq B)

ListSeq2 : SEQ2
ListSeq2 = record {Seq = List ; empty = lempty ; single = lsingle ; append = lappend ; map = lmap}

-- we can project from SEQ; e.g.
ListEmpty : {A : Type} → List A
ListEmpty = SEQ2.empty ListSeq2

prop2 : {A : Type} → (xs : List A) → lappend [] xs == xs
prop2 xs = refl xs 

record SeqStr ( A : Type) : Set₁ where
  field
    Seq      : Type → Type
    empty    : Seq A
    single   : A → Seq A
    append   : Seq A → Seq A → Seq A
    map      : { B : Type } → (A → B) → (Seq A → Seq B)

SEQ3 = Σ₁ A ꞉ Type ∙ (SeqStr A)

postulate
  e : {A : Type} → List A ≃ ℕ

test = Σ₁ Seq ꞉ (Type → Type) ∙ ( let empty = ((A : Type) → Seq A) in empty)
test2 = Σ₁ ( Type → Type ) (λ Seq → (A : Type) → Seq A )

prop22 : {A : Type} → (xs : List A) → lappend [] xs == xs
prop22 xs =
  begin xs □

