{-# OPTIONS --without-K #-}

open import Agda.Primitive

Type = Set 

---------------------------------------------------------
-----------------  naturals for testing -----------------
---------------------------------------------------------


data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

---------------------------------------------------------
-------------------- dependent pairs --------------------
---------------------------------------------------------

-- CHAPTER 2.3.2
record Σ (A : Type) (B : A → Type) : Type where
  constructor _,_
  field
    x : A
    b : B x

-- clearer syntax
syntax Σ A (λ x → b) = Σ x ꞉ A ∙ b

-- after chapter 3.2, we have the type of types, 𝒰;
-- here, 𝒰 is Set₁ 
record Σ₁ (A : Set₁) (B : A → Set₁) : Set₁ where
  constructor _,_
  field
    x : A
    b : B x

-- clearer syntax
syntax Σ₁ A (λ x → b) = Σ₁ x ꞉ A ∙ b

-- this Σ₁ could be done in a better, more encompassing way
-- here's how
record Σₙ {m n : Level} (A : Set m) (B : A → Set n) : Set (m ⊔ n) where
  constructor _,,_
  field
    x : A
    b : B x

-- clearer syntax
syntax Σₙ A (λ x → b) = Σₙ x ꞉ A ∙ b

-- projections (Agda gives them for free)

-- for Σ
-- alternative syntax:
--pr₁ : {A : Type} → {B : A → Type} → Σ A B → A
--pr₁ : {A B : Type} → Σ x ꞉ A ∙ B → A
pr₁ = Σ.x
-- alternative implementation
--pr₁ (x , y) = x

-- alternative syntax:
--pr₂ : {A : Type} → {B : A → Type} → ( z : Σ A B) → B (pr₁ z)
--pr₂ : {A B : Type} → (z : Σ x ꞉ A ∙ B) → B 
pr₂ = Σ.b
-- alternative implementation
--pr₂ (x , y) = y

-- for Σ₁
--Σ₁pr₁ : {A B : Set₁} → Σ₁ x ꞉ A ∙ B → A
--Σ₁pr₁ ( A ,, B ) = A
Σ₁pr₁ = Σ₁.x

--Σ₁pr₂ : {A B : Set₁} → (z : Σ₁ x ꞉ A ∙ B) → B 
--Σ₁pr₂ ( A ,, B ) = B
Σ₁pr₂ = Σ₁.b

-- for Σₙ
Σₙpr₁ = Σₙ.x

Σₙpr₂ = Σₙ.b           

-- induction principle for Σₙ
Σₙ-induction : {m n o : Level} {X : Set m} {Y : X → Set n} {A : Σₙ X Y → Set o}
            → ((x : X) (y : Y x) → A (x ,, y))
            → ((x ,, y) : Σₙ X Y) → A (x ,, y)
Σₙ-induction g (x ,, y) = g x y

-- CHAPTER 2.2.2

-- simple product: B doesn't depend on A
_×_ : Type → Type → Type
-- alternative definition:
--A × B = Σ A (λ _ → B)
A × B = Σ x ꞉ A ∙ B


---------------------------------------------------------
------------------ dependent functions ------------------
---------------------------------------------------------

-- CHAPTER 2.3.1
-- general implementation
Π : {m n : Level} (A : Set m) → (B : A → Set n) → Set (m ⊔ n)
Π A B = (x : A) → B x

syntax Π A (λ x → b) = Π x ꞉ A ∙ b

-- note that
-- Π A (λ _ → B) = Π x ꞉ A , B
-- is the same as the arrow type

-- identity function
id : {X : Type} → X → X
id x = x

-- identity function for types
idₜ : {𝒰 : Set₁} → 𝒰 → 𝒰
idₜ A = A

-- identity for general universes
idₙ : {n : Level} {𝒰 : Set n} → 𝒰 → 𝒰
idₙ A = A

-- functions to retrieve implicit arguments
domain : {X : Type} → {Y : Type} → (X → Y) → Type
domain {X} {Y} f = X

codomain : {X : Type} → {Y : Type} → (X → Y) → Type
codomain {X} {Y} f = Y

type-of : {X : Type} → X → Type
type-of {X} x = X

-- composition of functions
_∘_ : {A B C : Type} → (f : B → C) → (g : A → B) → (A → C)
f ∘ g = λ x → f (g x)
 
---------------------------------------------------------
-------------------- disjoint sum  ----------------------
---------------------------------------------------------

-- CHAPTER 2.2.3
data _⊎_ (A : Type) (B : Type) : Type where
  inₗ : A → A ⊎ B
  inᵣ : B → A ⊎ B


---------------------------------------------------------
-------------------- identity types ---------------------
---------------------------------------------------------

-- CHAPTER 2.4
-- data for identity type
-- note that we have I-formation and I-introduction here
data Id (X : Type) : X →  X → Type where
  refl : (x : X) → Id X x x

-- sym and trans are implemented in EqReasoning

-- notation
_==_ : {X : Type} → X → X → Type
x == y = Id _ x y
-- could also use
--x == y = Id (type-of x) x y

-- elimination and computation rules, taken from the thesis
==-induction : (X : Type)
             → (C : (x y : X) → x == y → Type)
             → ((x : X) → (C x x (refl x)) )
             → (a b : X) (p : a == b)
             → C a b p
==-induction X C c a a (refl a) = c a

-- transport 
-- Returns a function that
-- "translates" equality into another context,
-- brought about by P.
-- Since P x and P y will be of different types,
-- equality between their terms isn't defined.
-- However, by "changing context" through transport,
-- which we do based off of the premise x == y,
-- we can get something which is "equivalent" to equality
-- note that most of these definitions are made by path induction
transport : {A : Type} → (P : A → Type)
          →  {x y : A} → (x == y)
          → (P x → P y)
transport P (refl x) = id {P x}

-- action on paths (ap)
-- that is, apply 𝑓 to x == y
-- and obtain 𝑓 x == 𝑓 y
ap : {A B : Type} → (f : A → B)
   → {x y : A} → (x == y) → (f x == f y)
ap f (refl x) = refl (f x)

-- dependent action on paths (apd)
-- that is, apply ap still
-- but now we have a property/fibration/context change P
-- and some dependent 𝑓 : (Π x꞉A . P x)
-- our goal is to get the analogous of 𝑓 x == 𝑓 y
-- but in these circumstances. however,
-- 𝑓 x and 𝑓 y are now different types;
-- this means we'll need transport 𝑓 x. from here,
-- things are clear
-- ‼ note that the last equality is in the context of 𝑓 y
apd : {A : Type} → ( P : A → Type )
    → ( f : (a : A) → P a )
    → {x y : A} → (p : x == y)
    → ( (transport P p (f x)) == (f y))
apd P f (refl x) = refl (f x)

--------------------------------------------------------------
-- identity for types (requires mention of universes)
data Idₜ (𝒰 : Set₁) : 𝒰 → 𝒰 → Set₁ where
  reflₜ : (A : 𝒰) → Idₜ 𝒰 A A

-- notation for type identity
_==ₜ_ : {𝒰 : Set₁} → 𝒰 → 𝒰 → Set₁
A ==ₜ B = Idₜ _ A B

-- naturally, we could define this generally,
-- but that would take away clarity.

-- only need transport
transportₜ : {𝒰 : Set₁} → (C : 𝒰 → Set₁)
          → {A B : 𝒰} → (A ==ₜ B)
          → (C A → C B)
transportₜ C (reflₜ A) = idₜ {C A}

----------------------------------------------
-- identity for general case
data Idₙ {n : Level}(𝒰 : Set n) : 𝒰 → 𝒰 → Set (lsuc n) where
  reflₙ : (A : 𝒰) → Idₙ 𝒰 A A

-- notation for type identity
_==ₙ_ : {n : Level}{𝒰 : Set n} → 𝒰 → 𝒰 → Set (lsuc n)
A ==ₙ B = Idₙ _ A B

apₙ : {A B : Type} → (f : A → B)
   → {x y : A} → (x ==ₙ y) → (f x ==ₙ f y)
apₙ f (reflₙ x) = reflₙ (f x)

-- only need transport
transportₙ : {m n : Level} {𝒰 : Set m} → (C : 𝒰 → Set n)
          → {A B : 𝒰} → (A ==ₙ B)
          → (C A → C B)
transportₙ C (reflₙ A) = idₙ 
