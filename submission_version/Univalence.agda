{-# OPTIONS --without-K #-}

open import Types

-- broadly speaking, this implements chapter 3.2

private
  variable
    A B : Type

-- homotopy on functions:
-- property that states to function are equal.
-- also a type constructor:
-- takes two functions, says they're equal iff
-- for the same input they give the same output
Hom :  {A B : Type} → (f : A → B) → (g : A → B) → Type
Hom {A} {B} f g = Π x ꞉ A ∙ ((f x) == (g x))

-- one possible, more convenient definition ignoring types,
-- notation similar to book/thesis
-- we won't be needing the dependent version
_~₁_ : (f : A → B) → (g : A → B) → Type
f ~₁ g = Hom {domain f} {codomain f} f g

-- simplest definition is this
_∼_ : (f : A → B) → (g : A → B) → Type
f ∼ g = Π x ꞉ (domain f) ∙ ((f x) == (g x))

-- property for equivalences
-- also a type constructor:
-- takes function and returns pair of dep pair types
-- stating existence of left and right sided inverses
-- inverse here means composition is id
isequiv : (f : A → B) → Type
isequiv f = (Σ g ꞉ (codomain f → domain f) ∙ ((f ∘ g) ∼ id)) × (Σ h ꞉ (codomain f → domain f) ∙ ((h ∘ f) ∼ id))

-- we can now define the type constructor
-- for equivalence of types.
-- this is just a function between the two types,
-- with a proof that it is an equivalence
_≃_ : Type → Type → Type
A ≃ B = Σ f ꞉ (A → B) ∙ isequiv f

-- we now need equality between types
-- either implement it anew and specifically for this
-- (not that good an idea, since we need transport and ap)
-- or alter the thing with universes and get lots of it
-- for free

-- we can go from identity to equivalence;
-- the function given in proof of Theorem 3.2.7 suffices
--idtoequiv : (A ==ₙ B) → (A ≃ B) 
-- finish later

-- the Univalence Axiom (this is not the most general form)
-- if we have equivalence between types, we also have equality
-- and its (propositional) computational rule
postulate
  ua : (A ≃ B) → (A ==ₙ B)
  ua_elim : (x : A) → (e : A ≃ B) → (transportₙ (λ X → X) (ua e) x) ==ₙ ((pr₁ e) x)


-- we could derive function extensionality from ua (see thm 4.9 of the HoTT book),
-- but I'll assume it here as an axiom
postulate
  funext : {f g : A → B} → (f ∼ g) → (f == g)

-- we'll also need the reverse: to get extensionality from equality
-- the HoTT books calls the happly
happly : { f g : A → B} → (f == g) → (Π x ꞉ A ∙ ( f x == g x) )
happly (refl f) = (λ x → refl (f x))
