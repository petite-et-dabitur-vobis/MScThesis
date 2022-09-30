{-# OPTIONS --without-K #-}

open import Types

-- we have some things implemented for == in Types;
-- but sym and trans - even though proved in the thesis -,
-- are not implemented here.
-- this module starts off by implementing them and then
-- constructing syntax to make proofs more readable.
-- main resource used was https://plfa.github.io/Equality/

-- symmetry says that if x == y, then y == x
sym' : {A : Type} →
       Π x ꞉ A ∙ (Π y ꞉ A ∙ (
       x == y → y == x ))
sym' x y (refl x) = refl x

-- for convenience, I'll use some syntactic tricks
sym : {A : Type} → {x y : A} →
      x == y → y == x
sym (refl x) = refl x

symₙ : {A : Type} → {x y : A} →
      x ==ₙ y → y ==ₙ x
symₙ (reflₙ x) = reflₙ x

-- same thing for trans
trans' : {A : Type} →
         Π x ꞉ A ∙ ( Π y ꞉ A ∙ ( Π z ꞉ A ∙ (
         x == y → y == z → x == z )))
trans' x y z (refl x) (refl x) = refl x

trans : {A : Type} → {x y z : A} →
        x == y → y == z → x == z
trans (refl x) (refl x) = refl x

transₙ : {A : Type} → {x y z : A} →
        x ==ₙ y → y ==ₙ z → x ==ₙ z
transₙ (reflₙ x) (reflₙ x) = reflₙ x

