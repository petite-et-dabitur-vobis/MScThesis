open import Types

postulate
  ℝ : Set
  Char : Set

data Circle1 : Set where
  xcoord : ℝ → Circle1
  ycoord : ℝ → Circle1
  radius : ℝ → Circle1

data Circle2 : Set where
  center : Char → Circle2
  radius : ℝ    → Circle2
