{-# OPTIONS --without-K #-}

open import Types

module Interval where

data I : Type where
  0ᵢ : I
  1ᵢ : I

-- without cubical, we must use postulates
postulate
  seg : 0 == 1
