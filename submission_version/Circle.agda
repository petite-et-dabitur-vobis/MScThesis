{-# OPTIONS --without-K #-}

open import Types

module Circle where

-- without cubical, we must use postulates

data ๐ยน : Type where
  base : ๐ยน

postulate
  loop : base == base

-- simple recursors:
-- we have B with circle structure,
-- get point b and l in it
-- recursion principle says that a function exists s.t.
-- base is sent by it to b
๐ยน-induction-base-nondep : (B : Type)
                    โ (b : B) โ (l : b == b)
                    โ ๐ยน โ B
๐ยน-induction-base-nondep B b l base = b

-- loop is acted on by it into l
postulate
  ๐ยน-induction-loop-nondep : (B : Type)
                           โ (b : B) โ (l : b == b)
                           โ ap (๐ยน-induction-base-nondep B _ l) loop == l

-- dependent recursor/induction
-- HIT โ need only to treat two cases: "base" and "loop".
-- induction goes the same as usual:
-- 1. suppose a property P (or a fibration/context change)
-- 2. suppose we have elements corresponding to
--   a) P base
--   b) the "correct" equivalent of P loop
--      [this will be ... ]
-- 3. we want to produce a function from ๐ยน to
--    the new context, P x
-- by induction (higher induction, that is),
-- we only need to specify the output for "base" and "loop".
-- for "base", we return the element of P base that was given
๐ยน-induction-base : ( P : ๐ยน โ Type )
             โ ( b : P base ) โ ( l : transport P loop b == b )
             โ ( (x : ๐ยน) โ P x )
๐ยน-induction-base P b l base = b

-- note that l is not of type b = b;
-- as explained in the thesis, this is because
-- the path over loop does not need to have the same start and end points
-- precisely because of this, for the case where we have loop,
-- we're just working with a dependent path.
-- this means we need action on dependent paths,
-- that is, we need apd and not just ap
postulate 
  ๐ยน-induction-loop : ( P : ๐ยน โ Type )
                    โ ( b : P base ) โ ( l : transport P loop b == b )
                    โ apd P (๐ยน-induction-base P b l) loop == l

-- below was my (good) intuition (back before I studied it). this is just a fibration -
{- 
  all these seem like a standard mapping from a free generated group
  into another. this is probably an embedding: since we have,
  structurally speaking, that P has the ๐ยน structure embedded, which
  is shown by the fact that both (P base) and (P loop) are inhabited,
  then we can "embed" ๐ยน in P by sending ๐ยน's generators into some
  generators of P. now, these analogy is lacking something: I must still
  specify whether I'm talking about P or P x and, in any case, if it makes
  sense to talk about something analogous to a group.
-}  
