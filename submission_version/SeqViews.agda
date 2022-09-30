{-# OPTIONS --without-K #-}

open import Types
open import Univalence
open import EqReasoning
open import Agda.Primitive

-- assume A and B are type variables
private
  variable
    A B : Type

-- SEQ implementation: its a type constructor
-- which constructs off of Seq
-- with 5 fields to be instanciated
-- we have variable A; otherwise we could use {A : Type} →
-- before each function requiring a type
record SEQ : Set₁ where
  field
    Seq    : Type → Type
    empty  : Seq A
    single : A → Seq A
    append : Seq A → Seq A → Seq A
    map    : {B : Type} → (A → B) → (Seq A → Seq B)
    reduce : (A → A → A) → A → Seq A → A -- fold


-- list implementation for sequences
data List (A : Type) : Type where
  [] : List A
  cons : A → List A → List A

-- constructor for empty (because of type)

-- constructor for singleton
lsingle : {A : Type} → (x : A) → List A
lsingle x = cons x []

-- append two lists
-- _++_
lappend : {A : Type} → List A → List A → List A
lappend [] l = l
lappend (cons a l1) l2 = cons a (lappend l1 l2)

-- map function over list
lmap : {A B : Type} → (f : A → B) → List A → List B
lmap f [] = []
lmap f (cons a l) = cons (f a) (lmap f l)

-- foldl
lreduce : {A : Type} → (op : (A → A → A)) → ( b : A ) → List A → A
lreduce op b [] = b
lreduce op b (cons x xs) = lreduce op (op b x) xs

-- statement that List is now a possible implementation of SEQ
ListSeq : SEQ
ListSeq = record { Seq = List; 
                   empty = [];
                   single = lsingle ;
                   append = lappend ;
                   map = lmap ;
                   reduce = lreduce}

-- other list implementation:
-- reverse list (tail biased)
data RList (A : Type) : Type where
  rnull : RList A
  snoc : RList A → A → RList A
  
  -- constructor for singleton
rsingle : {A : Type} → (x : A) → RList A
rsingle x = snoc rnull x
  
  -- append two lists
rappend : {A : Type} → RList A → RList A → RList A
rappend rnull l = l
rappend (snoc l1 a) l2 = snoc (rappend l1 l2) a
  
-- map function over list
rmap : {A B : Type} → (f : A → B) → RList A → RList B
rmap f rnull = rnull
rmap f (snoc l a) = snoc (rmap f l) (f a)

-- foldl
rreduce : (op : (A → A → A)) → ( b : A ) → RList A → A
rreduce op b rnull = b
rreduce op b (snoc xs x) = rreduce op (op b x) xs

RListSeq : SEQ
RListSeq = record { Seq    = RList; 
                    empty  = rnull;
                    single = rsingle ;
                    append = rappend ;
                    map    = rmap ;
                    reduce = rreduce} 

-- alias for first projection, done in another way
-- (to handle meta variables), specific to equivalences
-- name is to match Licata's implementation
toList = pr₁

-- this is SEQ'
record SEQ'  : Set₁ where
  field
    -- use in/out syntax first
    Seq : Type → Type

    -- this is the type of equivalences
    e : {A : Type} → Seq A ≃ List A
    
    empty      : Seq A
    empty_spec : (toList (e {A})) empty == []

    single      : A → Seq A
    single_spec : Π x ꞉ A ∙ ( (toList (e {A})) (single x) == (cons x []) )

    append      : Seq A → Seq A → Seq A
    append_spec : Π s₁ ꞉ (Seq A) ∙ ( Π s₂ ꞉ (Seq A) ∙ ((toList (e {A})) (append s₁ s₂) == lappend (toList (e {A}) s₁) (toList (e {A}) s₂)) )

    map      : {B : Type} → (A → B) → (Seq A → Seq B)
    map_spec : Π f ꞉ (A → B) ∙ ( Π s ꞉ (Seq A) ∙ ((toList (e {B})) (map f s) == lmap f (toList (e {A}) s)) )

    reduce      : (A → A → A) → A → Seq A → A -- fold
    reduce_spec : Π op ꞉ (A → A → A) ∙ ( Π b ꞉ A ∙ ( Π s ꞉ Seq A ∙ ( reduce op b s == lreduce op b (toList (e {A}) s) )))

-- we can now construct a SEQ', using RList, which is a type with the view type embedded in it.
-- this give us the type along with a direct connection with the list implementation, through the view.
-- before that, we must have an isomorphism between RList and List. the function and its inverse is easy;
-- from is the in used by Walder
from : {A : Type} → List A → RList A
from [] = rnull
from (cons x xs) = snoc ( from xs ) x

-- the inverse
-- to is the out
to : {A : Type} → RList A → List A
to rnull = []
to (snoc xs x) = cons x (to xs)

-- proofs are left for later if there is time
postulate
  linv : {A : Type} → (to ∘ from) ∼ id {List A}
  rinv : {A : Type} → (from ∘ to) ∼ id {RList A}

-- the equivalence per se 
e : {A : Type} → RList A ≃ List A
e = (to , ((from , linv) , (from , rinv)) )

rempty_spec : (toList (e {A})) rnull == []
rempty_spec = refl []

postulate 
  rsingle_spec : Π x ꞉ A ∙ ( (toList (e {A})) (rsingle x) == (cons x []) )
  rappend_spec : Π s₁ ꞉ (RList A) ∙
                 ( Π s₂ ꞉ (RList A) ∙ ((toList (e {A})) (rappend s₁ s₂) == lappend (toList (e {A}) s₁) (toList (e {A}) s₂)) )
  rmap_spec : Π f ꞉ (A → B) ∙ ( Π s ꞉ (RList A) ∙ ((toList (e {B})) (rmap f s) == lmap f (toList (e {A}) s)) )
  rreduce_spec : Π op ꞉ (A → A → A) ∙ ( Π b ꞉ A ∙ ( Π s ꞉ RList A ∙ ( rreduce op b s == lreduce op b (toList (e {A}) s) )))

RListSeqView : SEQ'
RListSeqView = record { Seq         = RList;
                        e           = e;
                        empty       = rnull;
                        empty_spec  = rempty_spec;
                        append      = rappend;
                        append_spec = rappend_spec;
                        single      = rsingle;
                        single_spec = rsingle_spec;
                        map         = rmap;
                        map_spec    = rmap_spec;
                        reduce      = rreduce;
                        reduce_spec = rreduce_spec
                        }

-- with this view, we can prove properties about other implementations
-- this is an easy and known property for Lists.
append_prop : {A : Type} → (l : List A) → lappend [] l == l
append_prop l = refl l
-- with it and the view, we can prove a similar property for any isomorphic implementation;
-- here I'll prove for RList

------------- start proof
-- we'll need this lemma to get strict functional equality
iso_lemma1 : {A : Type} → (from ∘ to) == id {RList A}
iso_lemma1 = funext rinv

-- we'll also need this lemma to get from function equality to function ext
iso_lemma2 : {A : Type} → (r : RList A) → (from ∘ to) == id → (from ∘ to) r == id r 
iso_lemma2 r p = happly p r 

-- from the last two lemmas, we get this equality
iso_lemma3 : {A : Type} → (r : RList A) → (from ∘ to) r == id r
iso_lemma3 r = iso_lemma2 r iso_lemma1

-- we also know that id r = r, for any r, but specifically for r : RList A
iso_lemma4 : {A : Type} → (r : RList A) → id r == r
iso_lemma4 r = refl r

-- this means we can jump from r to (from ∘ to) r
-- direction is to facilitate reading
iso_prop_RList' : {A : Type} → (r : RList A) → r == (from ∘ to) r
iso_prop_RList' r = trans (iso_lemma4 r) ( sym (iso_lemma3 r) )

-- easier proof
lemma1 : {A : Type} → (r : RList A) → id r == r
lemma1 r = refl r

iso_prop_RList : {A : Type} → (r : RList A) → r == (from ∘ to) r
iso_prop_RList r = sym (trans (happly (funext rinv) r) (lemma1 r))

-- we know by definition that (from ∘ to) r == (from (to r))
-- by the property of append first proved, we can get (from ( lappend [] (to r) )
-- using ap on the already known equality
lemma5 : {A : Type} → (r : RList A) → (from ∘ to) r == from (lappend [] (to r))
lemma5 r = ap from (append_prop (to r))

-- by the rappend_spec, we can "switch" lappend and to:
spec_lemma1 : {A : Type} → (r : RList A) → lappend [] (to r) == to (rappend rnull r)
spec_lemma1 r = rappend_spec rnull r

-- and, by ap again, we can introduce "from"
lemma6 : {A : Type} → (r : RList A) → from (lappend [] (to r)) == (from ∘ to) (rappend rnull r)
lemma6 r = ap from (spec_lemma1 r)

-- this means we have that from (to r) == from (to (rappend rnull r))
lemma7 : {A : Type} → (r : RList A) → (from ∘ to) r == (from ∘ to) (rappend rnull r)
lemma7 r = trans (lemma5 r) (lemma6 r)

-- we're almost there; we can now take the from ∘ to off the rappend
-- using lemma2 again
lemma8 : {A : Type} → (r : RList A) → (from ∘ to) (rappend rnull r) == rappend rnull r
lemma8 r = sym (iso_prop_RList (rappend rnull r))

-- this means (from ∘ to) r == rappend rnull r
lemma9 : {A : Type} → (r : RList A) → (from ∘ to) r ==  (rappend rnull r)
lemma9 r = trans (lemma7 r) (lemma8 r)

-- finally, since r == (from ∘ to) r, we get
-- equality order is just to match append_prop
rappend_prop : {A : Type} → (r : RList A) → rappend rnull r == r
rappend_prop r = sym (trans (iso_prop_RList r) (lemma9 r))

------------- end proof
-- Now, one proof is enough, since once you've seen one of them, you've seen all of them.
-- In fact, this points us precisely in the direction of the HoTT solution:
-- this "generality" of the proofs should suggest some sort of possible principle from which they flow.

-- supposing we have a proof of functoriality for List...
-- prove if there's time
postulate
  list_fusion : {A B C : Type} → {f : A → B} → {g : B → C}
             → lmap (g ∘ f) == ((lmap g) ∘ (lmap f))

-- ...we can prove for RList.
-- we start with a lemma, applying rmap_spec to rmap (g ∘ f)
rmap_spec_lemma1 : {A B C : Type}
               → (f : A → B) → (g : B → C)
               → (to ∘ rmap (g ∘ f)) == (lmap (g ∘ f) ∘ to)
rmap_spec_lemma1 f g = funext (λ r → rmap_spec (g ∘ f) r)


-- using the fusion property for lists, which is now possible,
-- in this setting we get 
rmap_fusion_lemma1 : {A B C : Type}
                  → (f : A → B) → (g : B → C)
                  → (lmap (g ∘ f) ∘ to) == (((lmap g) ∘ (lmap f)) ∘ to)
rmap_fusion_lemma1 f g = ap (λ m → m ∘ to) list_fusion 

-- use rmap_spec again to shift "to" back
rmap_spec_lemma2 : {A B : Type}
               → (f : A → B) 
               → ((lmap f) ∘ to) == (to ∘ (rmap f))
rmap_spec_lemma2 f = funext (λ r → sym (rmap_spec f r))

-- we now add (lmap g) with ap
rmap_fusion_lemma2 : {A B C : Type}
                 → (f : A → B) → (g : B → C)
                 → (((lmap g) ∘ (lmap f)) ∘ to) == (((lmap g) ∘ to) ∘ (rmap f))
rmap_fusion_lemma2 f g = ap (λ m → lmap g ∘ m) (rmap_spec_lemma2 f)

-- we can do a trick to get the "second use" of rmap_spec
rmap_spec_lemma3 : {A B C : Type}
               → (f : A → B) → (g : B → C)
               → (((lmap g) ∘ to) ∘ rmap f) == ((to ∘ (rmap g)) ∘ rmap f)
rmap_spec_lemma3 f g = ap (λ m → m ∘ (rmap f)) (rmap_spec_lemma2 g)

-- we can now chain transitivities all the way back to the first lemma.
-- after that, we just apply from with ap.
-- from iso_prop_RList we can take away the (from ∘ to) from both sides.
-- here's the transivity chain
rmap_fusion_lemma3 : {A B C : Type}
               → (f : A → B) → (g : B → C)
               → (to ∘ rmap (g ∘ f)) == ((to ∘ (rmap g)) ∘ rmap f)
rmap_fusion_lemma3 f g = trans
                          (trans
                            (trans (rmap_spec_lemma1 f g) (rmap_fusion_lemma1 f g))
                            (rmap_fusion_lemma2 f g))
                          (rmap_spec_lemma3 f g)

-- now, wrap in from and cancel it with iso_prop_RList;
rmap_fusion_lemma4 : {A B C : Type}
               → (f : A → B) → (g : B → C)
               → ((from ∘ to) ∘ rmap (g ∘ f)) == (((from ∘ to) ∘ (rmap g)) ∘ rmap f)
rmap_fusion_lemma4 f g = ap (λ m → from ∘ m) (rmap_fusion_lemma3 f g)

-- finally, use iso_prop_RList to take (from ∘ to) out, from both sides
rlist_fusion : {A B C : Type}
               → (f : A → B) → (g : B → C)
               → rmap (g ∘ f) == (rmap g ∘ rmap f)
rlist_fusion f g = funext (λ r → -- ignore arguments
                           trans -- take from right
                             (trans (iso_prop_RList (rmap (g ∘ f) r)) ((happly (rmap_fusion_lemma4 f g)) r)) -- take from left
                             (sym (iso_prop_RList ((rmap g ∘ rmap f) r)))
                           )

-- solution with HoTT (equivalence can also be used for views):
-- start off by redefining SEQ to be an existential type, according to Plotkin
-- (consecutive existential types are defined as nested existential types)
-- this will facilitate equational reasoning further along
SEQ-Σ =  Σₙ Seq ꞉ (Type → Type) ∙ (
         Σₙ empty ꞉ ({A : Type} → Seq A) ∙ (
         Σₙ single ꞉ ({A : Type} → A → Seq A) ∙ (
         Σₙ append ꞉ ({A : Type} → Seq A → Seq A → Seq A) ∙ (
         Σₙ map ꞉ ({A B : Type} → (A → B) → (Seq A → Seq B)) ∙ (
         let reduce = {A : Type} → (A → A → A) → A → Seq A → A in reduce
         )))))
         -- small trick to have this field associated with reduce with current syntax

-- specifying an implementation is almost the same, except the syntax changes
ListSeq-Σ : SEQ-Σ
ListSeq-Σ = (List     ,,
            ( []      ,,
            ( lsingle ,,
            ( lappend ,,
            ( lmap    ,,
              lreduce
            )))))

RListSeq-Σ : SEQ-Σ
RListSeq-Σ = ( RList   ,,
             ( rnull   ,,
             ( rsingle ,,
             ( rappend ,,
             ( rmap    ,,
               rreduce
            )))))


-- we now want to equate ListSeq and RListSeq
-- but they are type constructors; so we instantiate them.
-- we now have elements Σ-types, and, from 2.3.2,
-- two elements of a Σ-type are equal iff their two components are equal.
-- their first component is the type constructor for List or RList;
-- we already know they are equal from the previous discussion.
-- however, the second component is dependent, and
-- SeqStr is diferent for List and RList, which means these two elements
-- are of different types; we can't compare them.
-- this situation is familiar: we need to transport from SeqStr List to SeqStr RList,
-- along the path we have - ua(e) - so that we can compare the elements.
-- from here, the type of equalities between Σ-types, sigma_eq, will be
postulate
  Σ_== : {A : Type} {B : A → Type} {s₁ s₂ : Σ x ꞉ A ∙ B x }
           (p : pr₁ s₁ == pr₁ s₂) (q : transport B p (pr₂ s₁) == pr₂ s₂)
        → s₁ == s₂
-- and this must be an axiom, since in Martin-Lof's type theory,
-- this is introduced as a rule.
-- however, we need the case where A is not just a type, but a type constructor
-- which is given by Σ₁; needless to say, the axiom works for all universes
postulate
  Σₙ_== : {m n : Level} {A : Set m} {B : A → Set n} {s₁ s₂ : Σₙ x ꞉ A ∙ B x }
          (p : Σₙpr₁ s₁ ==ₙ Σₙpr₁ s₂) (q : transportₙ B p (Σₙpr₂ s₁) ==ₙ Σₙpr₂ s₂)
        → s₁ ==ₙ s₂
  

-- start with simpler case: SEQ-Σ instantiated.
-- we can then use function extensionality to generalize
SEQ-Σ-P : (A : Type) → Set₁
SEQ-Σ-P A = Σₙ SeqA ꞉ Type ∙ (
            Σₙ empty ꞉ SeqA ∙ (
            Σₙ single ꞉ (A → SeqA ) ∙ (
            Σₙ append ꞉ (SeqA → SeqA → SeqA) ∙ (
            Σₙ map ꞉ ((A → A) → (SeqA → SeqA)) ∙ (
            let reduce =  ((A → A → A) → A → SeqA → A) in reduce
            )))))
            -- small trick to have this field associated with reduce with current syntax
-- (SEQ-Σ-P ℕ) 

-- here are the corresponding ListSeq-Σ and RListSeq-Σ
ListSeq-Σ-P : (A : Type) → SEQ-Σ-P A
ListSeq-Σ-P A = (List A        ,,
                ( []           ,,
                ( lsingle {A}  ,,
                ( lappend {A}  ,,
                ( lmap {A} {A} ,,
                  lreduce {A} 
                )))))
                
RListSeq-Σ-P : (A : Type) → SEQ-Σ-P A
RListSeq-Σ-P A = ( RList A    ,,
                 ( rnull        ,,
                 ( rsingle {A}  ,,
                 ( rappend {A}  ,,
                 ( rmap {A} {A} ,,
                 rreduce {A}
                 )))))

-- with a specific type, it's easy to state equality between RList and List:
-- we just need univalence
eq_RList_List : {A : Type} → RList A ==ₙ List A
eq_RList_List = ua e 

-- now, spec is of type spec : ListSeq ==ₜ RListSeq
-- we get this by using the Σ₁_== axiom
-- and showing proofs of the equality of both components.
-- we know the first components are equal;
-- we just need the equality for the second components.
-- this amounts to a recursive descent on the nested types,
-- exhibiting proofs of each component of the pair.
-- we could do this with the original SEQ structure,
-- but the nested-Σ structure is more helpful,
-- since it gives itself up to using Σₙ_==
spec : (A : Type) → RListSeq-Σ-P A ==ₙ ListSeq-Σ-P A
spec A = Σₙ_== (ua e) ( 
         Σₙ_== {!!} (   
         {!!}))

-- all of this comes from the fact that the UA guarantees we have
-- transport (SEQ-Σ-P A) (ua e) : SEQ-Σ-P (List A) → SEQ-Σ-P (RList A)

-- the first equality is obvious: List A == RList by the univalence axiom.
-- from the Σₙ_==, though, we now need to compare the second components,
-- shifted to the next context of SEQ-Σ-P through ua(e);
-- thus, we repeat the process: compare first components (under these restrictions)
-- this means we must compare the first components of
-- transportₙ (SEQ-Σ-P A) (ua e) (Σₙpr₂ (RListSeq-Σ-P A)) and
-- Σₙpr₂ (ListSeq-Σ-P A)
-- the RHS is just [];
-- the LHS is more hairy.
-- first, (Σₙpr₂ (RListSeq-Σ-P A)) is (rnull, ...), so we get
-- transportₙ (SEQ-Σ-P A) (ua e) (rnull, ...).
-- from theorem 2.7.4, since (SEQ-Σ-P A) is a Σ-type, we can distribute the transport as such
-- (transportₙ SEQ-Σ-P (ua e) rnull, ... ) and, since we only want the first component we get
-- transportₙ SEQ-Σ-P (ua e) rnull.
-- the (propositoinal) computation rule from chapter 2.10 HoTT book says that
-- transportₙ SEQ-Σ-P (ua e) rnull = (Σₙpr₁ e) rnull == to rnull
-- this means our equality is just (to rnull) == []
-- this is EXACTLY rempty_spec!

-- to fill hole 0, break into lemmas, as usual.
-- first, the equality for the rhs
hott_spec_lemma1 : (A : Type) → Σₙpr₁ (Σₙpr₂ (ListSeq-Σ-P A)) ==ₙ []
hott_spec_lemma1 A = reflₙ []

-- we know the second projection of (RListSeq-Σ-P A) is (rnull,...)
{-
hott_spec_lemma-1 : (A : Type) → (Σₙpr₂ (RListSeq-Σ-P A))
                   == ( rnull ,,  ( rsingle ,, ( rappend ,, ( rmap ,, rreduce))))
hott_spec_lemma-1 A = refl ( rnull ,,  ( rsingle ,, ( rappend ,, ( rmap ,, rreduce))))
-}

-- using theorem 2.7.4, we can distribute transportₙ over pairs
-- this is just the first component
-- state generally, prove if there's time
postulate
  hott_thm274 : (A : Set₁)
                 → (P : A → Set₁)
                 → (Q : (Σₙ x ꞉ A ∙ P x) → Set₁)
                 → {x y : A}
                 → (p : x ==ₙ y)
                 → ((u ,, z) : Σₙ u ꞉ (P x) ∙ (Q (x ,, u)))
                 → Σₙpr₁ (transportₙ (λ a → Σₙ u ꞉ (P a) ∙ Q (a ,, u)) p (u ,, z))
                    ==ₙ
                    transportₙ P p u
                 {-
                 → transportₙ (λ a → Σₙ u ꞉ (P a) ∙ (Q (a ,, u))) p (u ,, z)
                     ==ₙ
                   (transportₙ P p u ,,
                    transportₙ (λ a → Q (a ,, u) )
                               Σₙ_== p (refl (transport P p u))
                               z)
                  -}

-- alias for the context of transport
SEQ-Σ-P₂ : (A : Type) → (SeqA : Type) → Type
SEQ-Σ-P₂ A SeqA =
             Σₙ empty ꞉ SeqA ∙ (
             Σₙ single ꞉ (A → SeqA ) ∙ (
             Σₙ append ꞉ (SeqA → SeqA → SeqA) ∙ (
             Σₙ map ꞉ ((A → A) → (SeqA → SeqA)) ∙ (
             let reduce =  ((A → A → A) → A → SeqA → A) in reduce
             ))))
-- SEQ-Σ-P₂ ℕ

-- specific version
postulate
  hott_spec_lemma2 : (A : Type)
                  → Σₙpr₁ (transportₙ (SEQ-Σ-P₂ A) (ua (e {A})) (Σₙpr₂ (RListSeq-Σ-P A)))
                     ==ₙ transportₙ (λ X → X) (ua (e {A})) rnull
--hott_spec_lemma2 A = hott_thm274 A (λ X → X) (ua (e {A})) (Σₙpr₂ (RListSeq-Σ-P A))
                     

-- using the propositional computational rule of UA, we can transform the first component
hott_spec_lemma3 : (A : Type) → transportₙ (λ X → X) (ua (e {A})) rnull ==ₙ (pr₁ (e {A})) rnull
hott_spec_lemma3 A = ua_elim rnull (e {A})

-- this is trivial
hott_spec_lemma4 : (A : Type) → (pr₁ (e {A})) rnull ==ₙ to rnull
hott_spec_lemma4 A = reflₙ (to rnull)

-- starting the transitivity chains: 
-- the lhs yields (to rnull)
hott_spec_lemma5 : (A : Type)
                → Σₙpr₁ (transportₙ (SEQ-Σ-P₂ A)
                                     (ua (e {A}))
                                     (Σₙpr₂ (RListSeq-Σ-P A)))
                          ==ₙ to rnull
hott_spec_lemma5 A = (transₙ (hott_spec_lemma2 A)
                             (transₙ (hott_spec_lemma3 A)
                                     (hott_spec_lemma4 A)))

-- and the rhs yields [], by lemma1.
-- Finally, this means if we have the mentioned type,
-- we can get to our spec type
hott_spec : (A : Type)
         → (rnull_spec : Σₙpr₁ (transportₙ (SEQ-Σ-P₂ A)
                                            (ua (e {A}))
                                            (Σₙpr₂ (RListSeq-Σ-P A)))
                                  ==ₙ Σₙpr₁ (Σₙpr₂ (ListSeq-Σ-P A)))
         → to rnull ==ₙ []
hott_spec A rnull_spec = transₙ (transₙ (symₙ (hott_spec_lemma5 A))
                                        rnull_spec)
                                (hott_spec_lemma1 A)

-- which concludes the proof
