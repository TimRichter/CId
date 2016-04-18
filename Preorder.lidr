> module Preorder
> import Prop
> import Syntax.PreorderReasoning

> %default total

Preorders, partial orders, linear orders
========================================

Relations
---------

A binary relation between types X and Y is a "subset" of the cartesian 
product XxY. How to model this? 

First attempt: 
--------------

as a boolean predicate in "curried" form:

> RelB : Type -> Type -> Type
> RelB A B = A -> B -> Bool

binary relations on A then become

> BinRelB : Type -> Type
> BinRelB A = RelB A A

Examples

the empty relation between any two types

> emptyRelB : {A, B : Type} -> RelB A B
> emptyRelB x y = False

and the "all" relation:

> allRelB : {A, B : Type} -> RelB A B
> allRelB x y = True

"normal" greater or equal on Nat:

> geq : BinRelB Nat
> geq Z      Z    = True
> geq Z     (S n) = True
> geq (S m)  Z    = False
> geq (S m) (S n) = geq m n

prefix order on lists 
(we need the element type to have a decidable equality)

> lPre : DecEq a => BinRelB (List a)
> lPre []      _       = True
> lPre (x::xs) []      = False
> lPre (x::xs) (y::ys) 
>   with (decEq x y)
>   | Yes _ = lPre xs ys
>   | No  _ = False

But properties of relations are difficult to implement, e.g.:

< isReflexiveB : {A : Type} -> BinRelB A -> Bool

if A is infinite, such a "check" for reflexivity will never finish,
so we cannot implement this as a total function! So


Second attempt
--------------

as a type valued function! 

> Rel : Type -> Type -> Type
> Rel A B = A -> B -> Type

A relation r in (Rel A B) is a "family" of types, one
for each pair of elements a in A and b in B. Elements of
this type  r a b  are the proves (evidences, witnesses, ...) that
a and b are in relation r. 

the empty relation between any two types

> emptyRel : {A, B : Type} -> Rel A B
> emptyRel x y = Void

the "all" relation:

> allRel : {A, B : Type} -> Rel A B
> allRel x y = ()

> BinRel : Type -> Type
> BinRel A = Rel A A

> data IsRefl : {A : Type} -> BinRel A -> Type where
>   PrfRefl : -- if for a relation r on A
>             {A : Type} -> {r : BinRel A} ->
>             -- we provide for each x in A an element of (r x x)
>             ( (x : A) -> r x x ) ->
>             -- then we have proved reflexivity of r
>             (IsRefl r)

> data IsTrans : {A : Type} -> BinRel A -> Type where
>   PrfTrans :  -- if for a relation r on A
>               {A : Type} -> {r : BinRel A} ->        
>               -- for any x,y,z in A, given proofs (r x y) and (r y z)
>               -- we can produce a proof of (r x z)
>               ({x, y, z : A} -> r x y -> r y z -> r x z ) ->   
>               -- then we have proved transitivity of r
>               (IsTrans r)                          


Preorder
--------

To model a preordered set ("quasigeordnete Menge" in the
lecture):

> data Preorder : Type where
>   MkPreorder :  {- the set is modeled as a type -}
>                 (O : Type) ->
>                 {- the fact "a R b" is also modeled by a type -}
>                 (R : O -> O -> Type) ->
>                 {- R is reflexive -}
>                 (Ref : (a : O) -> R a a) ->
>                 {- R is transitive -}
>                 (Trans : {a, b, c : O} ->
>                          R a b -> R b c -> R a c) ->
>                 {- the types "a R b" have at most one inhabitant,
>                    i.e. they are "Propositions" -}
>                 (IsPropR : {a, b : O} -> IsProp (R a b)) ->
>                 Preorder

> PObj : Preorder -> Type
> PObj (MkPreorder o _ _ _ _) = o

> PHom : (pp : Preorder) -> (PObj pp) -> (PObj pp) -> Type
> PHom (MkPreorder _ rel _ _ _) = rel

> PRefl : {pp : Preorder} -> (a : PObj pp) -> PHom pp a a
> PRefl {pp=(MkPreorder _ _ ref _ _)} = ref

> PTrans :  {pp : Preorder} -> {a, b, c : PObj pp} ->
>           (PHom pp a b) -> (PHom pp b c) -> (PHom pp a c)
> PTrans {pp=(MkPreorder _ _ _ trans _)} = trans

> PProp : {pp : Preorder} -> {a, b : PObj pp} -> 
>         IsProp ( PHom pp a b )
> PProp {pp=(MkPreorder _ _ _ _ isProp)} = isProp



> namespace Preorder
>   using (pp : Preorder, a : PObj pp, b: PObj pp, c : PObj pp) 
>     qed : (a : PObj pp) -> PHom pp a a
>     qed = PRefl
>     step : (a : PObj pp) -> PHom pp a b -> PHom pp b c -> PHom pp a c
>     step a p q = PTrans p q

> isTrans' : (pp : Preorder) -> (a, b, c : PObj pp) ->
>           (PHom pp a b) -> (PHom pp b c) -> (PHom pp a c)
> isTrans' pp a b c p q =
>   a  ={ p }=
>   b  ={ q }=
>   c QED

Meets

> data IsMeet : {pp : Preorder} -> (a, b, c : PObj pp) -> Type where
>   PrfIsMeet : {pp : Preorder} -> (a, b, c : PObj pp) ->
>   -- c is lower bound of {a,b}
>       (PHom pp c a) ->  (PHom pp c b) ->   
>   -- and for any other lower bound d, d is lower than c
>       ((d : PObj pp) -> PHom pp d a -> PHom pp d b -> PHom pp d c) ->
>       IsMeet a b c


