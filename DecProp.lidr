> module DecProp
> import Data.So
> import Syntax.PreorderReasoning

> %default total 

> %auto_implicits off

> %access public export

decidable props, praedicates a.s.o. with type interfaces
========================================================

Remark: depends on a "really_believe_me" to proof
        that any two functions f,g : a -> Void  are equal.
        How far away is that from full function 
        extensionality ?

propositions
------------

> using (a : Type)
>   interface Prop a where
>     isProp : (x, y : a) -> x = y

> implementation Prop Void where
>   isProp x _ = absurd x

> implementation Prop Unit where
>   isProp () () = Refl

> using (a : Type)
>   implementation Uninhabited a => Prop a where
>     isProp x _ = absurd x

UIP

> using (a : Type, x : a, y : a)
>   implementation Prop ((=) {A=a} {B=a} x y) where
>     isProp Refl Refl = Refl

decidable propositions
----------------------

> using (a : Type)
>   interface Prop a => DecProp a where
>     decide : Dec a

logic of decidable propositions
-------------------------------

> implementation DecProp Void where
>   decide = No id

> implementation DecProp Unit where
>   decide = Yes ()

Negation of a decidable proposition
is a proposition (or, should be ... believe me...) 

> using (a : Type)
>   implementation DecProp a => Prop (Not a) where
>     isProp {a} f g = case decide {a} of
>       Yes x => absurd (f x)
>       No h  => really_believe_me h

and it is decidable

> using (b : Type)
>   implementation DecProp b => DecProp (Not b) where
>     decide = decNot decide where
>       decNot : {a : Type} -> Dec a -> Dec (Not a)
>       decNot  (Yes x    ) = No (\notx => notx x)
>       decNot  (No  notx ) = Yes notx

Conjunction

> AND : (a, b : Type) -> Type
> AND a b = (a,b)

> syntax [a] "/\\" [b] = AND a b 

> using (a : Type, b : Type)
>   implementation (Prop a, Prop b) => Prop (a /\ b) where
>     isProp (x,y) (x',y') = 
>       (x ,y )   ={ cong {f = \x => (x,y)}  (isProp x x') }=
>       (x',y )   ={ cong {f = \y => (x',y)} (isProp y y') }=
>       (x',y')   QED
>
> 
>   implementation (DecProp a, DecProp b) => DecProp (a /\ b) where
>     decide = case decide {a = a} of
>       Yes prfa  => case decide {a = b} of
>         Yes prfb  => Yes (prfa,prfb)
>         No  notb  => No (\(pa,pb) => notb pb)
>       No  nota  => No (\(pa,pb) => nota pa)

Disjunction

> data OR : (a, b : Type) -> Type where
>   Both    : {a, b : Type} -> a -> b -> OR a b
>   LeftO   : {a, b : Type} -> a -> (Not b) -> OR a b
>   RightO  : {a, b : Type} -> (Not a) -> b -> OR a b

> syntax [a] "\\/" [b] = OR a b 

> using (a : Type, b : Type)
>   implementation (DecProp a, DecProp b) => Prop (a \/ b) where
>     isProp p1 p2 with (decide {a = a}, decide {a = b})
>       isProp (Both x y) (Both x' y') | (Yes _, Yes _) =
>         (Both x  y)   
>         ={ cong {f = \x => (Both x y )} (isProp {a = a} x x') }=
>         (Both x' y)   
>         ={ cong {f = \y => (Both x' y)} (isProp {a = b} y y') }=
>         (Both x' y')  QED
>       isProp (LeftO x ny) (LeftO x' ny') | (Yes _, No _) =
>         (LeftO x  ny) 
>         ={ cong {f = \x  => (LeftO x  ny )} (isProp {a = a} x x') }=
>         (LeftO x' ny) 
>         ={ cong {f = \ny => (LeftO x' ny )} (isProp {a = (Not b)} ny ny')}=
>         (LeftO x' ny')  QED
>       isProp (RightO nx y) (RightO nx' y') | (No _, Yes _) =
>         (RightO nx  y) 
>         ={ cong {f = \nx => (RightO nx  y)} (isProp {a = (Not a)} nx nx')}=
>         (RightO nx' y) 
>         ={ cong {f = \y  => (RightO nx' y)} (isProp {a = b} y y')}=
>         (RightO nx' y')  QED
>       isProp (Both   x  _)  _ | (No nx, _    ) = absurd (nx x)
>       isProp (LeftO  x  _)  _ | (No nx, _    ) = absurd (nx x)
>       isProp (RightO nx _)  _ | (Yes x, _    ) = absurd (nx x)
>       isProp _ (Both   x  _)  | (No nx, _    ) = absurd (nx x)
>       isProp _ (LeftO  x  _)  | (No nx, _    ) = absurd (nx x)
>       isProp _ (RightO nx _)  | (Yes x, _    ) = absurd (nx x)
>       isProp (Both   _  y)  _ | (_    , No ny) = absurd (ny y)
>       isProp (RightO _  y)  _ | (_    , No ny) = absurd (ny y)
>       isProp (LeftO  _ ny)  _ | (_    , Yes y) = absurd (ny y)
>       isProp _ (Both   _  y)  | (_    , No ny) = absurd (ny y)
>       isProp _ (RightO _  y)  | (_    , No ny) = absurd (ny y)
>       isProp _ (LeftO  _ ny)  | (_    , Yes y) = absurd (ny y)
>    
>   implementation (DecProp a, DecProp b) => DecProp (a \/ b) where
>     decide with (decide {a = a}, decide {a = b})
>       | (Yes x, Yes y) = Yes (Both x y)
>       | (Yes x, No ny) = Yes (LeftO x ny)
>       | (No nx, Yes y) = Yes (RightO nx y)
>       | (No nx, No ny) = No notxory  where
>           notxory : (a \/ b) -> Void
>           notxory (Both   x _) = absurd (nx x)
>           notxory (LeftO  x _) = absurd (nx x)
>           notxory (RightO _ y) = absurd (ny y)

> Implies : (a: Type) -> (b: Type) -> Type
> Implies a b = (Not a) \/ b

> syntax [a] "==>" [b] = Implies a b

> Equiv : (a: Type) -> (b: Type) -> Type
> Equiv a b = (a ==> b) /\ (b ==> a)

> syntax [a] "<==>" [b] = Equiv a b

> using (a : Type) 
>   val : (DecProp a) => Bool
>   val {a} with (decide {a = a})
>     | Yes _ = True
>     | No  _ = False

Praedicates

a prepredicate is just a type family on a

> data PrePred : Type -> Type where 
>   MkPrePred : {a: Type} -> (a -> Type) -> PrePred a

> using (a : Type)
>   unwrap : PrePred a -> (a -> Type)
>   unwrap (MkPrePred P) = P
>
>   interface Pred a (P : PrePred a) where 
>     isPred : (z : a) -> (x, y : (unwrap P) z) -> x = y
>
>   interface Pred a P => DecPred a (P : PrePred a) where
>     decideAt : (z : a) -> Dec ((unwrap P) z)

> Empty : {a : Type} -> PrePred a
> Empty {a} = MkPrePred (\x => Void)

> using (a : Type)
>   implementation Pred a (Empty {a}) where
>     isPred z = isProp
>
>   implementation DecPred a (Empty {a}) where
>     decideAt z = decide

> Full : {a : Type} -> PrePred a
> Full {a} = MkPrePred (\x => ())

> using (a : Type)
>   implementation Pred a (Full {a}) where
>     isPred z = isProp
>
>   implementation DecPred a (Full {a}) where
>     decideAt z = decide

decidable relations a -> b are decidable predicates on a x b

>   interface Pred (a,b) P => DecRel a b (P : PrePred (a,b))  where { }

>   interface Pred (a,a) P => DecBinRel a (P : PrePred (a,a)) where { }


> Singleton : {a : Type} -> (x : a) -> PrePred a
> Singleton x = MkPrePred (\y => (x = y))

> data BoolPred : Type -> Type where
>   MkBoolPred : {a : Type} -> (a -> Bool) -> BoolPred a

> using (a : Type, x : a)
> implementation Pred a (Singleton {a} x) where
>   isPred z = isProp

doesn't work yet:
< implementation Eq a => DecPred a (Singleton x) where
<   decideAt z = if (x == z) then Yes Refl else ?lala

any boolean predicate on a generates a decidable predicate on a:

> predFromBPred : {a : Type} -> (a -> Bool) -> PrePred a
> predFromBPred bp = MkPrePred (\x => bp x = True)

< implementation Pred a (predFromBPred 

