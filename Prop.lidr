> module Prop

> %default total

A type is called a proposition iff any two inhabitants of
the type are equal:

> IsProp : Type -> Type
> IsProp t = (p, q : t) -> p = q

Heterogeneous variant (useful?)

> IsPropH : Type -> Type -> Type
> IsPropH t1 t2 = (p: t1) -> (q : t2) -> p = q

Void is obviously a proposition

> VoidIsProp : IsProp Void
> VoidIsProp p q = absurd p

and Unit as well

> UnitIsProp : IsProp ()
> UnitIsProp () () = Refl

Any equality type in Idris is a proposition 
(Uip = "uniqueness of identity proofs")

> Uip : {A : Type} -> {a1, a2 : A} -> IsProp (a1 = a2)
> Uip Refl Refl = Refl

> UipWT : {A, B : Type} -> { teq: A = B } -> {a1 : A} -> {a2 : B} -> IsProp (a1 = a2)
> UipWT {teq = Refl} Refl Refl = Refl

> UipWTH : {A, B : Type} -> { teq: A = B } -> {a1, a2 : A} -> {b1, b2 : B} ->
>          (asEq : a1 = a2) -> (bsEq: b1 = b2) -> IsPropH (a1 = b1) (a2 = b2)
> UipWTH {teq = Refl} Refl Refl Refl Refl = Refl

For subsets we also need families of Props, aka
Praedicates

> data Praed : (A : Type) -> Type where
>   MkPraed : {A : Type} -> (P : A -> Type) ->
>             ((a : A) -> IsProp (P a)) ->
>             Praed A

The Sigma type of a Praedicate over A is a Subset

> SubSet : {A : Type} -> Praed A -> Type
> SubSet {A} (MkPraed P _) = Sigma A P

> EmptyPraed : {A : Type} -> Praed A
> EmptyPraed = MkPraed (\a => Void) (\a => VoidIsProp) 

> EmptySubSet : {A : Type} -> Type
> EmptySubSet {A} = SubSet (EmptyPraed {A})




