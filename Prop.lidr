> module Prop

> %default total
> %auto_implicits off
> %access public export

A type is called a proposition iff any two inhabitants of
the type are equal:

> IsProp : Type -> Type
> IsProp t = (p, q : t) -> p = q

Heterogeneous variant (useful?)

> IsPropH : Type -> Type -> Type
> IsPropH t1 t2 = (p : t1) -> (q : t2) -> p = q

Void is a proposition

> VoidIsProp : IsProp Void
> VoidIsProp p q = absurd p

Unit is a proposition

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

heterogeneous equality implies type equality

> eqToTypeEq : {A, B : Type} -> {a : A} -> {b : B} -> (a = b) -> A = B
> eqToTypeEq Refl = Refl

> UipWTH2 : {A1, A2, B1, B2 : Type} -> 
>           {a1 : A1} -> {a2 : A2} -> {b1 : B1} -> {b2 : B2} -> 
>           (teq1 : A1 = B1) -> (teq2 : A2 = B2) ->
>           (a1 = a2) -> (b1 = b2) -> IsPropH (a1 = b1) (a2 = b2)
> UipWTH2 Refl Refl Refl Refl Refl Refl = Refl




For subsets we also need families of Props, aka
Praedicates

> data Praed : (A : Type) -> Type where
>   MkPraed : {A : Type} -> (P : A -> Type) ->
>             ((a : A) -> IsProp (P a)) ->
>             Praed A

The Sigma type of a Praedicate over A is a Subset

> SubSet : {A : Type} -> Praed A -> Type
> SubSet {A} (MkPraed P _) = ( a : A ** P a)

> EmptyPraed : {A : Type} -> Praed A
> EmptyPraed = MkPraed (\a => Void) (\a => VoidIsProp) 

> EmptySubSet : {A : Type} -> Type
> EmptySubSet {A} = SubSet (EmptyPraed {A})


