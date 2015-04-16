> module Prop

> %default total

A type is called a property iff any two inhabitants of
the type are equal:

> IsProp : Type -> Type
> IsProp t = (p : t) -> (q : t) -> p = q

Void is obviously a proposition

> VoidIsProp : IsProp Void
> VoidIsProp p q = absurd p

Any equality type in Idris is a proposition 
(uip = "uniqueness of identity proofs")

> Uip : {A : Type} -> {a1 : A} -> {a2 : A} -> IsProp (a1 = a2)
> Uip Refl Refl = Refl
