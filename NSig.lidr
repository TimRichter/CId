> import Data.Vect

> %default total
> %auto_implicits off
> %access public export

multisorted signatures

we have a type of (codes for) sorts

a symbol has an arity in any sort and a
destination sort:

symbols are indexed by a pair (Sort -> Nat, Sort)

> NSig : Type -> Type
> NSig S = (arity : S -> Nat) -> (tgt: S) -> Type

> arity : {S : Type} -> {nsig : NSig S} -> 
>         {arity : S -> Nat} -> {tgt : S} ->
>         nsig arity tgt -> S -> Nat
> arity {arity=ar} _ = ar

> tgt : {S : Type} -> {nsig : NSig S} -> 
>       {arity : S -> Nat} -> {tgt : S} ->
>       nsig arity tgt -> S
> tgt {tgt=t} _ = t

example: signature of Monoid acting on a set

> data MonoidUnit = Unit
> data MonoidOp   = Op
> data MonoidAct  = Act

> data SortsMonoidAction = M | X

> MonoidAction : NSig SortsMonoidAction
> MonoidAction arity M with (arity M, arity X)
>   | (Z,Z)      = MonoidUnit
>   | (S(S Z),Z) = MonoidOp
>   | _          = Void
> MonoidAction arity X with (arity M, arity X)
>   | ((S Z),(S Z)) = MonoidAct
>   | _             = Void


now what about adding equality?







